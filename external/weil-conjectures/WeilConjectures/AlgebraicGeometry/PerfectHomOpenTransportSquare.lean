/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
import all WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # The cartesian open square commutes with pullback Hom transport

Source: Stacks Project, Cohomology, Tag 0D5S; perfect.tex, Tag 09RE.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

set_option backward.isDefEq.respectTransparency true

section TransportCalculations

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

attribute [local irreducible] perfectHomComposition

private theorem tr_comp_source {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Y) (i : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj ((derivedPullback i).obj P) ⟶
      (derivedPullback p).obj ((derivedPullback i).obj Q)) :
    tr h (p ≫ i)
      ((perfectHomComposition p i).inv.app P ≫ a ≫
        (perfectHomComposition p i).hom.app Q) =
    (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
      (Category.assoc h p i))).inv.app P ≫
      (perfectHomComposition (h ≫ p) i).inv.app P ≫ tr h p a ≫
      (perfectHomComposition (h ≫ p) i).hom.app Q ≫
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h p i))).hom.app Q := by
  have hi := congrArg (fun e ↦ e.inv.app P) (cc_assoc h p i)
  have hh := congrArg (fun e ↦ e.hom.app Q) (cc_assoc h p i)
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Category.assoc] at hi hh
  simp only [tr, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((perfectHomComposition h (p ≫ i)).inv.app P)
    ((derivedPullback h).map ((perfectHomComposition p i).inv.app P)), hi]
  simp only [Category.assoc]
  rw [hh]

-- Equality transport through the selected composition comparisons needs this budget.
private theorem trTo_comp_source {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Y) (q : W ⟶ Y) (i : Y ⟶ Z) (e : h ≫ p = q)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj ((derivedPullback i).obj P) ⟶
      (derivedPullback p).obj ((derivedPullback i).obj Q)) :
    trTo h (p ≫ i) (q ≫ i) (by rw [← Category.assoc, e])
      ((perfectHomComposition p i).inv.app P ≫ a ≫
        (perfectHomComposition p i).hom.app Q) =
      (perfectHomComposition q i).inv.app P ≫ trTo h p q e a ≫
        (perfectHomComposition q i).hom.app Q := by
  subst q
  rw [trTo_refl]
  unfold trTo
  rw [tr_comp_source]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id]


private theorem homMap_natural {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P P' Q Q' : schemeDerivedCategory X}
    (m : P' ⟶ P) (n : Q ⟶ Q')
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s g
      ((derivedPullback (pullback.fst s T.hom)).map m ≫ f ≫
        (derivedPullback (pullback.fst s T.hom)).map n) =
      (derivedPullback (pullback.fst s T'.hom)).map m ≫ perfectHomMap s g f ≫
        (derivedPullback (pullback.fst s T'.hom)).map n := by
  have hm := (perfectHomComparison s g).hom.naturality m
  have hn := (perfectHomComparison s g).inv.naturality n
  dsimp only [Functor.comp_map] at hm hn
  simp only [perfectHomMap, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((perfectHomComparison s g).hom.app P'), ← hm]
  simp only [Category.assoc]
  rw [hn]

end TransportCalculations

set_option backward.isDefEq.respectTransparency false

/-- Open restriction commutes with transport along any morphism over the base.
Source: Stacks Project, Cohomology, Tag 0D5S; perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-open-transport-square).

Proof: Substitute the supplied equations for κ. The two composites of cartesian
arrows from B x_S T' to Y x_S T agree:
check their first and second projections using pullback.hom_ext. Paste the
counit-pinned composition comparisons for these arrows and their projections.
The associativity equation of exists_derivedPullbackComposition equates the two
pasted comparisons; naturality of sigma, the mate of the identity on the open
right adjoint, equates their final whiskered factors. Apply both comparisons at
M and Q. Pullback of f is natural with respect to their components. Expanding
the two conjugated Hom maps, cancel adjacent inverse and forward components.
The remaining composites are the two sides below. This is an identity of the
canonical maps and does not assert bijectivity of pullback. It remains valid
for empty opens, identity arrows and zero objects. -/
theorem perfect_hom_open_transport_square
    {S Y : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {T T' : Over S} (g : T' ⟶ T) (M Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s T.hom)).obj M ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    let b (r : Over S) :=
      pullback.map (B.ι ≫ s) r.hom s r.hom B.ι (𝟙 r.left) (𝟙 S) (by simp) (by simp)
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he (r : Over S) :
        b r ≫ pullback.fst s r.hom = pullback.fst (B.ι ≫ s) r.hom ≫ B.ι := by
      simp [b, pullback.map]
    let κ₀ (r : Over S) := perfectHomComposition (b r) (pullback.fst s r.hom) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) (he r)) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r.hom) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r.hom))
    ∀ κ : (r : Over S) →
        derivedPullback (pullback.fst s r.hom) ⋙ derivedPullback (b r) ≅
          schemeMVDerivedRestriction Y B ⋙ derivedPullback (pullback.fst (B.ι ≫ s) r.hom),
      (∀ r, κ r = κ₀ r) →
    (κ T').inv.app M ≫ (derivedPullback (b T')).map (perfectHomMap s g f) ≫
        (κ T').hom.app Q =
      perfectHomMap (B.ι ≫ s) g
        ((κ T).inv.app M ≫ (derivedPullback (b T)).map f ≫ (κ T).hom.app Q) := by
  set_option backward.isDefEq.respectTransparency true in
    intro b σ he κ₀ κ hκ
    simp only [hκ]
    let p (r : Over S) := pullback.fst s r.hom
    let q (r : Over S) := pullback.fst (B.ι ≫ s) r.hom
    let h := baseChangeMap s g
    let k := baseChangeMap (B.ι ≫ s) g
    have eh : h ≫ p T = p T' := baseChangeMap_fst s g
    have ek : k ≫ q T = q T' := baseChangeMap_fst (B.ι ≫ s) g
    have esq : b T' ≫ h = k ≫ b T := by
      apply pullback.hom_ext
      · simp only [Category.assoc, h, baseChangeMap_fst]
        rw [he T', he T, ← Category.assoc, baseChangeMap_fst]
      · simp only [Category.assoc, h, baseChangeMap_snd]
        dsimp only [b]
        simp only [pullback.map, pullback.lift_snd, Category.comp_id, ← Category.assoc]
        rw [baseChangeMap_snd]
    let d (r : Over S) (a : (derivedPullback (p r)).obj M ⟶ (derivedPullback (p r)).obj Q) :=
      (perfectHomComposition (q r) B.ι).hom.app M ≫ trTo (b r) (p r) (q r ≫ B.ι) (he r) a ≫
        (perfectHomComposition (q r) B.ι).inv.app Q
    have ht : trTo (b T') (p T') (q T' ≫ B.ι) (he T') (trTo h (p T) (p T') eh f) =
        trTo k (q T ≫ B.ι) (q T' ≫ B.ι) (by rw [← Category.assoc, ek])
          (trTo (b T) (p T) (q T ≫ B.ι) (he T) f) := by
      rw [trTo_assoc, trTo_assoc]
      exact trTo_congr _ _ _ _ _ _ esq f
    have hd : d T' (perfectHomMap s g f) =
        perfectHomMap (B.ι ≫ s) g (d T f) := by
      have hcomp := trTo_comp_source k (q T) (q T') B.ι ek (d T f)
      dsimp only [d] at hcomp ⊢
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
        Iso.inv_hom_id_app, Category.comp_id] at hcomp
      simp only [homMap_trTo]
      change _ = trTo k (q T) (q T') ek _
      rw [ht]
      rw [hcomp]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
    have norm (r : Over S) (a : (derivedPullback (p r)).obj M ⟶ (derivedPullback (p r)).obj Q) :
        (κ₀ r).inv.app M ≫ (derivedPullback (b r)).map a ≫ (κ₀ r).hom.app Q =
          (derivedPullback (q r)).map (σ.hom.app M) ≫ d r a ≫
            (derivedPullback (q r)).map (σ.inv.app Q) := by
      simp only [κ₀, d, trTo, tr, Iso.trans_inv, Iso.trans_hom,
        Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
      rfl
    rw [norm, norm, homMap_natural, hd]

end
end AlgebraicGeometry
