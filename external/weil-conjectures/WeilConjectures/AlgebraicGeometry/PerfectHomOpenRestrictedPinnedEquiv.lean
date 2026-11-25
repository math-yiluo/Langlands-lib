/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionMap
public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenTestBijective
import WeilConjectures.AlgebraicGeometry.DerivedOpenTestObject
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization

/-! # Pinned restriction comparisons
Source: Stacks Tags 079W, 08FE and 09RE.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

private theorem restriction_natural
    {S T Y : Scheme.{u}} (s : Y ⟶ S) (r : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s r)).obj N ⟶
      (derivedPullback (pullback.fst s r)).obj Q) :
    perfectHomOpenRestrictionMap s B r a
        ((derivedPullback (pullback.fst s r)).map g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
          ((schemeMVDerivedRestriction Y B).map g) ≫
        perfectHomOpenRestrictionMap s B r a f := by
  unfold perfectHomOpenRestrictionMap
  rw [Functor.map_comp]
  have hn := (perfectHomOpenPullbackComparison s B r a).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]

private theorem restricted_equiv
    {S T Y : Scheme.{u}} (s : Y ⟶ S) (r : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (P Q : schemeDerivedCategory Y)
    (e : ∀ M : schemeDerivedCategory Y, (M ⟶ P) ≃
      ((derivedPullback (pullback.fst s r)).obj M ⟶
        (derivedPullback (pullback.fst s r)).obj Q))
    (hn : ∀ (M N : schemeDerivedCategory Y) (g : M ⟶ N) (f : N ⟶ P),
      e M (g ≫ f) = (derivedPullback (pullback.fst s r)).map g ≫ e N f) :
    let L := schemeMVDerivedRestriction Y B
    let A := derivedPullback (pullback.fst (B.ι ≫ s) r)
    ∃ eb : ∀ N : schemeDerivedCategory B.toScheme,
        (N ⟶ L.obj P) ≃ (A.obj N ⟶ A.obj (L.obj Q)),
      (∀ (M N : schemeDerivedCategory B.toScheme) (g : M ⟶ N) (f : N ⟶ L.obj P),
        eb M (g ≫ f) = A.map g ≫ eb N f) ∧
      (∀ (M : schemeDerivedCategory Y) (f : M ⟶ P),
        eb (L.obj M) (L.map f) = perfectHomOpenRestrictionMap s B r a (e M f)) := by
  classical
  let L := schemeMVDerivedRestriction Y B
  let A := derivedPullback (pullback.fst (B.ι ≫ s) r)
  let A₀ := derivedPullback (pullback.fst s r)
  let _ := Classical.choice (nonempty_derivedOpenLocalization Y)
  have test (N : schemeDerivedCategory B.toScheme) :
      ∃ M : schemeDerivedCategory Y, Nonempty (N ≅ L.obj M) ∧
        ∀ E : schemeDerivedCategory Y, Function.Bijective (fun f : M ⟶ E ↦ L.map f) := by
    exact Scheme.exists_derivedOpen_testObject Y B N
  choose X δ hx using test
  let t (N : schemeDerivedCategory B.toScheme) : N ≅ L.obj (X N) :=
    Classical.choice (δ N)
  let lift (N : schemeDerivedCategory B.toScheme) (E : schemeDerivedCategory Y) :
      (N ⟶ L.obj E) ≃ (X N ⟶ E) :=
    (Iso.homCongr (t N) (Iso.refl _)).trans (Equiv.ofBijective _ (hx N E)).symm
  have lift_spec (N : schemeDerivedCategory B.toScheme) (E : schemeDerivedCategory Y)
      (f : N ⟶ L.obj E) : L.map (lift N E f) = (t N).inv ≫ f := by
    simpa only [lift, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
      Category.comp_id, Equiv.ofBijective_apply] using
      (Equiv.ofBijective _ (hx N E)).apply_symm_apply ((t N).inv ≫ f)
  have τbij (N : schemeDerivedCategory B.toScheme) :
      Function.Bijective (fun f : A₀.obj (X N) ⟶ A₀.obj Q ↦
        perfectHomOpenRestrictionMap s B r a f) := by
    exact perfect_hom_open_test_bijective s B r a (X N) Q (hx N)
      (perfectHomOpenPullbackComparison s B r a) rfl
  let transport (N : schemeDerivedCategory B.toScheme) :
      (A₀.obj (X N) ⟶ A₀.obj Q) ≃ (A.obj N ⟶ A.obj (L.obj Q)) :=
    (Equiv.ofBijective _ (τbij N)).trans
      (Iso.homCongr (A.mapIso (t N)).symm (Iso.refl _))
  have transport_apply (N : schemeDerivedCategory B.toScheme)
      (f : A₀.obj (X N) ⟶ A₀.obj Q) :
      transport N f = A.map (t N).hom ≫ perfectHomOpenRestrictionMap s B r a f := by
    simp only [transport, Equiv.trans_apply, Equiv.ofBijective_apply,
      Iso.homCongr_apply, Iso.symm_inv, Functor.mapIso_hom, Iso.refl_hom,
      Category.comp_id]
  have lift_comp (N : schemeDerivedCategory B.toScheme)
      (E E' : schemeDerivedCategory Y) (f : N ⟶ L.obj E) (g : E ⟶ E') :
      lift N E' (f ≫ L.map g) = lift N E f ≫ g := by
    apply (hx N E').injective
    dsimp only
    rw [L.map_comp, lift_spec, lift_spec, Category.assoc]
  let glift {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N) : X M ⟶ X N :=
    lift M (X N) (g ≫ (t N).hom)
  have glift_spec {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N) :
      L.map (glift g) = (t M).inv ≫ g ≫ (t N).hom := lift_spec _ _ _
  have lift_natural {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N)
      (E : schemeDerivedCategory Y) (f : N ⟶ L.obj E) :
      lift M E (g ≫ f) = glift g ≫ lift N E f := by
    apply (hx M E).injective
    dsimp only
    rw [L.map_comp, lift_spec, glift_spec, lift_spec]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have transport_natural {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N)
      (f : A₀.obj (X N) ⟶ A₀.obj Q) :
      transport M (A₀.map (glift g) ≫ f) = A.map g ≫ transport N f := by
    rw [transport_apply, transport_apply, restriction_natural,
      ← Category.assoc, ← Functor.map_comp, glift_spec]
    simp only [Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc]
  let eb (N : schemeDerivedCategory B.toScheme) :=
    (lift N P).trans ((e (X N)).trans (transport N))
  refine ⟨eb, ?_, ?_⟩
  · intro M N g f
    change transport M (e (X M) (lift M P (g ≫ f))) = _
    exact (congrArg (fun v ↦ transport M (e (X M) v)) (lift_natural g P f)).trans
      ((congrArg (transport M) (hn (X M) (X N) (glift g) (lift N P f))).trans
        (transport_natural g (e (X N) (lift N P f))))
  · intro M f
    let x := lift (L.obj M) M (𝟙 _)
    have hx' : L.map x = (t (L.obj M)).inv := by
      simpa only [Category.comp_id] using lift_spec (L.obj M) M (𝟙 _)
    have hf : lift (L.obj M) P (L.map f) = x ≫ f := by
      simpa only [Category.id_comp] using lift_comp (L.obj M) M P (𝟙 _) f
    change transport (L.obj M) (e (X (L.obj M)) (lift (L.obj M) P (L.map f))) = _
    rw [hf, hn, transport_apply, restriction_natural, hx',
      ← Category.assoc, ← Functor.map_comp]
    rw [Iso.hom_inv_id, A.map_id, Category.id_comp]

/-- Construct restricted Hom equivalences with prescribed values on identities.

Source: Stacks Project, Cohomology Tags 079W and 08FE; perfect.tex Tag 09RE.
Proof: for every testing object N on B use its supported extension X(N) from
Scheme.exists_derivedOpen_testObject, with t:N ≅ L(X(N)). Restriction on Hom out
of X(N) is bijective. Its inverse after precomposition with t.inv lifts N → LP
to X(N) → P. Compose this lifting equivalence with the supplied original Hom
equivalence and the cartesian restriction equivalence furnished by
perfect_hom_open_test_bijective, then precompose by pullback(t.hom).
Lift testing morphisms using the same Hom bijection. Injectivity of restriction
proves lift_natural and compatibility with postcomposition. Naturality of the
conjugated pullback map proves transport_natural, hence testing-object naturality
of the composed equivalence.
For an original M, lift id of LM to x:X(LM) → M. The lift equation says Lx=t.inv.
Postcomposition compatibility identifies the lift of Lf with x followed by f.
Original Hom naturality and cartesian restriction naturality therefore turn the
new value at Lf into pullback(t.hom) followed by pullback(Lx) followed by the
restriction of the old value at f. The first two factors cancel because Lx=t.inv.
This proves pinning for all M,f, in particular identities. Apply this construction
to each F_j and d.pt and assemble the four equivalence/naturality fields and the
two identity equations. It does not claim transition coherence or quasi-coherence.
The Hom equivalence is determined by these equations and naturality: its value
on any f:N → LP is determined after the supported testing isomorphism and unique
Hom lift. No data is defined by an arbitrary mere-existence witness. Empty opens
and zero objects yield singleton Hom sets, and the full open has the same inverse
cancellation; independent sign twists are excluded by identity normalization.
(blueprint: new-perfect-hom-open-restricted-pinned-equiv). -/
theorem perfect_hom_open_restricted_pinned_equiv
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    : ∃ e : PerfectHomOpenRestrictedEquivFields R c s B Q F d,
      (∀ j : Set.Ici i,
        e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) =
          perfectHomOpenRestrictionMap s B
            (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _))) ∧
      (e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv d.pt (𝟙 _))) := by
  classical
  have hs (j : Set.Ici i) := restricted_equiv s
    (Spec.map (R.map (homOfLE j.property))) B a (F.obj j) Q
      (h.stageEquiv j) (h.stageNatural j)
  choose es hns hps using hs
  obtain ⟨el, hnl, hpl⟩ := restricted_equiv s (Spec.map (c.ι.app i)) B a d.pt Q
    h.limitEquiv h.limitNatural
  refine ⟨{
    stageEquiv := es
    limitEquiv := el
    stageNatural := hns
    limitNatural := hnl }, ?_, ?_⟩
  · intro j
    exact (congrArg (es j ((schemeMVDerivedRestriction Y B).obj (F.obj j)))
      ((schemeMVDerivedRestriction Y B).map_id (F.obj j)).symm).trans
        (hps j (F.obj j) (𝟙 _))
  · exact (congrArg (el ((schemeMVDerivedRestriction Y B).obj d.pt))
      ((schemeMVDerivedRestriction Y B).map_id d.pt).symm).trans (hpl d.pt (𝟙 _))

end
end AlgebraicGeometry
