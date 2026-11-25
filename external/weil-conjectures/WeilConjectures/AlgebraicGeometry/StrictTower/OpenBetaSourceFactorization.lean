/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerPullbackSquarePasting

/-!
# Source factorization of the normalized inverse open comparison

Source: Stacks, Tags 03DI, 07A7 and 0F7B; the source-factorization calculation in
step 8 of (blueprint: lem-cbc-proper-open-clopen-projector).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
attribute [local irreducible] G gComp gCompEq squareG towers_hasDerivedCategory

private theorem source_square_aux {C : Type*} [Category C]
    {P Q R S T U : C} (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ S)
    (d : S ⟶ R) (e : Q ⟶ T) (f : P ⟶ U) (g : U ⟶ T)
    [IsIso b] [IsIso c] (h₁ : a ≫ b = c ≫ d) (h₂ : a ≫ e = f ≫ g) :
    d ≫ inv b ≫ e = inv c ≫ f ≫ g := by
  have hd : d ≫ inv b = inv c ≫ a := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h₁,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hd, Category.assoc, h₂]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_source_square
    {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {a : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ a κ ε)
    {V P W A T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ A) (i : A ⟶ T) (p : W ⟶ T)
    (h : (s ≫ b) ≫ p = (s ≫ q) ≫ i) (h₀ : q ≫ i = b ≫ p) (N : C T) :
    (κ s q (s ≫ q) rfl).hom.app ((L i).obj N) ≫
        (L s).map ((systemSquare κ q b i p h₀).inv.app N) =
      (systemSquare κ (s ≫ q) (s ≫ b) i p h.symm).inv.app N ≫
        (κ s b (s ≫ b) rfl).hom.app ((L p).obj N) := by
  have ha := NatTrans.congr_app (congrArg Iso.hom
    (S.assoc s q i (s ≫ q) (q ≫ i) ((s ≫ q) ≫ i)
      rfl rfl rfl (Category.assoc s q i).symm)) N
  have hb := NatTrans.congr_app (congrArg Iso.hom
    (S.assoc s b p (s ≫ b) (q ≫ i) ((s ≫ q) ≫ i)
      rfl h₀.symm h (Category.assoc s q i).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at ha hb
  have hh := source_square_aux _ _ _ _ _ _ _ ha hb
  simpa only [systemSquare, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, ← Functor.map_inv, NatIso.inv_hom_app, Category.assoc] using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem source_square {V P W S T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ S) (i : S ⟶ T) (p : W ⟶ T)
    (h : (s ≫ b) ≫ p = (s ≫ q) ≫ i) (h₀ : q ≫ i = b ≫ p)
    (N : Derived B T) :
    (gComp B s q).hom.app ((G B i).obj N) ≫
        (G B s).map ((squareG B q b i p h₀).inv.app N) =
      (squareG B (s ≫ q) (s ≫ b) i p h.symm).inv.app N ≫
        (gComp B s b).hom.app ((G B p).obj N) := by
  simpa only [← gCompEq_refl, ← squareG_system] using
    (system_source_square (pullbackSystem B) s b q i p h h₀ N)

private theorem transpose_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (d : R₂ ≅ R₁)
    (he : conjugateEquiv a b e.inv = d.inv)
    {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    b.homEquiv X Y (e.inv.app X ≫ f) ≫ d.hom.app Y = a.homEquiv X Y f := by
  have h := unit_conjugateEquiv a b e.inv X
  rw [he] at h
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← h]
  simp only [Category.assoc]
  rw [← reassoc_of% (d.inv.naturality f)]
  simp only [Iso.inv_hom_id_app, Category.comp_id]

/-- Factoring the source open through another open inserts precisely its open
adjunction counit in the inverse comparison. This requires neither properness nor
cartesianness and concerns the specified transformations on the full derived category.
Source: Stacks 03DI, 07A7 and 0F7B, the open-factorization calculation
(blueprint: lem-cbc-open-beta-source-factorization).
Proof: transpose both sides under the open adjunction for k. The compositor
jComp followed by jCongr is conjugate to the corresponding gComp and equality
transport. The counit for s cancels the unit introduced by the composite open
adjunction, by its triangle identity. Naturality moves the inverse-image
compositor across the remaining open unit. Associativity of the inverse-image
compositors identifies the remaining square with the square for r,k,i,p.
The two transposes are therefore G_r of the open unit for i followed by that
square's inverse. Injectivity of the adjunction Hom equivalence gives the equality.
This proof uses no faithfulness of evaluations and remains valid for the empty open. -/
theorem betaInv_source_factorization {V P W S T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ S)
    (k : V ⟶ W) (r : V ⟶ S) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k] [IsOpenImmersion i]
    (hk : s ≫ b = k) (hr : s ≫ q = r)
    (h : k ≫ p = r ≫ i) (h₀ : q ≫ i = b ≫ p) (M : Derived B S) :
    (betaInv B r k i p h.symm).app M =
      ((jComp B s b ≪≫ jCongr B hk).inv.app ((G B r).obj M)) ≫
      (J B b).map ((J B s).map
        ((((eqToIso (congrArg (G B) hr)).symm) ≪≫ gComp B s q).hom.app M) ≫
          (jAdj B s).counit.app ((G B q).obj M)) ≫
      (betaInv B q b i p h₀).app M := by
  subst k
  subst r
  let e := jComp B s b
  have he : conjugateEquiv ((jAdj B s).comp (jAdj B b))
      (jAdj B (s ≫ b)) e.inv = (gComp B s b).inv :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  apply ((jAdj B (s ≫ b)).homEquiv _ _).injective
  apply (cancel_mono ((gComp B s b).hom.app ((G B p).obj ((J B i).obj M)))).1
  change (jAdj B (s ≫ b)).homEquiv _ _
      (betaInvApp B (s ≫ q) (s ≫ b) i p h.symm M) ≫ _ = _
  rw [betaInvApp, Equiv.apply_symm_apply]
  simp only [jCongr, eqToIso_refl, Iso.refl_symm, Iso.trans_refl, Iso.refl_trans,
    Category.assoc]
  let f := (J B b).map ((J B s).map ((gComp B s q).hom.app M) ≫
    (jAdj B s).counit.app ((G B q).obj M)) ≫ (betaInv B q b i p h₀).app M
  have ht := transpose_conjugate ((jAdj B s).comp (jAdj B b))
    (jAdj B (s ≫ b)) e (gComp B s b) he f
  apply Eq.trans ?_ ht.symm
  dsimp only [f]
  rw [Adjunction.comp_homEquiv]
  change _ = (jAdj B s).homEquiv _ _ ((jAdj B b).homEquiv _ _
    ((J B b).map ((J B s).map ((gComp B s q).hom.app M) ≫
      (jAdj B s).counit.app ((G B q).obj M)) ≫
        (betaInv B q b i p h₀).app M))
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  have hε : (jAdj B s).homEquiv ((G B s).obj ((G B q).obj M))
      ((G B q).obj M) ((jAdj B s).counit.app ((G B q).obj M)) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [hε, Category.comp_id]
  change _ = (gComp B s q).hom.app M ≫
    (G B s).map ((jAdj B b).homEquiv _ _ (betaInvApp B q b i p h₀ M))
  rw [betaInvApp, Equiv.apply_symm_apply, Functor.map_comp]
  have hn := (gComp B s q).hom.naturality ((jAdj B i).unit.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  have hs := source_square B s b q i p h h₀ ((J B i).obj M)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn hs ⊢
  rw [← reassoc_of% hn, hs]

end AlgebraicGeometry.ProEtale.StrictTower
