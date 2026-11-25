/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

import WeilConjectures.AlgebraicGeometry.OpenRestrictionClosedMonoidal

/-! # Open restriction of canonical derived evaluation

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-pc-canonical-evaluation-open-restriction).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-canonical-evaluation-open-restriction). -/
local instance restrictionEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem closedMonoidal_evaluation
    {C : Type*} {B : Type*} [Category C] [Category B]
    [MonoidalCategory C] [MonoidalCategory B]
    (R : C ⥤ B) [R.Monoidal] (H : Cᵒᵖ × C ⥤ C) (J : Bᵒᵖ × B ⥤ B)
    (e : ∀ A K N : C, (A ⟶ H.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (f : ∀ A K N : B, (A ⟶ J.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (hf : ∀ A A' K N N' (a : A' ⟶ A) (c : N ⟶ N')
      (ξ : A ⟶ J.obj (op K, N)),
      f A' K N' (a ≫ ξ ≫ J.map ((𝟙 K).op, c)) =
        (a ⊗ₘ 𝟙 K) ≫ f A K N ξ ≫ c)
    (h : ∀ K N, R.obj (H.obj (op K, N)) ≅ J.obj (op (R.obj K), R.obj N))
    (hh : ∀ A K N (ξ : A ⟶ H.obj (op K, N)),
      f (R.obj A) (R.obj K) (R.obj N) (R.map ξ ≫ (h K N).hom) =
        (Functor.Monoidal.μIso R A K).hom ≫ R.map (e A K N ξ)) (K N : C) :
    let D := H.obj (op K, 𝟙_ C)
    let DU := J.obj (op (R.obj K), 𝟙_ B)
    let g := (e (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁ (e D K (𝟙_ C) (𝟙 D)) ≫ (ρ_ N).hom)
    let gU := (f (R.obj N ⊗ DU) (R.obj K) (R.obj N)).symm
      ((α_ (R.obj N) DU (R.obj K)).hom ≫
        R.obj N ◁ (f DU (R.obj K) (𝟙_ B) (𝟙 DU)) ≫ (ρ_ (R.obj N)).hom)
    ∃ a : R.obj (N ⊗ D) ≅ R.obj N ⊗ DU,
      ∃ b : R.obj (H.obj (op K, N)) ≅ J.obj (op (R.obj K), R.obj N),
        R.map g ≫ b.hom = a.hom ≫ gU := by
  classical
  dsimp only
  let D := H.obj (op K, 𝟙_ C)
  let DU := J.obj (op (R.obj K), 𝟙_ B)
  let u : R.obj (𝟙_ C) ≅ 𝟙_ B := (Functor.Monoidal.εIso R).symm
  let d : R.obj D ≅ DU := h K (𝟙_ C) ≪≫
    J.mapIso ((Iso.refl (op (R.obj K))).prod u)
  let a : R.obj (N ⊗ D) ≅ R.obj N ⊗ DU :=
    (Functor.Monoidal.μIso R N D).symm ≪≫ tensorIso (Iso.refl _) d
  let ev := e D K (𝟙_ C) (𝟙 D)
  let evU := f DU (R.obj K) (𝟙_ B) (𝟙 DU)
  have hid (Y : B) :
      J.map (X := (op (R.obj K), Y)) (Y := (op (R.obj K), Y))
        ((𝟙 (R.obj K)).op, 𝟙 Y) = 𝟙 (J.obj (op (R.obj K), Y)) := by
    rw [op_id, ← prod_id']
    exact J.map_id _
  have hd : d.hom ▷ R.obj K ≫ evU =
      (Functor.Monoidal.μIso R D K).hom ≫ R.map ev ≫ u.hom := by
    have h₁ := hf DU (R.obj D) (R.obj K) (𝟙_ B) (𝟙_ B) d.hom (𝟙 _) (𝟙 DU)
    have h₂ := hf (R.obj D) (R.obj D)
      (R.obj K) (R.obj (𝟙_ C)) (𝟙_ B) (𝟙 _) u.hom (h K (𝟙_ C)).hom
    simp only [hid, Category.comp_id, tensorHom_id] at h₁
    simp only [Category.id_comp, tensorHom_id, id_whiskerRight] at h₂
    rw [← h₁]
    change f _ _ _ ((h K (𝟙_ C)).hom ≫ J.map ((𝟙 (R.obj K)).op, u.hom)) = _
    rw [h₂]
    have h₃ := hh D K (𝟙_ C) (𝟙 D)
    simp only [R.map_id, Category.id_comp] at h₃
    rw [h₃]
    simp [ev]
  refine ⟨a, h K N, ?_⟩
  apply (f _ _ _).injective
  rw [hh]
  have hn := hf (R.obj N ⊗ DU) (R.obj (N ⊗ D)) (R.obj K)
    (R.obj N) (R.obj N) a.hom (𝟙 _)
    ((f (R.obj N ⊗ DU) (R.obj K) (R.obj N)).symm
      ((α_ (R.obj N) DU (R.obj K)).hom ≫ R.obj N ◁ evU ≫ (ρ_ (R.obj N)).hom))
  simp only [hid, Category.comp_id, Equiv.apply_symm_apply] at hn
  rw [hn]
  simp only [Equiv.apply_symm_apply, Functor.map_comp]
  change (Functor.Monoidal.μIso R (N ⊗ D) K).hom ≫
    R.map (α_ N D K).hom ≫ R.map (N ◁ ev) ≫ R.map (ρ_ N).hom =
    (a.hom ⊗ₘ 𝟙 (R.obj K)) ≫ (α_ (R.obj N) DU (R.obj K)).hom ≫
      R.obj N ◁ evU ≫ (ρ_ (R.obj N)).hom
  simp only [a, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    id_tensorHom, tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, hd]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    u, Iso.symm_hom, Functor.Monoidal.εIso_inv]
  rw [Functor.Monoidal.map_associator]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.Monoidal.map_rightUnitor]
  simp


/-- Restriction preserves the canonical derived evaluation arrow, including its
source and target comparisons. This is independent of any ordinary complex model.

Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom),
Tag 08DL (lemma-restriction-RHom-to-U), and Tag 06YH (derived tensor construction).
(blueprint: lem-pc-canonical-evaluation-open-restriction).

Proof:
1. Pass from the over-site to the open scheme by Modules.overEquiv. Its derived
   functor is an equivalence, also between independently specified localization
   universes. Compose it with exact open restriction to form R.
2. Restrict K-flat tensor representatives. Restriction preserves K-flatness and
   commutes with sheaf tensor and its direct-sum totalization. This gives the
   natural strong tensor comparison and the comparison of the degree-zero units.
3. Restrict the fixed K-injective Hom representatives. Open restriction preserves
   K-injectivity and commutes with the product Hom complex. This gives the natural
   Hom comparison. Its representative formula is restriction of each local map.
4. On a total-tensor summand, the uncurrying formula for the canonical tensor-Hom
   family evaluates the same local map before or after restriction. Thus its
   evaluation counit commutes with the tensor and Hom comparisons. Naturality of
   associators and right unitors, and the unit comparison, carry the adjunct
   defining g to the corresponding adjunct on the open scheme. Composing the
   tensor comparison with the dual Hom comparison gives a, and the Hom comparison
   gives b. Faithfulness of the tensor-Hom equivalence gives the displayed square.
No ordinary evaluation inverse or exactness assumption on a complex is used.
The same constructions apply to the empty open and to zero objects. -/
theorem exists_canonicalEvaluation_open_restriction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
    let HU := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let KU := R.obj K
    let NU := R.obj N
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let DU := HU.obj (op KU, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    let gU := ((schemeDerivedTensorHomEquiv U.toScheme) (NU ⊗ DU) KU NU).symm
      ((α_ NU DU KU).hom ≫ NU ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) DU KU
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 DU)) ≫ (ρ_ NU).hom)
    ∃ a : R.obj (N ⊗ D) ≅ NU ⊗ DU,
      ∃ b : R.obj (H.obj (op K, N)) ≅ HU.obj (op KU, NU),
        R.map g ≫ b.hom = a.hom ≫ gU := by
  -- Keep the derived functors and evaluation arrows shared while eliminating the witnesses.
  intro E R H HU KU NU D DU g gU
  refine (exists_openRestriction_closedMonoidal X U).elim fun m hm ↦ ?_
  let := m
  refine hm.elim fun h hh ↦ ?_
  exact closedMonoidal_evaluation _ _ _ (schemeDerivedTensorHomEquiv X)
    (schemeDerivedTensorHomEquiv U.toScheme)
    (fun A A' K N N' a c ξ ↦
      (Classical.choose_spec (exists_canonicalDerivedTensorHom U.toScheme)).1
        A A' K K N N' a (𝟙 K) c ξ) h hh K N

end AlgebraicGeometry
