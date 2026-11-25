/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # One-variable localized evaluation compatibility

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-precomposition).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem dinatural_comp {C : Type*} [Category* C] [MonoidalCategory C]
    (H : Cᵒᵖ × C ⥤ C) {A B D M : C} (f : A ⟶ B) (g : B ⟶ D)
    (eA : H.obj (op A, M) ⊗ A ⟶ M)
    (eB : H.obj (op B, M) ⊗ B ⟶ M)
    (eD : H.obj (op D, M) ⊗ D ⟶ M)
    (hf : (H.map (f.op, 𝟙 M) ⊗ₘ 𝟙 A) ≫ eA = (𝟙 _ ⊗ₘ f) ≫ eB)
    (hg : (H.map (g.op, 𝟙 M) ⊗ₘ 𝟙 B) ≫ eB = (𝟙 _ ⊗ₘ g) ≫ eD) :
    (H.map ((f ≫ g).op, 𝟙 M) ⊗ₘ 𝟙 A) ≫ eA = (𝟙 _ ⊗ₘ (f ≫ g)) ≫ eD := by
  have hm : H.map ((f ≫ g).op, 𝟙 M) =
      H.map (X := (op D, M)) (Y := (op B, M)) (g.op, 𝟙 M) ≫
        H.map (X := (op B, M)) (Y := (op A, M)) (f.op, 𝟙 M) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hm, comp_tensor_id, Category.assoc, hf]
  rw [← Category.assoc, tensor_id_comp_id_tensor,
    ← id_tensor_comp_tensor_id, Category.assoc, hg, ← id_tensor_comp_assoc]

private theorem dinatural_inv {C : Type*} [Category* C] [MonoidalCategory C]
    (H : Cᵒᵖ × C ⥤ C) {A B M : C} (f : A ⟶ B) [IsIso f]
    (eA : H.obj (op A, M) ⊗ A ⟶ M)
    (eB : H.obj (op B, M) ⊗ B ⟶ M)
    (hf : (H.map (f.op, 𝟙 M) ⊗ₘ 𝟙 A) ≫ eA = (𝟙 _ ⊗ₘ f) ≫ eB) :
    (H.map ((inv f).op, 𝟙 M) ⊗ₘ 𝟙 B) ≫ eB = (𝟙 _ ⊗ₘ inv f) ≫ eA := by
  have hm : H.map (X := (op B, M)) (Y := (op A, M)) (f.op, 𝟙 M) ≫
      H.map (X := (op A, M)) (Y := (op B, M)) ((inv f).op, 𝟙 M) = 𝟙 _ := by
    rw [← H.map_comp]
    have hpair : (show (op B, M) ⟶ (op A, M) from (f.op, 𝟙 M)) ≫
        ((inv f).op, 𝟙 M) = 𝟙 (op B, M) := by
      ext <;> simp
    rw [hpair, H.map_id]
  have : IsIso (H.map (X := (op B, M)) (Y := (op A, M)) (f.op, 𝟙 M)) := by
    have : IsIso (show (op B, M) ⟶ (op A, M) from (f.op, 𝟙 M)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    infer_instance
  apply (cancel_epi (H.map (X := (op B, M)) (Y := (op A, M)) (f.op, 𝟙 M) ⊗ₘ 𝟙 B)).mp
  rw [← comp_tensor_id_assoc, hm]
  simp only [id_tensorHom_id, Category.id_comp]
  rw [← Category.assoc, tensor_id_comp_id_tensor,
    ← id_tensor_comp_tensor_id, Category.assoc, hf, ← id_tensor_comp_assoc]
  simp

private theorem dinatural_right_fraction {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory D] (Q : C ⥤ D) (H : Dᵒᵖ × D ⥤ D) (M : D)
    (e : ∀ L : C, H.obj (op (Q.obj L), M) ⊗ Q.obj L ⟶ M)
    (h : ∀ (L L' : C) (b : L ⟶ L'),
      (H.map ((Q.map b).op, 𝟙 M) ⊗ₘ 𝟙 (Q.obj L)) ≫ e L =
        (𝟙 _ ⊗ₘ Q.map b) ≫ e L')
    {L L' : C} (b : Q.obj L ⟶ Q.obj L')
    (hb : ∃ (R : C) (s : R ⟶ L) (_ : IsIso (Q.map s)) (g : R ⟶ L'),
      b = inv (Q.map s) ≫ Q.map g) :
    (H.map (b.op, 𝟙 M) ⊗ₘ 𝟙 (Q.obj L)) ≫ e L = (𝟙 _ ⊗ₘ b) ≫ e L' := by
  obtain ⟨R, s, hs, g, rfl⟩ := hb
  have := hs
  exact dinatural_comp H (inv (Q.map s)) (Q.map g) _ _ _
    (dinatural_inv H (Q.map s) _ _ (h R L s)) (h R L' g)

private theorem normalized_chain {C : Type*} [Category* C] [MonoidalCategory C]
    {A A' H H' L L' M : C}
    (d : A' ⟶ A) (j : A ⟶ H) (j' : A' ⟶ H') (f : H' ⟶ H) (b : L ⟶ L')
    (U : H ⊗ L ⟶ M) (U' : H' ⊗ L' ⟶ M)
    (hj : d ≫ j = j' ≫ f)
    (hraw : (f ⊗ₘ 𝟙 L) ≫ U = (𝟙 H' ⊗ₘ b) ≫ U') :
    (d ⊗ₘ 𝟙 L) ≫ (j ⊗ₘ 𝟙 L) ≫ U = (𝟙 A' ⊗ₘ b) ≫ (j' ⊗ₘ 𝟙 L') ≫ U' := by
  rw [← comp_tensor_id_assoc, hj, comp_tensor_id_assoc, hraw]
  rw [← Category.assoc, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id,
    Category.assoc]

private def evaluation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := schemeDerivedTensorMonoidal X
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
      (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ⊗ DerivedCategory.Q.obj L ⟶
        DerivedCategory.Q.obj M :=
  letI := schemeDerivedTensorMonoidal X
  ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
      𝟙 (DerivedCategory.Q.obj L)) ≫
    pullbackTensorModelMap X _ L ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
        schemeHomResolutionInverse X M

private theorem hom_resolution_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L L' M M' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : L' ⟶ L) (c : M ⟶ M') :
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        ((DerivedCategory.Q.map b).op, DerivedCategory.Q.map c) ≫
          (schemeDerivedInternalHomResolutionIso X L' M').hom =
      (schemeDerivedInternalHomResolutionIso X L M).hom ≫
        DerivedCategory.Q.map
          ((Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
            (X := (op L, (schemeHomKInjectiveResolution X).obj M))
            (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
            (b.op, (schemeHomKInjectiveResolution X).map c)) := by
  have := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  exact (Localization.fac _
    (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf
      (CochainComplex.kInjectiveResolutionFunctor.{u}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (CochainComplex.toKInjectiveResolution.{u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).hom.naturality
      (X := (op L, M)) (Y := (op L', M')) (b.op, c)

-- The localization factorization elaborates through the sheaf and derived tensor instances.
set_option backward.isDefEq.respectTransparency.types true in
private theorem evaluation_chain (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L L' M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : L ⟶ L') :
    letI := schemeDerivedTensorMonoidal X
    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        ((DerivedCategory.Q.map b).op, 𝟙 (DerivedCategory.Q.obj M)) ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫ evaluation X L M =
      (𝟙 _ ⊗ₘ DerivedCategory.Q.map b) ≫ evaluation X L' M := by
  let := schemeDerivedTensorMonoidal X
  let H := homComplex (R := X.sheaf) L ((schemeHomKInjectiveResolution X).obj M)
  let H' := homComplex (R := X.sheaf) L' ((schemeHomKInjectiveResolution X).obj M)
  let f : H' ⟶ H := (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
    (X := (op L', (schemeHomKInjectiveResolution X).obj M))
    (Y := (op L, (schemeHomKInjectiveResolution X).obj M))
    (b.op, (schemeHomKInjectiveResolution X).map (𝟙 M))
  have h₁ := schemeTensorHomUncurry_localized_evaluation X H' H' L' L M M
    (𝟙 H') b (𝟙 M) (𝟙 H')
  have h₂ := schemeTensorHomUncurry_localized_evaluation X H H' L L M M
    f (𝟙 L) (𝟙 M) (𝟙 H)
  have hid : ((𝟙 L).op, (schemeHomKInjectiveResolution X).map (𝟙 M)) =
      𝟙 (op L, (schemeHomKInjectiveResolution X).obj M) := by
    rw [(schemeHomKInjectiveResolution X).map_id M, op_id]
    rfl
  simp only [Category.id_comp] at h₁ h₂
  rw [hid, (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map_id] at h₂
  simp only [Category.comp_id, DerivedCategory.Q.map_id] at h₁ h₂
  have hraw := h₂.symm.trans h₁
  have hj :
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        ((DerivedCategory.Q.map b).op, 𝟙 (DerivedCategory.Q.obj M)) ≫
          (schemeDerivedInternalHomResolutionIso X L M).hom =
      (schemeDerivedInternalHomResolutionIso X L' M).hom ≫ DerivedCategory.Q.map f := by
    simpa only [DerivedCategory.Q.map_id] using
      hom_resolution_naturality X L' L M M b (𝟙 M)
  exact normalized_chain _ _ _ _ _ _ _ hj hraw

-- Matching the fixed evaluation expression uses the shared sheaf localization instances.
set_option backward.isDefEq.respectTransparency.types true in
/-- One-variable compatibility of the explicit localized identity evaluation.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-precomposition).

Proof: Evaluation is dinatural in the complex being evaluated. Resolve L and L' by
K-flat complexes and represent b on a common K-flat roof. Hom into I(M) is
K-injective on these models, so the comparison is computed by chain maps modulo
homotopy. On each total tensor summand, the Hom projection and sheaf tensor-Hom
adjunction identify evaluation after Hom precomposition with evaluation after
applying the comparison in the tensor factor. Extend over the coproduct to get the
chain-map identity. Uncurry the degree-minus-one components to carry chain
homotopies to tensor homotopies using the signed Hom differential formula. Apply
Q; naturality of its lax tensor comparison and the Hom resolution comparison
identifies the resulting composites. Cancel the localized roof denominators and
K-flat resolutions. This proves the displayed identity for arbitrary unbounded
L and L'; zero complexes, zero maps, and identity comparisons obey the same
summand identity. -/
theorem tensorHomEvaluation_precomposition (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L L' M : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
    letI := schemeDerivedTensorMonoidal X
    let E := fun L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ↦
      ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X (homComplex (R := X.sheaf) L
          ((schemeHomKInjectiveResolution X).obj M)) L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
        schemeHomResolutionInverse X M
    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        (b.hom.op, 𝟙 (DerivedCategory.Q.obj M)) ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫ E L M =
      (𝟙 _ ⊗ₘ b.hom) ≫ E L' M := by
  let := schemeDerivedTensorMonoidal X
  -- Dinaturality on chain maps extends to a right fraction by inversion and composition.
  exact dinatural_right_fraction DerivedCategory.Q
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf) (DerivedCategory.Q.obj M)
    (fun L ↦ evaluation X L M) (fun L L' b ↦ evaluation_chain X L L' M b)
    b.hom (DerivedCategory.right_fac b.hom)

end AlgebraicGeometry
