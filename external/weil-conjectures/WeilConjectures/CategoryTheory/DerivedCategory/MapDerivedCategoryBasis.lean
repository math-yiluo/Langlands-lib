/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.NatTransId
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Bases of the unit of a levelwise derived adjunction

Let `adj : f ⊣ g` be an adjunction of exact functors between abelian categories, and let
`τ : ι → (𝟭 B ⟶ 𝟭 B)` be a finite family of natural endomorphisms of the identity of `B` (for
instance the multiplications by the elements of a basis of a finite free extension of scalars)
such that, for every object `M`, the morphism
`⨁_i M ⟶ g (f M)` with components `η_M ≫ g (τ_i (f M))` is an isomorphism. Then the analogous
morphism `⨁_i K ⟶ D(g) (D(f) K)` built from the unit of the levelwise derived adjunction
`D(f) ⊣ D(g)` and the induced endomorphisms `DerivedCategory.natTransId (τ i)` is an isomorphism
for every object `K` of the derived category
(`CategoryTheory.Adjunction.isIso_biproductDesc_mapDerivedCategoryAdjunction_unit`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

/-- Let `φ_i : P ⟶ R` and `ψ_i : P' ⟶ R'` be two families of morphisms which correspond to each
other under isomorphisms `P ≅ P'` and `R ≅ R'`. Then the morphism `⨁_i P ⟶ R` with components
`φ_i` is an isomorphism if and only if the morphism `⨁_i P' ⟶ R'` with components `ψ_i` is. -/
lemma CategoryTheory.Limits.isIso_biproduct_desc_iff_of_iso {C : Type*} [Category* C]
    [Preadditive C] {ι : Type*} {P P' R R' : C} [HasBiproduct fun _ : ι ↦ P]
    [HasBiproduct fun _ : ι ↦ P'] (φ : ι → (P ⟶ R)) (ψ : ι → (P' ⟶ R')) (a : P ≅ P')
    (b : R ≅ R') (h : ∀ i, φ i ≫ b.hom = a.hom ≫ ψ i) :
    IsIso (biproduct.desc φ) ↔ IsIso (biproduct.desc ψ) := by
  have e : biproduct.desc φ =
      (biproduct.mapIso fun _ ↦ a).hom ≫ biproduct.desc ψ ≫ b.inv := by
    refine biproduct.hom_ext' _ _ (fun i ↦ ?_)
    simp [← reassoc_of% (h i)]
  rw [e, isIso_comp_left_iff, isIso_comp_right_iff]

namespace CategoryTheory.Adjunction

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [HasCountableCoproducts A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasKInjectiveResolutions B]
  {f : A ⥤ B} {g : B ⥤ A} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The morphisms `η_K ≫ D(g) (s_i (D(f) K))`, where `η` is the unit of `D(f) ⊣ D(g)` and the `s_i`
are natural endomorphisms of the identity of `D(B)`, are natural in `K`. -/
lemma mapDerivedCategoryAdjunction_unit_app_comp_map_natTrans_app_naturality
    (s : 𝟭 (DerivedCategory B) ⟶ 𝟭 (DerivedCategory B)) {K K' : DerivedCategory A}
    (e : K ⟶ K') :
    (adj.mapDerivedCategoryAdjunction.unit.app K ≫
        g.mapDerivedCategory.map (s.app (f.mapDerivedCategory.obj K))) ≫
        g.mapDerivedCategory.map (f.mapDerivedCategory.map e) =
      e ≫ adj.mapDerivedCategoryAdjunction.unit.app K' ≫
        g.mapDerivedCategory.map (s.app (f.mapDerivedCategory.obj K')) := by
  have hu := adj.mapDerivedCategoryAdjunction.unit.naturality e
  have hs := s.naturality (f.mapDerivedCategory.map e)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hu hs
  rw [Category.assoc, ← Functor.map_comp, ← hs, Functor.map_comp, reassoc_of% hu]

/-- On the image of a cochain complex `Y`, the morphisms `η ≫ D(g) (s_i (D(f) K))` are, up to
the factorization isomorphisms, the images of the levelwise morphisms
`η_Y ≫ g (τ_i (f Y))`. -/
lemma mapDerivedCategoryAdjunction_unit_app_comp_map_natTransId_app_Qh_obj_quotient_obj
    (τ : 𝟭 B ⟶ 𝟭 B) (Y : CochainComplex A ℤ) :
    (adj.mapDerivedCategoryAdjunction.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≫
        g.mapDerivedCategory.map ((DerivedCategory.natTransId τ).app (f.mapDerivedCategory.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))))) ≫
        (g.mapDerivedCategory.mapIso (f.mapDerivedCategoryFactorsh.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≪≫
          g.mapDerivedCategoryFactorsh.app ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))).hom =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app Y ≫
          (g.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((HomologicalComplex.natTransId τ (ComplexShape.up ℤ)).app
              ((f.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y)))) := by
  have hs := (DerivedCategory.natTransId τ).naturality
    (f.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))
  have hτ := DerivedCategory.natTransId_app_Qh_obj_quotient_obj τ
    ((f.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y)
  have hG := g.mapDerivedCategoryFactorsh.hom.naturality
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((HomologicalComplex.natTransId τ (ComplexShape.up ℤ)).app
        ((f.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y)))
  have hu := adj.mapDerivedCategoryAdjunction_unit_app_Qh_obj
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)
  rw [mapHomotopyCategory_unit_app_quotient] at hu
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hs hG
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hs, Functor.map_comp_assoc]
  erw [hτ, hG, reassoc_of% hu]
  rw [Functor.map_comp, Functor.map_comp]
  rfl

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Let `τ : ι → (𝟭 B ⟶ 𝟭 B)` be a finite family of natural endomorphisms of the identity of `B`
such that for every `M : A`, the morphism `⨁_i M ⟶ g (f M)` with components
`η_M ≫ g (τ_i (f M))` is an isomorphism. Then for every object `K` of the derived category, the
morphism `⨁_i K ⟶ D(g) (D(f) K)` with components `η_K ≫ D(g) (τ_i (D(f) K))`, built from the unit
of the levelwise derived adjunction `D(f) ⊣ D(g)` and the induced endomorphisms
`DerivedCategory.natTransId (τ i)`, is an isomorphism. -/
theorem isIso_biproductDesc_mapDerivedCategoryAdjunction_unit {ι : Type*} [Finite ι]
    (τ : ι → (𝟭 B ⟶ 𝟭 B))
    (hτ : ∀ M : A, IsIso (biproduct.desc fun i ↦ adj.unit.app M ≫ g.map ((τ i).app (f.obj M))))
    (K : DerivedCategory A) :
    IsIso (biproduct.desc fun i ↦ adj.mapDerivedCategoryAdjunction.unit.app K ≫
      g.mapDerivedCategory.map ((DerivedCategory.natTransId (τ i)).app
        (f.mapDerivedCategory.obj K))) := by
  obtain ⟨X, ⟨e⟩⟩ : ∃ X, Nonempty (DerivedCategory.Qh.obj X ≅ K) :=
    ⟨_, ⟨DerivedCategory.Qh.objObjPreimageIso K⟩⟩
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [← isIso_biproduct_desc_iff_of_iso _ _ e
    (g.mapDerivedCategory.mapIso (f.mapDerivedCategory.mapIso e)) (fun i ↦
      adj.mapDerivedCategoryAdjunction_unit_app_comp_map_natTrans_app_naturality _ e.hom)]
  let c (i : ι) : Y ⟶ (g.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((f.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) :=
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app Y ≫
      (g.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.natTransId (τ i) (ComplexShape.up ℤ)).app
          ((f.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y))
  refine (isIso_biproduct_desc_iff_of_iso _
    (fun i ↦ (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map (c i))
    (Iso.refl _) (g.mapDerivedCategory.mapIso (f.mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≪≫
      g.mapDerivedCategoryFactorsh.app ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))) (fun i ↦
      (adj.mapDerivedCategoryAdjunction_unit_app_comp_map_natTransId_app_Qh_obj_quotient_obj
        (τ i) Y).trans (Category.id_comp _).symm)).2 ?_
  have := (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    |>.preservesBiproductsOfShape_of_additive (J := ι)
  rw [← biproduct.mapBiproduct_inv_map_desc, isIso_comp_left_iff]
  have h (n : ℤ) : IsIso ((biproduct.desc c).f n) := by
    have := (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
      |>.preservesBiproductsOfShape_of_additive (J := ι)
    rw [← HomologicalComplex.eval_map,
      ← biproduct.mapBiproduct_hom_desc (HomologicalComplex.eval A (ComplexShape.up ℤ) n)]
    have : IsIso (biproduct.desc fun j ↦
        (HomologicalComplex.eval A (ComplexShape.up ℤ) n).map (c j)) :=
      hτ (Y.X n)
    exact IsIso.comp_isIso' (Iso.isIso_hom _) this
  have := HomologicalComplex.Hom.isIso_of_components (biproduct.desc c)
  infer_instance

end CategoryTheory.Adjunction
