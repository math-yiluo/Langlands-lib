/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree

/-! # Explicit Cech complexes in the right coefficient

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: def-sc-picard-external-right-cech-models).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Scalar Cech complexes as a functor of the coefficient.
Source: Stacks, Tag 0BED (blueprint: def-sc-picard-external-right-cech-models). -/
def picardCechFunctor (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type w} (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℕ :=
  scalarFunctor f ⋙ sheafToPresheaf _ _ ⋙ cechComplexFunctor U

/-- Tensor totals of the factor Cech complexes, extended by zero to integers.
Source: Stacks, Tag 0BED (blueprint: def-sc-picard-external-right-cech-models). -/
def picardRightTensorCechFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) :
    Y.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  picardCechFunctor g V ⋙
    ((curriedTensor (ModuleCat.{w} k)).map₂HomologicalComplex
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj
        ((picardCechFunctor f U).obj F) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{w} k)

/-- Product-cover Cech complexes of external coefficients, extended by zero.
Source: Stacks, Tag 0BED (blueprint: def-sc-picard-external-right-cech-models). -/
def picardRightProductCechFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) :
    Y.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  tensorPullback (pullback.snd f g) ⋙
    tensorLeft ((tensorPullback (pullback.fst f g)).obj F) ⋙
    picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{w} k)

/-- Scalar Cech preserves zero maps.
Source: the termwise formulas, Stacks Tag 0BED
(blueprint: def-sc-picard-external-right-cech-models). -/
instance picardCechFunctor_zero (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type w} (U : ι → X.Opens) : (picardCechFunctor f U).PreservesZeroMorphisms := by
  constructor
  intro A B
  apply HomologicalComplex.Hom.ext
  funext n
  apply TopCat.Presheaf.cechComplexFunctor_hom_ext U ((scalarSheaf f B).obj)
  intro y
  change ((cechComplexFunctor U).map ((scalarHom f (0 : A ⟶ B)).hom)).f n ≫ _ = _
  rw [TopCat.Presheaf.cechComplexFunctor_map_f_π]
  have hz : scalarHomApp f (0 : A ⟶ B) (Opposite.op (∏ᶜ fun l ↦ U (y l))) = 0 := by
    ext x
    rfl
  change _ ≫ scalarHomApp f (0 : A ⟶ B) _ = 0 ≫ _
  rw [hz, comp_zero, zero_comp]


/-- The tensor Cech functor preserves zero maps.
Source: the termwise tensor formula, Stacks Tag 0BED
(blueprint: def-sc-picard-external-right-cech-models). -/
instance picardRightTensorCechFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) :
    (picardRightTensorCechFunctor f g U V F).PreservesZeroMorphisms := by
  constructor
  intro A B
  change HomologicalComplex.extendMap
    (HomologicalComplex.mapBifunctorMap (𝟙 _) ((picardCechFunctor g V).map 0)
      (curriedTensor _) (ComplexShape.up ℕ)) ComplexShape.embeddingUpNat = 0
  rw [Functor.map_zero]
  suffices HomologicalComplex.mapBifunctorMap (𝟙 ((picardCechFunctor f U).obj F))
      (0 : (picardCechFunctor g V).obj A ⟶ (picardCechFunctor g V).obj B)
      (curriedTensor _) (ComplexShape.up ℕ) = 0 by
    rw [this, HomologicalComplex.extendMap_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp


/-- The product Cech functor preserves zero maps.
Source: the coefficient tensor formula, Stacks Tag 0BED
(blueprint: def-sc-picard-external-right-cech-models). -/
instance picardRightProductCechFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) :
    (picardRightProductCechFunctor f g U V F).PreservesZeroMorphisms := by
  let : (tensorPullback (pullback.snd f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction _)).left_adjoint_additive
  let : (tensorLeft ((tensorPullback (pullback.fst f g)).obj F)).Additive := by
    have : PreservesColimitsOfSize.{0, 0}
        (tensorLeft ((tensorPullback (pullback.fst f g)).obj F)) :=
      (SheafOfModules.tensorHomAdjunction (Limits.pullback f g).sheaf
        ((tensorPullback (pullback.fst f g)).obj F)).leftAdjoint_preservesColimits
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (tensorLeft ((tensorPullback (pullback.fst f g)).obj F))
    exact Functor.additive_of_preservesBinaryBiproducts _
  constructor
  intro A B
  change HomologicalComplex.extendMap
    ((picardCechFunctor (pullback.fst f g ≫ f) _).map
      ((tensorLeft ((tensorPullback (pullback.fst f g)).obj F)).map
        ((tensorPullback (pullback.snd f g)).map (0 : A ⟶ B))))
    ComplexShape.embeddingUpNat = 0
  rw [Functor.map_zero, Functor.map_zero, Functor.map_zero,
    HomologicalComplex.extendMap_zero]

end
end AlgebraicGeometry.Scheme.Modules
