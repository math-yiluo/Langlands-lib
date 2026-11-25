/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import WeilConjectures.Algebra.Homology.BaseLocalizationMap
import WeilConjectures.Algebra.Homology.BaseLocalizationComparisonAux
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-base-localization-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra Rp A] [Algebra Rp B]
  [tRpA : IsScalarTower R Rp A] [tRpB : IsScalarTower R Rp B]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [Algebra A D] [Algebra B D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] B) D]
  [tBpD : IsScalarTower B (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]

include tRpA tRpB tAD tBD tApD tBpD in
/-- Compatibility of the characterized map with localized augmentation.
Source: Stacks Project, Tags 0DJ8 and 06Y6.
(blueprint: lem-pc-base-localization-comparison).

Proof: the universal lift defining baseLocalizationDerivedMap satisfies its
counit equation by leftDerived_fac. Apply it to the restricted complex Q and
then cohomology. The ordinary tensor identification fixes b tensor x.
Combine this identity with both comparison_eq equations to identify the
ordinary comparison maps. Transpose by extension/restriction adjunction and
use localized_eq on both models. On a generator 1 tensor x, the resulting
D-linear square is exactly the formula defining IsBaseLocalizationMap.
Every ordinary complex identification tau satisfying the specified formula
coincides with the canonical identification: tensor induction proves equality
of its degree-j maps, and complex extensionality proves equality of chain
maps. Tensor induction likewise proves the D-linear square from its generators.
This proof uses neither invertibility of the comparison maps nor flatness
of D. Zero complexes and zero coefficient rings give the unique zero maps. -/
theorem baseLocalization_comparison (S : Submonoid R) [IsLocalization S Rp] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K.cohomology i))
    (he : IsBaseLocalizationMap R Rp B A D S Q L K i e.hom)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] B) D).comp
              (algebraMap A (A ⊗[Rp] B)))).mapHomologicalComplex (.up ℤ)).obj Q)
          (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A,(algebraMap (A ⊗[Rp] B) D).comp
                (algebraMap A (A ⊗[Rp] B))] x) :
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            e.hom ≫ K.localizedComparison i := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i)
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
    K.localizedComparison i (e.hom
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))
  rw [baseLocalization_comparison_aux R A B Rp D S i Q L K τ hτ, he]


end RingTensorCohomology
