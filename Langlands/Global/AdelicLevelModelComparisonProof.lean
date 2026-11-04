import Langlands.Global.AdelicLevelModelComparisonStatement
import Langlands.Global.CurvePlaceAdeleLevelTopologyProof
import Langlands.Global.NumberFieldAdeleLevelTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.LocalProductPointComparisonProof
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientProofs

/-! # Proof of the actual adelic-level model comparison -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C]

/-- An actual homeomorphic coefficient equivalence preserves affine evaluation topology. -/
theorem ringPointChangeRingEquiv_isHomeomorph
    (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₐ[C] B) (he : IsHomeomorph e) :
    IsHomeomorph (ringPointChangeRingEquiv C X e) := by
  let h : A ≃ₜ B := e.toEquiv.toHomeomorphOfContinuousOpen he.continuous he.isOpenMap
  let hp : RingPoint C X A ≃ₜ RingPoint C X B :=
    { toEquiv := ringPointChangeRingEquiv C X e
      continuous_toFun := affineSchemeCoefficientContinuity_proof C A B X
        e.toAlgHom he.continuous
      continuous_invFun := affineSchemeCoefficientContinuity_proof C B A X
        e.symm.toAlgHom h.symm.continuous }
  exact hp.isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- Reindexing the published level homeomorphism preserves the actual coefficient topology. -/
theorem curvePlaceLevelFactorAlgEquiv_isHomeomorph :
    IsHomeomorph (curvePlaceLevelFactorAlgEquiv k F S) := by
  exact (Homeomorph.sumPiEquivProdPi _ _ (CurvePlaceLevelFactor k F S)).symm.isHomeomorph.comp
    (curvePlaceAdeleLevelProductEquiv_isHomeomorph k F S)

variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

theorem curvePlaceLevelModelPointMap_injective [QuasiSeparatedSpace X.left] :
    Function.Injective (curvePlaceLevelModelPointMap k F S X) := by
  rw [curvePlaceLevelModelPointMap_eq]
  exact (localProductPointMap_injective _ _ X).comp
    (ringPointChangeRingEquiv _ X (curvePlaceLevelFactorAlgEquiv k F S)).injective

theorem curvePlaceLevelModelPointMap_surjective_of_isAffine [IsAffine X.left] :
    Function.Surjective (curvePlaceLevelModelPointMap k F S X) := by
  rw [curvePlaceLevelModelPointMap_eq]
  exact (localProductPointMap_surjective_of_isAffine _ _ X).comp
    (ringPointChangeRingEquiv _ X (curvePlaceLevelFactorAlgEquiv k F S)).surjective

theorem curvePlaceLevelModelPointMap_surjective [CompactSpace X.left] :
    Function.Surjective (curvePlaceLevelModelPointMap k F S X) := by
  rw [curvePlaceLevelModelPointMap_eq]
  exact (localProductPointMap_surjective _ _ X).comp
    (ringPointChangeRingEquiv _ X (curvePlaceLevelFactorAlgEquiv k F S)).surjective

theorem curvePlaceLevelModelPointMap_bijective
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    Function.Bijective (curvePlaceLevelModelPointMap k F S X) :=
  ⟨curvePlaceLevelModelPointMap_injective k F S X,
    curvePlaceLevelModelPointMap_surjective k F S X⟩

theorem curvePlaceLevelModelPointMap_isHomeomorph [IsAffine X.left] :
    IsHomeomorph (curvePlaceLevelModelPointMap k F S X) := by
  rw [curvePlaceLevelModelPointMap_eq]
  exact (localProductPointMap_isHomeomorph _ _ X).comp
    (ringPointChangeRingEquiv_isHomeomorph _ X (curvePlaceLevelFactorAlgEquiv k F S)
      (curvePlaceLevelFactorAlgEquiv_isHomeomorph k F S))

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- Both sum reindexings preserve the full level topology, including all infinite factors. -/
theorem numberFieldLevelFactorAlgEquiv_isHomeomorph :
    IsHomeomorph (numberFieldLevelFactorAlgEquiv K S) := by
  let h := (Homeomorph.sumPiEquivProdPi _ _ (NumberFieldLevelFactor K S)).trans
    ((Homeomorph.refl (InfiniteAdeles K)).prodCongr
      (Homeomorph.sumPiEquivProdPi _ _ (fun j => NumberFieldLevelFactor K S (.inr j))))
  exact h.symm.isHomeomorph.comp (numberFieldAdeleLevelProductEquiv_isHomeomorph K S)

variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

theorem numberFieldLevelModelPointMap_injective [QuasiSeparatedSpace X.left] :
    Function.Injective (numberFieldLevelModelPointMap K S X) := by
  rw [numberFieldLevelModelPointMap_eq]
  exact (localProductPointMap_injective _ _ X).comp
    (ringPointChangeRingEquiv _ X (numberFieldLevelFactorAlgEquiv K S)).injective

theorem numberFieldLevelModelPointMap_surjective_of_isAffine [IsAffine X.left] :
    Function.Surjective (numberFieldLevelModelPointMap K S X) := by
  rw [numberFieldLevelModelPointMap_eq]
  exact (localProductPointMap_surjective_of_isAffine _ _ X).comp
    (ringPointChangeRingEquiv _ X (numberFieldLevelFactorAlgEquiv K S)).surjective

theorem numberFieldLevelModelPointMap_surjective [CompactSpace X.left] :
    Function.Surjective (numberFieldLevelModelPointMap K S X) := by
  rw [numberFieldLevelModelPointMap_eq]
  exact (localProductPointMap_surjective _ _ X).comp
    (ringPointChangeRingEquiv _ X (numberFieldLevelFactorAlgEquiv K S)).surjective

theorem numberFieldLevelModelPointMap_bijective
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    Function.Bijective (numberFieldLevelModelPointMap K S X) :=
  ⟨numberFieldLevelModelPointMap_injective K S X,
    numberFieldLevelModelPointMap_surjective K S X⟩

theorem numberFieldLevelModelPointMap_isHomeomorph [IsAffine X.left] :
    IsHomeomorph (numberFieldLevelModelPointMap K S X) := by
  rw [numberFieldLevelModelPointMap_eq]
  exact (localProductPointMap_isHomeomorph _ _ X).comp
    (ringPointChangeRingEquiv_isHomeomorph _ X (numberFieldLevelFactorAlgEquiv K S)
      (numberFieldLevelFactorAlgEquiv_isHomeomorph K S))

end NumberField

/-- The exact five-clause actual curve-place model comparison. -/
theorem curvePlaceLevelModelComparison : CurvePlaceLevelModelComparisonStatement.{u} := by
  intro k F _ _ _ S X
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hQS
    exact curvePlaceLevelModelPointMap_injective k F S X
  · intro hAffine
    exact curvePlaceLevelModelPointMap_surjective_of_isAffine k F S X
  · intro hCompact
    exact curvePlaceLevelModelPointMap_surjective k F S X
  · intro hCompact hQS
    exact curvePlaceLevelModelPointMap_bijective k F S X
  · intro hAffine
    exact curvePlaceLevelModelPointMap_isHomeomorph k F S X

/-- The exact five-clause actual full number-field model comparison. -/
theorem numberFieldLevelModelComparison : NumberFieldLevelModelComparisonStatement.{u} := by
  intro K _ _ S X
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hQS
    exact numberFieldLevelModelPointMap_injective K S X
  · intro hAffine
    exact numberFieldLevelModelPointMap_surjective_of_isAffine K S X
  · intro hCompact
    exact numberFieldLevelModelPointMap_surjective K S X
  · intro hCompact hQS
    exact numberFieldLevelModelPointMap_bijective K S X
  · intro hAffine
    exact numberFieldLevelModelPointMap_isHomeomorph K S X

/-- The exact comparison target for both actual arithmetic level maps. -/
theorem adelicLevelModelComparison : AdelicLevelModelComparisonStatement.{u} :=
  ⟨curvePlaceLevelModelComparison, numberFieldLevelModelComparison⟩

end Langlands.Global
