import Langlands.ClassFieldTheory.Local.ClosureInflationNaturalityStatement
import Langlands.Cohomology.Continuous.EquivalenceTransport

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

namespace ClosureNaturality

section FiniteInflation

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L] [FiniteDimensional K M]

/-- Continuous normal restriction with the actual Krull topologies. -/
def normalRestriction : Gal(M/K) →ₜ* Gal(L/K) where
  __ := AlgEquiv.restrictNormalHom L
  continuous_toFun := continuous_of_discreteTopology

/-- The existing unit inclusion, regarded as a continuous coefficient map. -/
def continuousInflationCoefficients :
    TopRep.res (normalRestriction K L M) (discreteUnitsRepresentation K L) ⟶
      discreteUnitsRepresentation K M where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear L M
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes σ L x.val }

abbrev continuousInflation (n : ℕ) :
    continuousCohomology n (discreteUnitsRepresentation K L) ⟶
      continuousCohomology n (discreteUnitsRepresentation K M) :=
  ContinuousCohomology.map (normalRestriction K L M)
    (continuousInflationCoefficients K L M) n

/-- Comparison intertwines continuous inflation with the actual ordinary inflation. -/
theorem continuousInflation_comparison (n : ℕ)
    (x : continuousCohomology n (discreteUnitsRepresentation K L)) :
    continuousToRelative K M n (continuousInflation K L M n x) =
      relativeInflation K L M n (continuousToRelative K L n x) := by
  exact ConcreteCategory.congr_hom
    (Langlands.Continuous.continuousToOrdinary_naturality
      (discreteUnitsRepresentation K L) (discreteUnitsRepresentation K M)
      (normalRestriction K L M) (continuousInflationCoefficients K L M) n) x

end FiniteInflation

section Tower

variable (K : Type u) [Field K]
  (L M : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K M] [Normal K L] [Normal K M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M (AlgebraicClosure K)]

/-- Restricting through the larger field is direct restriction. -/
theorem normalRestriction_closure :
    (normalRestriction K L M).comp (closureRestriction K M) = closureRestriction K L := by
  apply ContinuousMonoidHom.ext
  intro σ
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M σ).symm

/-- Continuous inflation composes through the actual intermediate field. -/
theorem continuousInflation_closure (n : ℕ) :
    continuousInflation K L M n ≫ closureContinuousInflation K M n =
      closureContinuousInflation K L n := by
  rw [continuousInflation, closureContinuousInflation, closureContinuousInflation,
    ← ContinuousCohomology.map_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  apply Langlands.Continuous.continuousCochainsMap_congr
    (normalRestriction_closure K L M)
  intro x
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply L M (AlgebraicClosure K) x.val).symm

end Tower

section MixedFinite

variable (K E L M : Type u) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [Normal K L] [FiniteDimensional E M]

/-- Restrict the base scalars, then restrict to the normal source stage. -/
def mixedRestriction : Gal(M/E) →ₜ* Gal(L/K) where
  __ := (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  continuous_toFun := continuous_of_discreteTopology

/-- The actual stage-unit inclusion for the mixed restriction. -/
def mixedCoefficients :
    TopRep.res (mixedRestriction K E L M) (discreteUnitsRepresentation K L) ⟶
      discreteUnitsRepresentation E M where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear L M
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L x.val }

abbrev mixedContinuousMap (n : ℕ) :
    continuousCohomology n (discreteUnitsRepresentation K L) ⟶
      continuousCohomology n (discreteUnitsRepresentation E M) :=
  ContinuousCohomology.map (mixedRestriction K E L M) (mixedCoefficients K E L M) n

/-- The mixed continuous map compares to ordinary inflation followed by restriction. -/
theorem mixedContinuousMap_comparison (n : ℕ)
    (x : continuousCohomology n (discreteUnitsRepresentation K L)) :
    continuousToRelative E M n (mixedContinuousMap K E L M n x) =
      relativeRestriction K E M n
        (relativeInflation K L M n (continuousToRelative K L n x)) := by
  have hm : groupCohomology.map (mixedRestriction K E L M : Gal(M/E) →* Gal(L/K))
      (Rep.ofHom (mixedCoefficients K E L M).hom.toIntertwiningMap) n =
        relativeInflation K L M n ≫ relativeRestriction K E M n := by
    rw [relativeInflation, relativeRestriction, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr rfl
    rfl
  have h := ConcreteCategory.congr_hom
    (Langlands.Continuous.continuousToOrdinary_naturality
      (discreteUnitsRepresentation K L) (discreteUnitsRepresentation E M)
      (mixedRestriction K E L M) (mixedCoefficients K E L M) n) x
  exact h.trans (ConcreteCategory.congr_hom hm (continuousToRelative K L n x))

end MixedFinite

section BaseChange

variable (K E : Type u) [Field K] [Field E]
  [Algebra K E]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]
  (L : IntermediateField K (AlgebraicClosure K))
  (M : IntermediateField E (AlgebraicClosure E))
  [FiniteDimensional E M] [Normal K L] [Normal E M]
  [Algebra K M] [Algebra L M] [IsScalarTower K E M] [IsScalarTower K L M]
  (hcompat : ∀ a : L,
    algebraMap M (AlgebraicClosure E) (algebraMap L M a) =
      algebraMap (AlgebraicClosure K) (AlgebraicClosure E)
        (algebraMap L (AlgebraicClosure K) a))

include hcompat

/-- The field-induced group restrictions agree for the specified closure embedding. -/
theorem closure_mixedRestriction :
    (closureRestriction K L).comp (Field.absoluteGaloisGroup.mapOfAlgebra K E) =
      (mixedRestriction K E L M).comp (closureRestriction E M) := by
  apply ContinuousMonoidHom.ext
  intro σ
  change Gal(AlgebraicClosure E/E) at σ
  apply AlgEquiv.ext
  intro a
  change ((σ.restrictScalars K).restrictNormal (AlgebraicClosure K)).restrictNormal L a =
    ((σ.restrictNormal M).restrictScalars K).restrictNormal L a
  apply (algebraMap L (AlgebraicClosure K)).injective
  apply (algebraMap (AlgebraicClosure K) (AlgebraicClosure E)).injective
  calc
    _ = σ (algebraMap (AlgebraicClosure K) (AlgebraicClosure E)
        (algebraMap L (AlgebraicClosure K) a)) :=
      (congrArg (algebraMap (AlgebraicClosure K) (AlgebraicClosure E))
        (AlgEquiv.restrictNormal_commutes
          ((σ.restrictScalars K).restrictNormal (AlgebraicClosure K)) L a)).trans
        (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K)
          (AlgebraicClosure K) (algebraMap L (AlgebraicClosure K) a))
    _ = σ (algebraMap M (AlgebraicClosure E) (algebraMap L M a)) :=
      congrArg σ (hcompat a).symm
    _ = algebraMap M (AlgebraicClosure E)
        (algebraMap L M (((σ.restrictNormal M).restrictScalars K).restrictNormal L a)) :=
      (AlgEquiv.restrictNormal_commutes σ M (algebraMap L M a)).symm.trans
        (congrArg (algebraMap M (AlgebraicClosure E))
          (AlgEquiv.restrictNormal_commutes ((σ.restrictNormal M).restrictScalars K) L a).symm)
    _ = _ := hcompat _

/-- The continuous cohomology square follows from the two actual field map identities. -/
theorem closureContinuousInflation_baseChange (n : ℕ) :
    closureContinuousInflation K L n ≫ absoluteRestriction K E n =
      mixedContinuousMap K E L M n ≫ closureContinuousInflation E M n := by
  rw [closureContinuousInflation, absoluteRestriction, mixedContinuousMap,
    closureContinuousInflation, ← ContinuousCohomology.map_comp,
    ← ContinuousCohomology.map_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  apply Langlands.Continuous.continuousCochainsMap_congr
    (closure_mixedRestriction K E L M hcompat)
  intro x
  apply Units.ext
  exact (hcompat x.val).symm

end BaseChange

end ClosureNaturality

/-- Exact tower compatibility of the published ordinary-to-absolute inflation. -/
theorem closureInflationTowerCompatibility : ClosureInflationTowerCompatibility.{u} := by
  intro K _ L M _ _ _ _ _ _ _ n x
  obtain ⟨y, rfl⟩ := (continuousToRelativeEquiv K L n).surjective x
  change closureInflation K M n (relativeInflation K L M n (continuousToRelative K L n y)) =
    closureInflation K L n (continuousToRelative K L n y)
  rw [← ClosureNaturality.continuousInflation_comparison,
    closureInflation_continuousToRelative, closureInflation_continuousToRelative]
  exact ConcreteCategory.congr_hom (ClosureNaturality.continuousInflation_closure K L M n) y

/-- Exact mixed base-change compatibility, without normality of either larger field over K. -/
theorem closureInflationBaseChangeCompatibility : ClosureInflationBaseChangeCompatibility.{u} := by
  intro K E _ _ _ _ _ _ L M _ _ _ _ _ _ _ _ hcompat n x
  obtain ⟨y, rfl⟩ := (continuousToRelativeEquiv K L n).surjective x
  change absoluteRestriction K E n (closureInflation K L n (continuousToRelative K L n y)) =
    closureInflation E M n
      (relativeRestriction K E M n (relativeInflation K L M n (continuousToRelative K L n y)))
  rw [← ClosureNaturality.mixedContinuousMap_comparison,
    closureInflation_continuousToRelative, closureInflation_continuousToRelative]
  exact ConcreteCategory.congr_hom
    (ClosureNaturality.closureContinuousInflation_baseChange K E L M hcompat n) y

end Langlands.ClassFieldTheory.Local
