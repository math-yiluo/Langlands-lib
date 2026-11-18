import Langlands.ClassFieldTheory.Local.ClosureInflationNaturalityProof
import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Mathlib.FieldTheory.SeparableClosure

/-! # Continuous cohomology of separable-closure units -/

noncomputable section

open CategoryTheory

universe u

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local

/-- The discrete module of actual units with its jointly continuous Galois action. -/
def galoisUnitModule (K S : Type u) [Field K] [Field S] [Algebra K S]
    [Algebra.IsIntegral K S] : Langlands.Continuous.DiscreteModule IntegerScalars.{u} Gal(S/K) where
  toTopRep := discreteUnitsRepresentation K S
  isDiscrete := inferInstance
  continuous_action := continuous_unitAction K S

/-- Mathlib continuous cohomology with actual discrete field units as coefficients. -/
abbrev continuousUnitCohomology (K S : Type u) [Field K] [Field S] [Algebra K S] (n : ℕ) :
    TopModuleCat.{u} IntegerScalars.{u} :=
  continuousCohomology n (discreteUnitsRepresentation K S)

/-- Continuous degree-two cohomology of the Krull group of the separable closure. -/
abbrev separableH2 (K : Type u) [Field K] : TopModuleCat.{u} IntegerScalars.{u} :=
  continuousUnitCohomology K (SeparableClosure K) 2

section Inflation

variable (K L S : Type u) [Field K] [Field L] [Field S]
  [Algebra K L] [Algebra K S] [Algebra L S] [IsScalarTower K L S]
  [Normal K L]

/-- Restriction along an embedding of normal extensions is continuous for the Krull topologies. -/
def normalKrullRestriction : Gal(S/K) →ₜ* Gal(L/K) where
  __ := AlgEquiv.restrictNormalHom L
  continuous_toFun := by
    apply continuous_of_continuousAt_one (AlgEquiv.restrictNormalHom L)
      (continuousAt_def.mpr ?_)
    intro U hU
    rw [map_one, krullTopology_mem_nhds_one_iff] at hU
    obtain ⟨F, hF, hFU⟩ := hU
    let i := IsScalarTower.toAlgHom K L S
    refine (krullTopology_mem_nhds_one_iff K S _).2
      ⟨F.map i, Module.Finite.equiv (F.equivMap i).toLinearEquiv, ?_⟩
    intro σ hσ
    apply hFU
    simp only [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    apply i.injective
    exact (AlgEquiv.restrictNormal_commutes σ L x).trans
      (hσ (i x) ((F.map_mem_map i).mpr hx))

/-- The coefficient component of inflation is the inclusion of the actual units. -/
def continuousUnitInflationCoefficients :
    TopRep.res (normalKrullRestriction K L S) (discreteUnitsRepresentation K L) ⟶
      discreteUnitsRepresentation K S where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear L S
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes σ L x.val }

/-- Continuous inflation from a normal subextension. -/
abbrev continuousUnitInflation (n : ℕ) :
    continuousUnitCohomology K L n ⟶ continuousUnitCohomology K S n :=
  ContinuousCohomology.map (normalKrullRestriction K L S)
    (continuousUnitInflationCoefficients K L S) n

variable [FiniteDimensional K L]

/-- Ordinary finite relative cohomology inflates after the inverse finite-group
comparison with continuous cohomology. -/
def relativeToContinuous (n : ℕ) :
    relativeCohomology K L n →+ continuousUnitCohomology K S n :=
  (continuousUnitInflation K L S n).hom.toAddMonoidHom.comp
    (continuousToRelativeEquiv K L n).symm.toAddMonoidHom

/-- Inflation of a finite continuous class agrees with inflation of its
ordinary class. -/
theorem relativeToContinuous_continuousToRelative (n : ℕ)
    (x : continuousUnitCohomology K L n) :
    relativeToContinuous K L S n (continuousToRelative K L n x) =
      continuousUnitInflation K L S n x := by
  change continuousUnitInflation K L S n
    ((continuousToRelativeEquiv K L n).symm (continuousToRelativeEquiv K L n x)) = _
  rw [AddEquiv.symm_apply_apply]

end Inflation

section Tower

variable (K L M S : Type u) [Field K] [Field L] [Field M] [Field S]
  [Algebra K L] [Algebra K M] [Algebra K S] [Algebra L M] [Algebra M S] [Algebra L S]
  [IsScalarTower K L M] [IsScalarTower K M S] [IsScalarTower K L S] [IsScalarTower L M S]
  [FiniteDimensional K L] [FiniteDimensional K M] [Normal K L] [Normal K M]

omit [FiniteDimensional K L] [FiniteDimensional K M] in
private theorem continuousUnitInflation_tower (n : ℕ) :
    continuousUnitInflation K L M n ≫ continuousUnitInflation K M S n =
      continuousUnitInflation K L S n := by
  rw [continuousUnitInflation, continuousUnitInflation, continuousUnitInflation,
    ← ContinuousCohomology.map_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  apply Langlands.Continuous.continuousCochainsMap_congr
  · apply ContinuousMonoidHom.ext
    intro σ
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M σ).symm
  · intro x
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply L M S x.val).symm

/-- Relative inflation through a larger finite normal stage gives the same
continuous class as direct inflation. -/
theorem relativeToContinuous_tower (n : ℕ) (x : relativeCohomology K L n) :
    relativeToContinuous K M S n (relativeInflation K L M n x) =
      relativeToContinuous K L S n x := by
  obtain ⟨y, rfl⟩ := (continuousToRelativeEquiv K L n).surjective x
  change relativeToContinuous K M S n
      (relativeInflation K L M n (continuousToRelative K L n y)) =
    relativeToContinuous K L S n (continuousToRelative K L n y)
  have h : continuousToRelative K M n (continuousUnitInflation K L M n y) =
      relativeInflation K L M n (continuousToRelative K L n y) :=
    ClosureNaturality.continuousInflation_comparison K L M n y
  rw [← h, relativeToContinuous_continuousToRelative, relativeToContinuous_continuousToRelative]
  exact ConcreteCategory.congr_hom (continuousUnitInflation_tower K L M S n) y

end Tower

end Langlands.BrauerComparison
