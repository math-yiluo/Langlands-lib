import Langlands.Algebra.BrauerComparison.SeparableCohomology
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # Restriction on continuous unit cohomology -/

noncomputable section

open CategoryTheory

universe u

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local

section Krull

variable (K E T : Type u) [Field K] [Field E] [Field T]
  [Algebra K E] [Algebra K T] [Algebra E T] [IsScalarTower K E T]
  [Algebra.IsAlgebraic E T]

/-- Restricting scalars on automorphisms is continuous for the two Krull topologies. -/
def krullRestrictScalars : Gal(T/E) →ₜ* Gal(T/K) where
  __ := AlgEquiv.restrictScalarsHom K
  continuous_toFun := by
    apply continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom K)
      (continuousAt_def.mpr ?_)
    intro V hV
    rw [map_one, krullTopology_mem_nhds_one_iff] at hV
    obtain ⟨F, hF, hFV⟩ := hV
    have _ : FiniteDimensional K F := hF
    obtain ⟨s, hs⟩ := (IntermediateField.essFiniteType_iff (K := F)).mp inferInstance
    let M := IntermediateField.adjoin E (s : Set T)
    have hM : FiniteDimensional E M :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    refine (krullTopology_mem_nhds_one_iff E T _).mpr ⟨M, hM, ?_⟩
    intro σ hσ
    apply hFV
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hs]
    apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff K (σ.restrictScalars K)).mpr
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff M σ).mp hσ x
      (IntermediateField.subset_adjoin E _ hx)

end Krull

section Restriction

variable (K E S T : Type u) [Field K] [Field E] [Field S] [Field T]
  [Algebra K E] [Algebra K S] [Algebra E T] [Algebra K T] [Algebra S T]
  [IsScalarTower K E T] [IsScalarTower K S T] [Normal K S] [Algebra.IsAlgebraic E T]

/-- The induced homomorphism given by restricting base scalars and then restricting to `S`. -/
abbrev krullRestriction : Gal(T/E) →ₜ* Gal(S/K) :=
  (normalKrullRestriction K S T).comp (krullRestrictScalars K E T)

/-- The actual inclusion of units is equivariant for restriction of automorphisms. -/
def continuousUnitRestrictionCoefficients :
    TopRep.res (krullRestriction K E S T) (discreteUnitsRepresentation K S) ⟶
      discreteUnitsRepresentation E T where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear S T
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) S x.val }

/-- Cohomological restriction along the compatible base-field and coefficient embeddings. -/
abbrev continuousUnitRestriction (n : ℕ) :
    continuousUnitCohomology K S n ⟶ continuousUnitCohomology E T n :=
  ContinuousCohomology.map (krullRestriction K E S T)
    (continuousUnitRestrictionCoefficients K E S T) n

variable (L M : Type u) [Field L] [Field M]
  [Algebra K L] [Algebra L S] [Algebra K M] [Algebra E M] [Algebra L M] [Algebra M T]
  [IsScalarTower K L S] [IsScalarTower K E M] [IsScalarTower K L M] [IsScalarTower E M T]
  [Normal K L] [Normal E M] [FiniteDimensional K L] [FiniteDimensional E M]
  (hcompat : ∀ a : L, algebraMap M T (algebraMap L M a) = algebraMap S T (algebraMap L S a))

include hcompat

omit [FiniteDimensional K L] in
private theorem krullRestriction_stages :
    (normalKrullRestriction K L S).comp (krullRestriction K E S T) =
      (ClosureNaturality.mixedRestriction K E L M).comp (normalKrullRestriction E M T) := by
  apply ContinuousMonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro a
  change ((σ.restrictScalars K).restrictNormal S).restrictNormal L a =
    ((σ.restrictNormal M).restrictScalars K).restrictNormal L a
  apply (algebraMap L S).injective
  apply (algebraMap S T).injective
  calc
    _ = σ (algebraMap S T (algebraMap L S a)) :=
      (congrArg (algebraMap S T) (AlgEquiv.restrictNormal_commutes
        ((σ.restrictScalars K).restrictNormal S) L a)).trans
        (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) S (algebraMap L S a))
    _ = σ (algebraMap M T (algebraMap L M a)) := congrArg σ (hcompat a).symm
    _ = algebraMap M T
          (algebraMap L M (((σ.restrictNormal M).restrictScalars K).restrictNormal L a)) :=
      (AlgEquiv.restrictNormal_commutes σ M (algebraMap L M a)).symm.trans
        (congrArg (algebraMap M T)
          (AlgEquiv.restrictNormal_commutes ((σ.restrictNormal M).restrictScalars K) L a).symm)
    _ = _ := hcompat _

omit [FiniteDimensional K L] in
private theorem continuousUnitRestriction_inflation (n : ℕ) :
    continuousUnitInflation K L S n ≫ continuousUnitRestriction K E S T n =
      ClosureNaturality.mixedContinuousMap K E L M n ≫ continuousUnitInflation E M T n := by
  rw [continuousUnitInflation, continuousUnitRestriction, ClosureNaturality.mixedContinuousMap,
    continuousUnitInflation, ← ContinuousCohomology.map_comp, ← ContinuousCohomology.map_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  apply Langlands.Continuous.continuousCochainsMap_congr
    (krullRestriction_stages K E S T L M hcompat)
  intro x
  apply Units.ext
  exact (hcompat x.val).symm

/-- The restriction of an inflated relative class is computed by finite-stage
inflation and restriction, for any compatible stages in the two closures. -/
theorem relativeToContinuous_restriction (n : ℕ) (x : relativeCohomology K L n) :
    continuousUnitRestriction K E S T n (relativeToContinuous K L S n x) =
      relativeToContinuous E M T n (relativeRestriction K E M n (relativeInflation K L M n x)) := by
  obtain ⟨y, rfl⟩ := (continuousToRelativeEquiv K L n).surjective x
  change continuousUnitRestriction K E S T n
      (relativeToContinuous K L S n (continuousToRelative K L n y)) =
    relativeToContinuous E M T n
      (relativeRestriction K E M n (relativeInflation K L M n (continuousToRelative K L n y)))
  rw [← ClosureNaturality.mixedContinuousMap_comparison,
    relativeToContinuous_continuousToRelative, relativeToContinuous_continuousToRelative]
  exact ConcreteCategory.congr_hom (continuousUnitRestriction_inflation K E S T L M hcompat n) y

end Restriction

section Containment

variable {K E L T : Type u} [Field K] [Field E] [Field L] [Field T]
  [Algebra K E] [Algebra K L] [Algebra E T] [Algebra K T] [IsScalarTower K E T]
  [FiniteDimensional K L] [IsGalois E T]

/-- A specified embedding of a finite field is contained in a finite Galois
stage over the new base. -/
theorem exists_finiteStage_containing (i : L →ₐ[K] T) :
    ∃ (M : FiniteGaloisIntermediateField E T) (j : L →ₐ[K] M), ∀ a : L, (j a : T) = i a := by
  let F := i.fieldRange
  have _ : FiniteDimensional K F := Module.Finite.equiv (AlgEquiv.ofInjective i i.injective).toLinearEquiv
  obtain ⟨s, hs⟩ := (IntermediateField.essFiniteType_iff (K := F)).mp inferInstance
  let M := FiniteGaloisIntermediateField.adjoin E (s : Set T)
  have hFM : F ≤ M.toIntermediateField.restrictScalars K := by
    rw [← hs, IntermediateField.adjoin_le_iff]
    exact FiniteGaloisIntermediateField.subset_adjoin E (s : Set T)
  refine ⟨M, (IntermediateField.inclusion hFM).comp (AlgEquiv.ofInjective i i.injective).toAlgHom,
    fun _ => rfl⟩

end Containment

end Langlands.BrauerComparison
