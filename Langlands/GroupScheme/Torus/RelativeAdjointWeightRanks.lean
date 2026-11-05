import Langlands.GroupScheme.Torus.RelativeAdjointWeights
import Langlands.GroupScheme.Lie.SmoothFiniteProjective
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Locally constant ranks of actual relative adjoint weight summands -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.splitTorus

attribute [local instance] Module.finitePresentation_of_projective

variable {R : CommRingCat.{u}} (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : splitTorus (Spec R) I ⟶ G)

/-- Each actual exponent weight space is finite, as a retract of the actual
finite Lie module. -/
instance finite_exponentWeightSpace (m : I → ℤ) :
    Module.Finite R (exponentWeightSpace I G i m) :=
  Module.Finite.of_surjective (exponentProjection I G i m)
    (fun X => ⟨X, exponentProjection_subtype I G i m X⟩)

/-- Each actual exponent weight space is projective, as a direct summand of
the actual projective Lie module. -/
instance projective_exponentWeightSpace (m : I → ℤ) :
    Module.Projective R (exponentWeightSpace I G i m) :=
  Module.Projective.of_split (exponentWeightSpace I G i m).subtype
    (exponentProjection I G i m) (exponentProjection_comp_subtype I G i m)

/-- There are only finitely many nonzero integral-exponent weight summands
in the actual smooth affine Lie module over the whole ring. -/
theorem exists_finset_exponentWeightSpace_eq_bot :
    ∃ s : Finset (I → ℤ), ∀ m ∉ s, exponentWeightSpace I G i m = ⊥ := by
  classical
  obtain ⟨p, hp⟩ := (LinearMap.finsuppLinearMap_bijective_of_moduleFinite
    (S := R) (R := R) (M := Additive (lieKernel G R))
    (N := Additive (lieKernel G R)) (ι := I → ℤ)).2
      (universalAdjointCoefficients I G i)
  refine ⟨p.support, fun m hm => ?_⟩
  have hpm : p m = 0 := Finsupp.notMem_support_iff.mp hm
  apply le_antisymm ?_ bot_le
  intro X hX
  change X = 0
  have h := congrArg (fun q : Additive (lieKernel G R) →ₗ[R]
      (I → ℤ) →₀ Additive (lieKernel G R) => q X m) hp
  have hdiag := universalAdjointCoefficients_of_mem_exponentWeightSpace I G i m X hX
  simpa [LinearMap.finsuppLinearMap, hpm, hdiag] using h.symm

/-- The rank of an actual exponent weight summand at each prime of the base ring. -/
def exponentWeightRank (m : I → ℤ) : PrimeSpectrum R → ℕ :=
  Module.rankAtStalk (R := R) (exponentWeightSpace I G i m)

/-- Each actual exponent weight rank is locally constant on the arbitrary base. -/
theorem isLocallyConstant_exponentWeightRank (m : I → ℤ) :
    IsLocallyConstant (exponentWeightRank I G i m) :=
  Module.isLocallyConstant_rankAtStalk

/-- The simultaneous ranks of all the actual adjoint exponent weight summands. -/
def exponentWeightRankProfile (p : PrimeSpectrum R) : (I → ℤ) → ℕ :=
  fun m => exponentWeightRank I G i m p

/-- One open neighbourhood makes all actual adjoint weight-summand ranks
constant simultaneously. -/
theorem exists_open_exponentWeightRanks_eq (p : PrimeSpectrum R) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, ∀ m, exponentWeightRank I G i m q = exponentWeightRank I G i m p := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_exponentWeightSpace_eq_bot I G i
  let U : Set (PrimeSpectrum R) :=
    ⋂ m : s, {q | exponentWeightRank I G i m q = exponentWeightRank I G i m p}
  refine ⟨U, isOpen_iInter_of_finite (fun m =>
    (isLocallyConstant_exponentWeightRank I G i m).isOpen_fiber _),
    Set.mem_iInter.mpr (fun _ => rfl), ?_⟩
  intro q hq m
  by_cases hm : m ∈ s
  · exact Set.mem_iInter.mp hq ⟨m, hm⟩
  · let : Subsingleton (exponentWeightSpace I G i m) :=
      Submodule.subsingleton_iff_eq_bot.mpr (hs m hm)
    simp only [exponentWeightRank, Module.rankAtStalk_eq_zero_of_subsingleton, Pi.zero_apply]

/-- The full actual adjoint weight-rank profile is locally constant. -/
theorem isLocallyConstant_exponentWeightRankProfile :
    IsLocallyConstant (exponentWeightRankProfile I G i) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro p
  obtain ⟨U, hU, hpU, hconst⟩ := exists_open_exponentWeightRanks_eq I G i p
  exact ⟨U, hU, hpU, fun q hq => funext (hconst q hq)⟩

end Langlands.GroupScheme.splitTorus
