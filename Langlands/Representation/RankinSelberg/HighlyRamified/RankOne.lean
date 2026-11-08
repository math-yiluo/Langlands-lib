import Langlands.Representation.RankinSelberg.HighlyRamified.PairInductionGenericity
import Langlands.Representation.RankinSelberg.HighlyRamified.UniverseTransport
import Langlands.Representation.RankinSelberg.UniformRankOneTwistStatement
import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistGamma
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier

/-!
# The rank-one case of gamma stability

This module derives `PairStability r 0`, gamma stability against tests of rank one,
from `UniformRankOneTwistStatement` (Jacquet and Shalika 1985, Proposition (2.2),
level-uniform). A generic test `σ` of `GL_1(F)` is a quasicharacter `η`. A gamma
factor of `(π ⊗ χ ∘ det, η)` is a gamma factor of `(π ⊗ (η χ) ∘ det, 1)`, and
`a(η χ) ≥ a(χ)` once `a(χ) > a(η)`. The statement then gives one common gamma
factor for the two candidates. A test with a vector fixed by `1 + ϖ^m' O` has
`a(η) ≤ m'`, which gives the level-uniform form `UniformPairStability r 0`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- If `a(η) < a(χ)`, then `a(χ) ≤ a(η χ)`: otherwise both `η χ` and `η` are trivial
on the units of level `a(χ) - 1`, and then so is `χ`. -/
theorem le_multiplicativeConductor_mul (F : PadicField.{uF} p)
    (χ η : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (h : F.canonicalTopologicalData.multiplicativeConductor η <
      F.canonicalTopologicalData.multiplicativeConductor χ) :
    F.canonicalTopologicalData.multiplicativeConductor χ ≤
      F.canonicalTopologicalData.multiplicativeConductor (η * χ) := by
  let := F.canonicalTopologicalData.topology
  by_contra hlt
  rw [not_le] at hlt
  have hχ : F.canonicalTopologicalData.MultiplicativeTrivialAt χ
      (F.canonicalTopologicalData.multiplicativeConductor χ - 1) := by
    intro u hu
    have h1 := (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le
      (η * χ) _).mpr (by omega) u hu
    have h2 := (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le
      η _).mpr (by omega) u hu
    have h3 : (η * χ) u = η u * χ u := rfl
    rw [h3, h2, one_mul] at h1
    exact h1
  have := (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le χ _).mp hχ
  omega

/-- A gamma factor of `(π ⊗ χ ∘ det, σ)` for a rank-one test `σ ≃ η` is a gamma factor
of `(π ⊗ (η χ) ∘ det, 1)`: the test character moves to a determinant twist
(`isPadicSymmetricGammaFactor_rankOne_test_twist`), and twists compose. -/
theorem isPadicSymmetricGammaFactor_trivial_of_rankOne_test (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F.Carrier) W)
    (χ η : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (e : σ.Equiv (rankOneCharacter (η : F.Carrierˣ →* ℂˣ)))
    (hπ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π)
    {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor F ψ ν
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ G) :
    IsPadicSymmetricGammaFactor F ψ ν
      (Langlands.twist (((η * χ : letI := F.canonicalTopologicalData.topology
        Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ).comp determinant) π)
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G := by
  let := F.canonicalTopologicalData.topology
  have hW : IsOfWhittakerType r (standardCharacter ψ r)
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
    isOfWhittakerType_of_isGeneric F
      (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ)
  have h0 := (IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl _) e).mp hG
  have h1 := (Padic.isPadicSymmetricGammaFactor_comm F ψ ν _ _ hW
    (rankOneCharacter_isOfWhittakerType p F ψ η) G).mp h0
  have h2 := (isPadicSymmetricGammaFactor_rankOne_test_twist ψ ν η _ (fun _ => hW) G).mpr h1
  rw [twist_twist] at h2
  have hηχ : ((η : F.Carrierˣ →* ℂˣ).comp (determinant (n := r + 1))) *
      ((χ : F.Carrierˣ →* ℂˣ).comp (determinant (n := r + 1))) =
      (((η * χ : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ).comp
        (determinant (n := r + 1))) := rfl
  rw [hηχ] at h2
  exact (Padic.isPadicSymmetricGammaFactor_comm F ψ ν _ _
    (rankOneCharacter_isOfWhittakerType p F ψ 1)
    (isOfWhittakerType_of_isGeneric F
      (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ (η * χ) hπ)) G).mp h2

/-- The rank-one case: `UniformRankOneTwistStatement` gives `PairStability r 0`. Write
the test as a quasicharacter `η` (`rankOneCharacterReduction`). Take the bound `B` of
the statement at the common level of `π₁, π₂`, and `A = max B (a(η) + 1)`. For
`a(χ) ≥ A`, both gamma factors are gamma factors of `(π_i ⊗ (η χ) ∘ det, 1)` with
`a(η χ) ≥ B`, so both equal the common factor. -/
theorem pairStability_rankOne (h : UniformRankOneTwistStatement.{uF, uV}) (r : ℕ) :
    PairStability.{uF, uV, uW} r 0 := by
  intro p _ F ψ ν hψ V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hc
  let := F.canonicalTopologicalData.topology
  have := nontrivial_of_isGeneric F.canonicalTopologicalData ψ hπ₁
  have := nontrivial_of_isGeneric F.canonicalTopologicalData ψ hπ₂
  obtain ⟨m₁, h₁⟩ := exists_hasPrincipalLevelVector F π₁ hπ₁.2.1.1
  obtain ⟨m₂, h₂⟩ := exists_hasPrincipalLevelVector F π₂ hπ₂.2.1.1
  obtain ⟨η, ⟨e⟩⟩ := rankOneCharacterReduction p F ψ W σ (isOfWhittakerType_of_isGeneric F hσ)
  obtain ⟨B, -, hB⟩ := h p F ψ ν hψ r (max m₁ m₂)
  refine ⟨max B (F.canonicalTopologicalData.multiplicativeConductor η + 1),
    fun χ hχ G₁ G₂ hG₁ hG₂ => ?_⟩
  have hηχ := le_multiplicativeConductor_mul F χ η
    (Nat.lt_of_succ_le (le_of_max_le_right hχ))
  obtain ⟨G, hG₁', hG₂'⟩ := hB π₁ π₂ hπ₁ hπ₂ (h₁.mono F π₁ (le_max_left m₁ m₂))
    (h₂.mono F π₂ (le_max_right m₁ m₂)) hc (η * χ) ((le_of_max_le_left hχ).trans hηχ)
  exact ((isPadicSymmetricGammaFactor_trivial_of_rankOne_test F ψ ν.val π₁ σ χ η e hπ₁
    hG₁).unique hG₁').trans
    ((isPadicSymmetricGammaFactor_trivial_of_rankOne_test F ψ ν.val π₂ σ χ η e hπ₂
      hG₂).unique hG₂').symm

/-- A scalar matrix whose entry is a principal unit of level `a` lies in the principal
congruence subgroup `1 + ϖ^a M_(n+1)(O)` (the integral group when `a = 0`). -/
theorem scalar_mem_principalLevelSubgroup (F : PadicField.{uF} p) (n a : ℕ)
    (u : F.Carrierˣ) (hu : u ∈ F.canonicalTopologicalData.principalUnits a) :
    letI := F.canonicalTopologicalData.valuativeRel
    scalar (n := n + 1) u ∈ Conductor.principalLevelSubgroup F.Carrier n a := by
  let := F.canonicalTopologicalData.valuativeRel
  have hv : F.canonicalTopologicalData.discreteValuation (u : F.Carrier) = 1 := hu.1
  have hO : ∀ x : F.Carrier, F.canonicalTopologicalData.discreteValuation x ≤ 1 →
      x ∈ (ValuativeRel.valuation F.Carrier).integer := fun x hx =>
    (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one x).mpr hx
  have hvinv : F.canonicalTopologicalData.discreteValuation
      ((u⁻¹ : F.Carrierˣ) : F.Carrier) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  let U : ((ValuativeRel.valuation F.Carrier).integer)ˣ :=
    ⟨⟨u, hO _ hv.le⟩, ⟨((u⁻¹ : F.Carrierˣ) : F.Carrier), hO _ hvinv.le⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  obtain ⟨y, hy, hyu⟩ : (u : F.Carrier) - 1 ∈
      UnequalRankMirabolicUnitTest.levelSet F.Carrier a := by
    rw [RankOneBox.levelSet_eq_additiveLattice F a]
    exact hu.2
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) U, ?_, ?_⟩
  · rw [SetLike.mem_coe, Conductor.mem_integralPrincipalCongruence]
    intro i j
    by_cases hij : i = j
    · subst hij
      have hy' : (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) U) i i -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) _) i i = y := by
        apply Subtype.ext
        simp [Matrix.scalar_apply, hyu, U]
      rw [hy']
      exact hy
    · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, U, Matrix.GeneralLinearGroup.map]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.GeneralLinearGroup.map]

/-- If a representation of `GL_1(F)` equivalent to `η ∘ det` has a nonzero vector fixed
by `1 + ϖ^m O`, then `a(η) ≤ m`. -/
theorem multiplicativeConductor_le_of_hasPrincipalLevelVector (F : PadicField.{uF} p)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F.Carrier) W)
    (η : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (e : σ.Equiv (rankOneCharacter (η : F.Carrierˣ →* ℂˣ))) {m : ℕ}
    (h : HasPrincipalLevelVector F σ m) :
    F.canonicalTopologicalData.multiplicativeConductor η ≤ m := by
  let := F.canonicalTopologicalData.valuativeRel
  apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le η m).mp
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro u hu
  have hfix : σ (scalar (n := 0 + 1) u) v = v := by
    simp only [Langlands.fixedVectors, Representation.mem_invariants] at hv
    exact hv ⟨_, scalar_mem_principalLevelSubgroup F 0 m u hu⟩
  have h1 := Representation.IntertwiningMap.isIntertwining σ _ e.toIntertwiningMap
    (scalar (n := 0 + 1) u) v
  rw [hfix] at h1
  have hdet : determinant (scalar (n := 0 + 1) u) = u := by
    ext
    simp [determinant]
  have hne : e v ≠ 0 := by
    intro h0
    exact hv0 (e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm))
  have h2 : ((η u : ℂˣ) : ℂ) • e v = (1 : ℂ) • e v := by
    rw [one_smul]
    have h3 : (rankOneCharacter (η : F.Carrierˣ →* ℂˣ)) (scalar (n := 0 + 1) u) (e v) =
        ((η u : ℂˣ) : ℂ) • e v := by
      simp [rankOneCharacter, Langlands.characterRepresentation, Langlands.twist, hdet]
    rw [← h3]
    exact h1.symm
  exact Units.ext (smul_left_injective ℂ hne h2)

/-- The uniform rank-one case: `UniformRankOneTwistStatement` gives
`UniformPairStability r 0`. A test of rank one with a level-`m'` vector is `η ∘ det` with
`a(η) ≤ m'`, so `A = max B (m' + 1)` works, where `B` is the bound of the statement at
rank `r + 1` and level `m`. -/
theorem uniformPairStability_rankOne (h : UniformRankOneTwistStatement.{uF, uV}) (r : ℕ) :
    UniformPairStability.{uF, uV, uW} r 0 := by
  intro p _ F ψ ν hψ m m'
  obtain ⟨B, -, hB⟩ := h p F ψ ν hψ r m
  refine ⟨max B (m' + 1), ?_⟩
  intro V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ h₁ h₂ hσm hc χ hχ G₁ G₂ hG₁ hG₂
  let := F.canonicalTopologicalData.topology
  obtain ⟨η, ⟨e⟩⟩ := rankOneCharacterReduction p F ψ W σ (isOfWhittakerType_of_isGeneric F hσ)
  have hη := multiplicativeConductor_le_of_hasPrincipalLevelVector F σ η e hσm
  have hηχ := le_multiplicativeConductor_mul F χ η
    (lt_of_le_of_lt hη (Nat.lt_of_succ_le (le_of_max_le_right hχ)))
  obtain ⟨G, hG₁', hG₂'⟩ := hB π₁ π₂ hπ₁ hπ₂ h₁ h₂ hc (η * χ) ((le_of_max_le_left hχ).trans hηχ)
  exact ((isPadicSymmetricGammaFactor_trivial_of_rankOne_test F ψ ν.val π₁ σ χ η e hπ₁
    hG₁).unique hG₁').trans
    ((isPadicSymmetricGammaFactor_trivial_of_rankOne_test F ψ ν.val π₂ σ χ η e hπ₂
      hG₂).unique hG₂').symm

/-- `HighlyRamifiedGammaStabilityStatement` follows from the adjacent case
`∀ n, PairStability (n + 1) n` at universes `(uV, uW)`, `(max uF uV, uW)` and
`(uV, max uF uW)`, and `UniformRankOneTwistStatement`. -/
theorem highlyRamifiedGammaStability_of_adjacent_and_uniformRankOne
    (hadj : ∀ n, PairStability.{uF, uV, uW} (n + 1) n)
    (hadjV : ∀ n, PairStability.{uF, max uF uV, uW} (n + 1) n)
    (hadjW : ∀ n, PairStability.{uF, uV, max uF uW} (n + 1) n)
    (hone : UniformRankOneTwistStatement.{uF, uV}) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_adjacent_and_rankOne hadj hadjV hadjW
    (fun r => pairStability_rankOne hone r) (fun r => pairStability_rankOne hone r)

/-- `HighlyRamifiedGammaStabilityStatement` follows from the uniform adjacent case
`∀ n, UniformPairStability (n + 1) n` with both spaces in the universe `max uF uV uW`,
and `UniformRankOneTwistStatement`. Uniform stability implies stability
(`pairStability_of_uniformPairStability`), and `pairStability_of_common` moves it to the
three universe pairs used by the rank reduction. -/
theorem highlyRamifiedGammaStability_of_uniformAdjacent_and_uniformRankOne
    (hadj : ∀ n, UniformPairStability.{uF, max uF uV uW, max uF uV uW} (n + 1) n)
    (hone : UniformRankOneTwistStatement.{uF, uV}) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_adjacent_and_uniformRankOne
    (fun n => pairStability_of_common (pairStability_of_uniformPairStability (hadj n)))
    (fun n => pairStability_of_common.{uF, max uF uV, uW}
      (pairStability_of_uniformPairStability (hadj n)))
    (fun n => pairStability_of_common.{uF, uV, max uF uW}
      (pairStability_of_uniformPairStability (hadj n)))
    hone

end Langlands.RankinSelberg.HighlyRamified
