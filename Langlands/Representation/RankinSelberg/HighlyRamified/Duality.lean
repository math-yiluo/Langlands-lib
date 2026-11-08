import Langlands.Representation.RankinSelberg.HighlyRamified.Uniform
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.LocalFactor.Abelian.Scaling
import Langlands.LocalFactor.Abelian.UnramifiedTwist

/-!
# Inverse transpose and the inverse additive character

The dual side of a functional equation uses `inverseTransposePullback π` and the
character `ψ.scale (-1)`. This module shows that the hypotheses of
`UniformRankOneTwistStatement` pass to that side: genericity, principal level vectors,
conductor exponent `0` of the additive character, self-duality of the measure, and the
conductor exponent of the twisting character.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- The inverse transpose of a generic representation is generic for `ψ⁻¹`. -/
theorem isGeneric_inverseTransposePullback (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n π) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    Whittaker.IsGeneric (ψ.scale (-1)) n (inverseTransposePullback π) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  refine ⟨(CuspidalSupport.isIrreducible_comp_mulEquiv_iff π
      (inverseTranspose (n + 1) F.Carrier)).mpr hπ.1,
    isAdmissible_comp_continuousMulEquiv π (inverseTransposeContinuous (n + 1) F.Carrier)
      hπ.2.1, ?_⟩
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  have hne : dualFunctionalEquiv π ψ ℓ ≠ 0 := by
    intro h0
    apply hℓ
    have h1 : ℓ = 0 := (dualFunctionalEquiv π ψ).map_eq_zero_iff.mp h0
    exact congrArg Subtype.val h1
  change HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
    (θ := standardCharacter (ψ.scale (-1)) n) (inverseTransposePullback π)
  rw [standardCharacter_scale_neg_one]
  exact ⟨dualFunctionalEquiv π ψ ℓ, fun h0 => hne (Subtype.ext h0)⟩

/-- Inverse transpose maps the principal congruence subgroup `1 + ϖ^m M(O)` to itself. -/
theorem inverseTranspose_mem_principalLevelSubgroup (F : PadicField.{uF} p) {r m : ℕ}
    {g : Langlands.GeneralLinear (r + 1) F.Carrier}
    (hg : letI := F.canonicalTopologicalData.valuativeRel
      g ∈ Conductor.principalLevelSubgroup F.Carrier r m) :
    letI := F.canonicalTopologicalData.valuativeRel
    inverseTranspose (r + 1) F.Carrier g ∈ Conductor.principalLevelSubgroup F.Carrier r m := by
  let := F.canonicalTopologicalData.valuativeRel
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨inverseTranspose (r + 1) _ h, ?_, ?_⟩
  · have hinv := (Conductor.integralPrincipalCongruence r _).inv_mem hh
    rw [Conductor.mem_integralPrincipalCongruence] at hinv
    rw [SetLike.mem_coe, Conductor.mem_integralPrincipalCongruence]
    intro i j
    have := hinv j i
    simpa [inverseTranspose, Matrix.one_apply, eq_comm] using this
  · apply Units.ext
    ext i j
    rfl

/-- A principal level vector of `π` is one of `inverseTransposePullback π`. -/
theorem hasPrincipalLevelVector_inverseTransposePullback (F : PadicField.{uF} p) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V) {m : ℕ}
    (h : HasPrincipalLevelVector F π m) :
    HasPrincipalLevelVector F (inverseTransposePullback π) m := by
  let := F.canonicalTopologicalData.valuativeRel
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [HasPrincipalLevelVector, Submodule.ne_bot_iff]
  refine ⟨v, ?_, hv0⟩
  simp only [Langlands.fixedVectors, Representation.mem_invariants] at hv ⊢
  intro g
  exact hv ⟨_, inverseTranspose_mem_principalLevelSubgroup F g.property⟩

/-- `ψ⁻¹` has the same conductor exponent as `ψ`. -/
theorem additiveConductor_scale_neg_one (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    F.canonicalTopologicalData.additiveConductor (ψ.scale (-1)) =
      F.canonicalTopologicalData.additiveConductor ψ := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  rw [F.canonicalTopologicalData.additiveConductor_scale]
  simp [PadicField.TopologicalData.ord]

/-- The inverse of a quasicharacter has the same conductor exponent. -/
theorem multiplicativeConductor_inv (F : PadicField.{uF} p)
    (η : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    F.canonicalTopologicalData.multiplicativeConductor η⁻¹ =
      F.canonicalTopologicalData.multiplicativeConductor η := by
  have key : ∀ (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
      (k : ℕ), F.canonicalTopologicalData.MultiplicativeTrivialAt χ k →
        F.canonicalTopologicalData.MultiplicativeTrivialAt χ⁻¹ k := by
    intro χ k h u hu
    change (χ u)⁻¹ = 1
    rw [h u hu, inv_one]
  apply le_antisymm
  · exact (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ _).mp
      (key η _ (F.canonicalTopologicalData.multiplicativeConductor_spec η))
  · apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ _).mp
    intro u hu
    have h := F.canonicalTopologicalData.multiplicativeConductor_spec η⁻¹ u hu
    change (η u)⁻¹ = 1 at h
    exact inv_eq_one.mp h

/-- Inverse transpose turns the twist by `χ ∘ det` into the twist by `χ⁻¹ ∘ det`. -/
def inverseTransposePullbackTwistEquiv (F : PadicField.{uF} p) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : F.Carrierˣ →* ℂˣ) :
    (inverseTransposePullback (Langlands.twist (χ.comp determinant) π)).Equiv
      (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback π)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
    ext v
    change (χ (determinant (inverseTranspose (r + 1) F.Carrier g)) : ℂ) •
        π (inverseTranspose (r + 1) F.Carrier g) v =
      ((χ⁻¹ (determinant g) : ℂˣ) : ℂ) • π (inverseTranspose (r + 1) F.Carrier g) v
    rw [RankOneGammaTwist.determinant_inverseTranspose, map_inv]
    rfl

/-- Inverse transpose fixes the trivial character of `GL_1`. -/
def inverseTransposePullbackTrivialEquiv (F : PadicField.{uF} p) :
    (inverseTransposePullback (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))).Equiv
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) fun g => by
    apply LinearMap.ext
    intro v
    change ((1 : F.Carrierˣ →* ℂˣ) (determinant (inverseTranspose 1 F.Carrier g)) : ℂ) • v =
      ((1 : F.Carrierˣ →* ℂˣ) (determinant g) : ℂ) • v
    simp

end Langlands.RankinSelberg.HighlyRamified
