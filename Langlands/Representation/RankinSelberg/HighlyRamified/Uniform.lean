import Langlands.Representation.RankinSelberg.UniformRankOneTwistStatement
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof

/-!
# Level-uniform stability of pair gamma factors

The induction behind Jacquet–Shalika 1985, Proposition 4.1, needs twisting bounds
that depend only on the ranks and on a principal-congruence level of the
representations. The level predicate is the published `HasPrincipalLevelVector`.
This module proves its two basic properties and defines the uniform stability
proposition for one pair of ranks.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section Level

variable (F : PadicField.{uF} p) {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)

/-- A level vector is also a vector of every deeper level. -/
theorem _root_.Langlands.RankinSelberg.HasPrincipalLevelVector.mono {m m' : ℕ} (hm : m ≤ m')
    (h : HasPrincipalLevelVector F π m) : HasPrincipalLevelVector F π m' := by
  let := F.canonicalTopologicalData.valuativeRel
  intro hbot
  apply h
  rw [eq_bot_iff] at hbot ⊢
  intro v hv
  apply hbot
  simp only [Langlands.fixedVectors, Representation.mem_invariants] at hv ⊢
  intro g
  exact hv ⟨g.val, Conductor.principalLevelSubgroup_antitone F.Carrier r hm g.property⟩

/-- A smooth representation on a nontrivial space has a level vector. -/
theorem exists_hasPrincipalLevelVector
    (hπ : (letI := F.canonicalTopologicalData.topology; IsSmooth π)) [Nontrivial V] :
    ∃ m, HasPrincipalLevelVector F π m := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hK⟩ := hπ v
  obtain ⟨a, -, ha⟩ := Conductor.principalLevelCofinal F.Carrier r (K : Set _)
    (K.isOpen.mem_nhds K.one_mem)
  refine ⟨a, fun hbot => hv ?_⟩
  have hmem : v ∈ Langlands.fixedVectors π (Conductor.principalLevelSubgroup F.Carrier r a) := by
    simp only [Langlands.fixedVectors, Representation.mem_invariants] at hK ⊢
    intro g
    exact hK ⟨g.val, ha g.property⟩
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end Level

/-- Uniform stability for candidates of rank `r + 1` and tests of rank `t + 1`: for all
levels `m, m'` there is one bound `A` such that, for every quasicharacter `χ` with
conductor exponent at least `A`, any two gamma certificates of the twists by `χ ∘ det`
of two generic candidates with level-`m` vectors and the same central character, against
any generic test with a level-`m'` vector, agree. The additive character has conductor
exponent `0` and the Haar measure is self-dual. -/
def UniformPairStability (r t : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ m m' : ℕ, ∃ A : ℕ,
      ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
        (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
        (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁) →
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂) →
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ) →
        HasPrincipalLevelVector F π₁ m → HasPrincipalLevelVector F π₂ m →
          HasPrincipalLevelVector F σ m' →
        SameGLCentralCharacter F π₁ π₂ →
        ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
          A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
          ∀ G₁ G₂ : RationalFunctions,
            IsPadicSymmetricGammaFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G₁ →
            IsPadicSymmetricGammaFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G₂ →
            G₁ = G₂

end Langlands.RankinSelberg.HighlyRamified
