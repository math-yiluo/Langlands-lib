import Langlands.Representation.RankinSelberg.HighlyRamifiedStatement
import Langlands.Representation.Conductor.PrincipalCongruence

/-!
# Rank-one factors after highly ramified twists, uniformly in the level

Jacquet and Shalika 1985, Proposition (2.2) (printed page 320), for the factors of a
pair with the trivial character of `GL_1`, with a twisting bound that depends only on
the rank and on a principal-congruence level at which the representation has a
nonzero fixed vector. The uniformity is read off from the proof in §§2.3–2.7
(printed pages 320–323). This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- `π` has a nonzero vector fixed by the principal congruence subgroup
`1 + ϖ^m M_(r+1)(O)` of `GL_(r+1)(F)` for positive `m`; at `m = 0`
the subgroup is the full integral group `GL_(r+1)(O)`. -/
def HasPrincipalLevelVector (F : PadicField.{uF} p) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V) (m : ℕ) : Prop :=
  letI := F.canonicalTopologicalData.valuativeRel
  Langlands.fixedVectors π (Conductor.principalLevelSubgroup F.Carrier r m) ≠ ⊥

/-- Uniform form of Jacquet and Shalika 1985, Proposition (2.2), against the trivial
character of `GL_1`. Let `ψ` have conductor exponent `0` and `ν` be self-dual. For every
rank `r + 1` and level `m` there is `B` such that for every quasicharacter `χ` with
conductor exponent `a ≥ B`, uniformly over the representations:

* every irreducible admissible generic `π` with a nonzero `1 + ϖ^m M(O)`-fixed vector
  satisfies `L(s, (π ⊗ χ ∘ det) × 1) = 1` and `ε(s, (π ⊗ χ ∘ det) × 1, ψ) = c q^(-(r+1)a s)`
  for some `c : ℂˣ`;
* two such representations with the same central character have one common gamma
  factor `γ(s, (π_i ⊗ χ ∘ det) × 1, ψ)`. -/
def UniformRankOneTwistStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ (r m : ℕ), ∃ B : ℕ,
      (∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V),
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π) →
        HasPrincipalLevelVector F π m →
        ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
          B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
          IsPadicSymmetricLPolynomial F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1 ∧
            ∃ c : ℂˣ, IsPadicSymmetricEpsilonFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
              (c, (((r + 1) * F.canonicalTopologicalData.multiplicativeConductor χ : ℕ) : ℤ))) ∧
      (∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
        (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
        (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂),
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁) →
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂) →
        HasPrincipalLevelVector F π₁ m → HasPrincipalLevelVector F π₂ m →
        SameGLCentralCharacter F π₁ π₂ →
        ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
          B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
          ∃ G : RationalFunctions,
            IsPadicSymmetricGammaFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G ∧
            IsPadicSymmetricGammaFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G)

end Langlands.RankinSelberg
