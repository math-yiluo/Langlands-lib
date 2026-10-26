import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Entire Whittaker deformation for two lower-induced blocks

The lemma of JPSS 1983, Section (4.5), printed pages 408-409, in its
inverse-character form used on page 409. For `σ_u = Ind(G_t, Q; σ_1 ⊗ α^u, σ_2)`
with `α = |det|`, every Whittaker function of `σ_0` lies in an entire family
`W_u` of Whittaker functions of `σ_u` with one compact open right stabilizer
for all `u`. The family `σ_u` is the actual canonical normalized lower
parabolic induction of the two blocks, the first twisted by
`T.determinantComplexPower (m 0 + 1) u`. This module only states the lemma.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

section Family

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The deformed blocks `σ_u`: the first block is twisted by `|det|^u`, the
second block is unchanged. -/
abbrev twoBlockDeformedBlocks
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ) :
    ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i) :=
  fun i => Langlands.twist
    (F.canonicalTopologicalData.determinantComplexPower (m i + 1) (if i = 0 then u else 0))
    (σ i)

/-- The deformed representation `ρ_u`: canonical normalized lower parabolic
induction of the deformed blocks to `GL_(t+1)`. -/
abbrev twoBlockDeformedInduced
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ) :=
  F.canonicalNormalizedOppositeParabolicInduced (succBlockShape m h)
    ((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u))

/-- At `u = 0` the deformed blocks are the original blocks. -/
theorem twoBlockDeformedBlocks_zero
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) :
    twoBlockDeformedBlocks F m σ 0 = σ := by
  funext i
  simp only [twoBlockDeformedBlocks, ite_self,
    PadicField.TopologicalData.determinantComplexPower_zero, twist_one]

end Family

/-- JPSS 1983, Lemma of Section (4.5), printed pages 408-409, for the inverse
character as applied on page 409. Every coefficient `g ↦ ℓ₀(ρ₀(g) v₀)` of a
nonzero inverse-character Whittaker functional of `ρ₀` is the value at `0` of a
family `W_u` such that each `W_u` is such a coefficient of `ρ_u`, all `W_u` are
right invariant under one compact open subgroup, and `u ↦ W_u(g)` is entire. -/
def TwoBlockWhittakerDeformationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (t : ℕ) (m : Fin 2 → ℕ)
      (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∀ (ℓ₀ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0)), ℓ₀.val ≠ 0 →
      ∀ v₀, ∃ Wu : ℂ → Langlands.GeneralLinear (t + 1) F.Carrier → ℂ,
        (∀ g, Wu 0 g = ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀)) ∧
        (∀ u : ℂ, ∃ ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
          ℓ.val ≠ 0 ∧ ∃ v, ∀ g, Wu u g = ℓ.val (twoBlockDeformedInduced F m h σ u g v)) ∧
        (∃ K : Subgroup (Langlands.GeneralLinear (t + 1) F.Carrier),
          IsOpen (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) ∧
          IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) ∧
          ∀ (u : ℂ) (g : Langlands.GeneralLinear (t + 1) F.Carrier) (k : K),
            Wu u (g * k) = Wu u g) ∧
        ∀ (g : Langlands.GeneralLinear (t + 1) F.Carrier) (u : ℂ),
          AnalyticAt ℂ (fun z => Wu z g) u

end Langlands.RankinSelberg
