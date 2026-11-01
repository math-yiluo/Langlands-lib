import Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement

/-!
# Entire standard-character deformation on the second lower-induced block

A derived transport of the published first-block inverse-character deformation
from JPSS 1983, Section (4.5), printed pages 408-409. Only the second block is
multiplied by `|det|^u`; the family is the actual canonical normalized lower
parabolic induction on the original ordered dependent block carriers.

The closed proposition is stated here, without its proof. Its paired Markdown
explains character change, the parameter `-u`, and the global determinant twist
needed to transport the published theorem. No representation comparison or
analytic family is assumed in the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

section Family

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The original ordered blocks with only the second block twisted by `|det|^u`.
The field and every dependent block carrier keep their original universes. -/
abbrev twoBlockSecondDeformedBlocks
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ) :
    ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i) :=
  fun i => Langlands.twist
    (F.canonicalTopologicalData.determinantComplexPower (m i + 1) (if i = 1 then u else 0))
    (σ i)

/-- The deformed representation `ρ_u`: canonical normalized lower parabolic
induction of the deformed blocks to `GL_(t+1)`. -/
abbrev twoBlockSecondDeformedInduced
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ) :=
  F.canonicalNormalizedOppositeParabolicInduced (succBlockShape m h)
    ((succBlockShape m h).blockTensor (twoBlockSecondDeformedBlocks F m σ u))

/-- At `u = 0` the deformed blocks are the original blocks. -/
theorem twoBlockSecondDeformedBlocks_zero
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) :
    twoBlockSecondDeformedBlocks F m σ 0 = σ := by
  funext i
  simp only [twoBlockSecondDeformedBlocks, ite_self,
    PadicField.TopologicalData.determinantComplexPower_zero, twist_one]

end Family

/-- Derived second-block standard-character form of the published first-block
inverse-character deformation. Every coefficient of every nonzero standard
Whittaker functional at zero extends to actual coefficients at every complex
parameter, with one compact open right level and pointwise entire dependence.
This definition states the assertion; its transport proof is separate. -/
def TwoBlockSecondWhittakerDeformationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (t : ℕ) (m : Fin 2 → ℕ)
      (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∀ (ℓ₀ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ 0)), ℓ₀.val ≠ 0 →
      ∀ v₀, ∃ Wu : ℂ → Langlands.GeneralLinear (t + 1) F.Carrier → ℂ,
        (∀ g, Wu 0 g = ℓ₀.val (twoBlockSecondDeformedInduced F m h σ 0 g v₀)) ∧
        (∀ u : ℂ, ∃ ℓ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u),
          ℓ.val ≠ 0 ∧ ∃ v, ∀ g, Wu u g = ℓ.val (twoBlockSecondDeformedInduced F m h σ u g v)) ∧
        (∃ K : Subgroup (Langlands.GeneralLinear (t + 1) F.Carrier),
          IsOpen (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) ∧
          IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) ∧
          ∀ (u : ℂ) (g : Langlands.GeneralLinear (t + 1) F.Carrier) (k : K),
            Wu u (g * k) = Wu u g) ∧
        ∀ (g : Langlands.GeneralLinear (t + 1) F.Carrier) (u : ℂ),
          AnalyticAt ℂ (fun z => Wu z g) u

end Langlands.RankinSelberg
