import Langlands.Representation.RankinSelberg.MultiplicativityStatement

/-!
# Whittaker completeness against normalized products of supercuspidals

Henniart 1993, Lemma 2.1 (printed page 342), quoting Jacquet–Shalika 1985,
Lemma 3.2: a smooth function `H` on `GL_(n+1)(F)` with `H(ug) = ψ(u) H(g)` on the
upper unipotent subgroup `N`, compactly supported modulo `N`, and orthogonal on
`N \ GL_(n+1)(F)` to the Whittaker functions of every irreducible generic
representation vanishes. This module states the variant whose test
representations are the normalized upper block inductions of irreducible
supercuspidal representations, with all their inverse-character Whittaker
functionals. These proposition definitions do not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uW

section Pairing

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The product `H(g) f(g)` of a standard-character function and an
inverse-character function, descended to the left quotient `N \ GL_(n+1)`. -/
def whittakerProductIntegrand (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (H : WhittakerFunctions ψ n) (f : InverseWhittakerFunctions ψ n) :
    LeftUnipotentQuotient n F → ℂ :=
  QuotientIntegration.descend _ (fun g => H.val g * f.val g)
    (whittaker_product_invariant ψ H f)

@[simp] theorem whittakerProductIntegrand_mk (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (H : WhittakerFunctions ψ n) (f : InverseWhittakerFunctions ψ n)
    (g : Langlands.GeneralLinear (n + 1) F) :
    whittakerProductIntegrand ψ H f (Quotient.mk _ g) = H.val g * f.val g := rfl

/-- A standard-character function is a compact Whittaker test function when it
is invariant under right translation by an open subgroup and is supported in
`N C` for a compact set `C`. -/
def IsCompactWhittakerTestFunction (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (H : WhittakerFunctions ψ n) : Prop :=
  (∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
    ∀ g k : Langlands.GeneralLinear (n + 1) F, k ∈ K → H.val (g * k) = H.val g) ∧
  (∃ C : Set (Langlands.GeneralLinear (n + 1) F), IsCompact C ∧
    ∀ g : Langlands.GeneralLinear (n + 1) F, H.val g ≠ 0 →
      ∃ (u : upperUnipotent (n + 1) F) (c : Langlands.GeneralLinear (n + 1) F),
        c ∈ C ∧ g = u.val * c)

end Pairing

/-- Whittaker completeness against normalized products of supercuspidals, for
every p-adic field with its canonical topology, every unitary additive
character `ψ` and every rank `n + 1`. Let `μ` be a compatible quotient measure on
`N \ GL_(n+1)(F)`. Let `H` be a compact Whittaker test function for `ψ`. Assume
that `∫ H(g) f(g) dμ(g) = 0` for every block shape `(m_1 + 1, …, m_k + 1)` of
`n + 1`, all smooth irreducible supercuspidal representations `τ_i` of
`GL_(m_i + 1)(F)` on carriers in universe `uW`, every inverse-character
Whittaker functional `ℓ'` of their normalized induction
`canonicalNormalizedProductInduced`, and every `f` in the coefficient model of
`ℓ'`. Then `H = 0`. -/
def SupercuspidalProductCompletenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ →
      ∀ H : WhittakerFunctions ψ n, IsCompactWhittakerTestFunction ψ n H →
        (∀ (k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = n + 1)
          (W : Fin k → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
          (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
          (∀ i, IsSmooth (τ i)) → (∀ i, Representation.IsIrreducible (τ i)) →
          (∀ i, GeneralLinear.IsSupercuspidal (τ i)) →
          ∀ (ℓ' : glInverseFunctionals ψ n
              (F.canonicalNormalizedProductInduced (succBlockShape m h) τ))
            (f : (coefficientModel _ ℓ').toSubmodule),
            ∫ q, whittakerProductIntegrand ψ H f.val q ∂μ = 0) →
        H = 0

end Langlands.RankinSelberg
