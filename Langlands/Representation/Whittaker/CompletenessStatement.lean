import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessStatement
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Completeness of Whittaker functions

Jacquet and Shalika 1985, Lemma (3.2) (printed page 325): a smooth function on
`GL_r(F)`, left equivariant under `N_r` for the inverse standard character and
compactly supported modulo `N_r`, whose integral against every Whittaker function of
every irreducible admissible generic representation vanishes, is zero. Its proof is
that of Jacquet, Piatetski-Shapiro and Shalika 1981, Lemme (3.5) (printed page 207).
This module only defines the proposition.
-/

noncomputable section

namespace Langlands.Whittaker

open MeasureTheory HarmonicAnalysis GeneralLinear RankinSelberg QuotientIntegration

universe uF uV

/-- Jacquet and Shalika 1985, Lemma (3.2) (printed page 325), over every p-adic
field with its canonical structures. Let `ψ` be a nontrivial unitary additive
character and `H` a function on `GL_(n+1)(F)` with `H(u g) = ψ_N(u)⁻¹ H(g)` for
upper unitriangular `u`, right invariant under an open subgroup, and supported in
`N_(n+1) C` for a compact set `C`. If, for the canonical quotient measure on
`N_(n+1) \ GL_(n+1)`, the integral of `W H` vanishes for every vector `W` of every
Whittaker model of every irreducible admissible generic representation, then `H`
vanishes identically. -/
def WhittakerCompletenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ),
      letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
      haveI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F.Carrier)
      haveI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      haveI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
      ∀ H : InverseWhittakerFunctions ψ n,
        (∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
          ∀ g k, k ∈ K → H.val (g * k) = H.val g) →
        (∃ C : Set (Langlands.GeneralLinear (n + 1) F.Carrier), IsCompact C ∧
          ∀ g, H.val g ≠ 0 → ∃ u : upperUnipotent (n + 1) F.Carrier, ∃ c ∈ C, g = u.val * c) →
        (∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
          IsGeneric ψ n π →
          ∀ (ℓ : glFunctionals ψ n π) (w : (coefficientModel π ℓ).toSubmodule),
            ∫ x, whittakerProductIntegrand ψ w.val H x ∂unipotentQuotientHaar F.Carrier n = 0) →
        ∀ g, H.val g = 0

end Langlands.Whittaker
