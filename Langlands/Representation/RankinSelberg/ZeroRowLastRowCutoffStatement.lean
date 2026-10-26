import Langlands.LocalField.Definitions
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Compact last-row cutoff for smooth zero-row Whittaker coefficients

This proposition isolates the compact-support input to JPSS Section 8.3.
The smooth coefficient-image scope and the zero-or-one cutoff are a derived
internal formulation, as explained in the paired Markdown.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- Every coefficient in a smooth Whittaker coefficient image admits a
zero-or-one Schwartz–Bruhat cutoff on the last row that leaves its zero-row
restriction unchanged. This is a closed proposition definition, not a proof. -/
def ZeroRowLastRowCutoffStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n k : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.valuativeExtension
  letI := T.moduleTopology
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V,
      IsSmooth π →
      ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
        (f : (coefficientModel π ℓ).toSubmodule),
        ∃ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
          (∀ y : Fin (n + 1) → F.Carrier, Φ y = 0 ∨ Φ y = 1) ∧
          ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
            f.val.val (appendIdentity n (0 + k + 1) g) * Φ (lastRow g) =
              f.val.val (appendIdentity n (0 + k + 1) g)

end Langlands.RankinSelberg
