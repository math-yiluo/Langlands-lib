import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
import Langlands.AllField.Group.GL.PadicSupplement
/-!
# Compact last-row cutoff for smooth zero-row Whittaker coefficients

This proposition isolates the compact-support input to JPSS Section 8.3.
The smooth coefficient-image scope and the zero-or-one cutoff are a derived
internal formulation, as explained in the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding ZeroRowLastRowCutoffStatement
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

/-- Every coefficient in a smooth Whittaker coefficient image admits a
zero-or-one Schwartz–Bruhat cutoff on the last row that leaves its zero-row
restriction unchanged. This is a closed proposition definition, not a proof. -/
def ZeroRowLastRowCutoffStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n k : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V,
      IsSmooth π →
      ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
        (f : (coefficientModel π ℓ).toSubmodule),
        ∃ Φ : SchwartzBruhat (Fin (n + 1) → F),
          (∀ y : Fin (n + 1) → F, Φ y = 0 ∨ Φ y = 1) ∧
          ∀ g : Langlands.GeneralLinear (n + 1) F,
            f.val.val (appendIdentity n (0 + k + 1) g) * Φ (lastRow g) =
              f.val.val (appendIdentity n (0 + k + 1) g)

end Langlands.AllField.RankinSelberg
