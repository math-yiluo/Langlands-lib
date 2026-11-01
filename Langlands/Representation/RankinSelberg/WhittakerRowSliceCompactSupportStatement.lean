import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.WhittakerNormData

/-!
# Compact support of Whittaker row data on a determinant slice

The compact-support assertion of JPSS (1983), Section 4.6, printed page 412,
for the norm of `W(g) Φ(η g)` on each fixed determinant slice of the actual
quotient `N_(n+1) \ GL_(n+1)`, for actual coefficient images of smooth
representations. This is a proposition definition; no proof is supplied.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- On every determinant slice, the norm of `W(g) Φ(lastRow g)`, extended by zero
off the slice, has compact support on the actual quotient topology. The scope is
every actual coefficient image of every smooth representation, including zero
functionals, zero coefficients, zero test functions and actual rank one. -/
def WhittakerRowSliceCompactSupportStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V,
      IsSmooth π →
      ∀ ℓ : glFunctionals ψ n π,
        ∀ W : (coefficientModel π ℓ).toSubmodule,
        ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
        ∀ k : ℤ,
          HasCompactSupport
            ((determinantSlice T n k).indicator
              (fun q : LeftUnipotentQuotient n F.Carrier =>
                whittakerNorm ψ W.val q * ‖Φ (quotientLastRow n q)‖))

end Langlands.RankinSelberg
