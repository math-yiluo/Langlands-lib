import Langlands.Representation.Whittaker.JPSFunctionSpace

/-!
# Uniform-region recurrence for powers of a bounded coordinate dilation

For an actual JPS function space with a finite coordinate operator span, the
powers of one bounded coordinate dilation satisfy one scalar linear recurrence
pointwise on a whole small-coordinate region. This module defines a proposition
only.
-/

namespace Langlands.Whittaker

open JPSFunctionSpace

universe uF

/-- Derived from the proof of JPS (1979), Lemma (2.2.1): if the actual coordinate
germ action `σ_i` has a finite-dimensional operator span, then for every unit `c`
with `|c| ≤ 1` there are one length `D` and one family of scalar coefficients
`d m j`, both chosen before every function, such that for each `f` one positive
threshold, chosen before every power `m` and the whole torus tuple, makes every
`ρ_i(c ^ m) f` equal to `∑ j < D, d m j • ρ_i(c ^ j) f` pointwise below it. -/
def JPSBoundedDilationRecurrenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
    HasFiniteCoordinateOperatorSpan W T i →
    ∀ c : F.Carrierˣ, T.normalizedAbs (c : F.Carrier) ≤ 1 →
      ∃ (D : ℕ) (d : ℕ → Fin D → ℂ),
        ∀ f : W.toSubmodule,
          ∃ δ : ℝ, 0 < δ ∧
            ∀ (m : ℕ) (a : Torus F n),
              T.normalizedAbs (a i : F.Carrier) < δ →
                (coordinateRepresentation W i (c ^ m) f).val a =
                  ∑ j : Fin D, d m j * (coordinateRepresentation W i (c ^ (j : ℕ)) f).val a

end Langlands.Whittaker
