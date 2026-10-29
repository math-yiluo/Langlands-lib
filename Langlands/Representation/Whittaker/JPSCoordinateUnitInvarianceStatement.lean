import Langlands.Representation.Whittaker.JPSFunctionSpace

/-!
# Uniform coordinate-unit invariance for actual JPS coordinate germs

An internal regularity and uniformity prerequisite for JPS (1979), Lemma (2.2.1).
This module defines a proposition only.
-/

namespace Langlands.Whittaker

open JPSFunctionSpace

universe uF

/-- Local constancy and finite coordinate operator span give one compact open
norm-one subgroup acting trivially on the actual coordinate-germ quotient.
For each representative, one positive coordinate threshold works for all torus
tuples and every element of that subgroup. This is an internal derived target. -/
def JPSCoordinateUnitInvarianceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
      IsLocallyConstantSpace W T →
      HasFiniteCoordinateOperatorSpan W T i →
      ∃ U : Subgroup F.Carrierˣ,
        IsOpen (U : Set F.Carrierˣ) ∧
        IsCompact (U : Set F.Carrierˣ) ∧
        (∀ u ∈ U, T.normalizedAbs (u : F.Carrier) = 1) ∧
        (∀ u ∈ U, ∀ q : CoordinateGerm W T i, sigma W T i u q = q) ∧
        ∀ f : W.toSubmodule,
          ∃ ε : ℝ, 0 < ε ∧
            ∀ a : Torus F n,
              T.normalizedAbs (a i : F.Carrier) < ε →
              ∀ u ∈ U, (coordinateRepresentation W i u f).val a = f.val a

end Langlands.Whittaker
