import Langlands.Representation.Whittaker.JPSFunctionSpace

/-!
# Uniform small-coordinate dilation for actual JPS function spaces

The small-coordinate dilation step in the proof of JPS (1979), Lemma (2.2.1),
for the actual function spaces and coordinate-germ quotients of
`Langlands.Whittaker.JPSFunctionSpace`. This module defines a proposition only.
-/

namespace Langlands.Whittaker

open JPSFunctionSpace

universe uF

/-- JPS (1979), proof of Lemma (2.2.1): from local constancy and a finite
coordinate operator span alone, one finite set `Y` of finite functions on `Fˣ`
and one operator family `A` in the span of the bounded coordinate dilations
`ρ_i(b)`, `|b| ≤ 1`, both chosen before every function, expand the action
`σ_i(b)` on the actual germ quotient for every `b`. For each `f`, one positive
threshold, chosen before the whole torus tuple and every `b` with `|b| ≤ 1`,
makes the expansion of `ρ_i(b) f` hold pointwise below it. -/
def JPSUniformDilationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
      IsLocallyConstantSpace W T →
      HasFiniteCoordinateOperatorSpan W T i →
      ∃ (Y : Finset (F.Carrierˣ → ℂ))
        (A : (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule),
        (∀ η ∈ Y, Continuous η ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) ∧
        (∀ η ∈ Y, A η ∈ Submodule.span ℂ {B : Module.End ℂ W.toSubmodule |
          ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧
            coordinateRepresentation W i b = B}) ∧
        (∀ (b : F.Carrierˣ) (f : W.toSubmodule),
          sigma W T i b (germMap W T i f) =
            germMap W T i (∑ η ∈ Y, η b • A η f)) ∧
        ∀ f : W.toSubmodule,
          ∃ ε : ℝ, 0 < ε ∧
            ∀ a : Torus F n,
              T.normalizedAbs (a i : F.Carrier) < ε →
              ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
                (coordinateRepresentation W i b f).val a =
                  ∑ η ∈ Y, η b * (A η f).val a

end Langlands.Whittaker
