# Proof of the plus-sign Fourier integral of a p-adic lattice coset

Author: Worker 741.

The closing theorem `Langlands.HarmonicAnalysis.padicLatticeFourier.{u}`
proves exactly the published proposition
`Langlands.HarmonicAnalysis.PadicLatticeFourierStatement F T` from
[the statement module](PadicLatticeFourierStatement.md). Its complete
telescope is

```lean
theorem Langlands.HarmonicAnalysis.padicLatticeFourier {p : ℕ} [Fact p.Prime]
    (F : Langlands.PadicField.{u} p) (T : F.TopologicalData) :
    PadicLatticeFourierStatement F T
```

The universe `u` is arbitrary, and the theorem covers every supplied `T`. It
adds no hypotheses. It holds for every unitary additive character `ψ`, every
regular additive Haar measure `μ` with no normalization, every level `m : ℤ`
(negative levels included), every centre `a` and every argument `y`. The
target statement module and its imports are unchanged. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports

- [PadicLatticeFourierStatement](PadicLatticeFourierStatement.md), the target.
- [PadicLatticeGeometryProof](PadicLatticeGeometryProof.md), the published
  geometry proof. Through
  [ZeroRowLastRowCutoffProof](../Representation/RankinSelberg/ZeroRowLastRowCutoffProof.md)
  it supplies three theorems in namespace `Langlands.PadicField.TopologicalData`,
  authored by Worker 252:
  `isCompact_additiveLattice`, `isOpen_additiveLattice` and
  `mem_additiveLattice_of_forall_mul_eq_one`. The last one is derived from the
  conductor and annihilator API of
  [PadicAdditiveConductorProof](PadicAdditiveConductorProof.md) and
  [Conductor](Conductor.md).
- Mathlib's `MeasureTheory.Group.Integral` (translation invariance of the
  Bochner integral) and `MeasureTheory.Function.LocallyIntegrable`
  (integrability of continuous functions on compact sets).

`additiveConductor`, `additiveConductor_spec` and `mem_additiveLattice` come
from [Conductor](Conductor.md). `UnitaryAdditiveCharacter`,
`AdditiveHaarMeasure` and `fourierIntegral` come from [Basic](Basic.md).

## Generic coset lemmas

The section `CompactOpenCoset` works over any field `F` with a topological
ring structure, a measurable space and `BorelSpace F`. `L` is any additive
subgroup of `F`. The coset is written `{x | x - a ∈ L}`, exactly as in the
target. Its raw indicator is `{x | x - a ∈ L}.indicator (fun _ => (1 : ℂ))`.

- `coset_integrand_eq` (private) rewrites the integrand pointwise:
  `ψ.complex (x * y)` times the coset indicator equals the coset's indicator of
  `x ↦ ψ.complex (x * y)`. Both sides are compared on and off the coset.

- `coset_fourierIntegrand_integrable` assumes that `L` is compact and open. It
  proves that the plus-sign integrand `x ↦ ψ.complex (x * y)` times the coset
  indicator is integrable for `μ.measure`. The coset is open because it is the
  preimage of `L` under the continuous map `x ↦ x - a`. It is compact because
  it equals the image of `L` under the continuous map `t ↦ t + a`. After
  `coset_integrand_eq`, Mathlib's `integrable_indicator_iff` reduces the goal
  to integrability on the coset. `ContinuousOn.integrableOn_compact'` gives
  that, since `x ↦ ψ.complex (x * y)` is continuous (`ψ.continuous_complex`)
  and a Haar measure is finite on compact sets. This is a genuine
  integrability proof. It does not rely on Mathlib's convention that the
  integral of a nonintegrable function is `0`.

- `coset_fourierIntegral_eq` extracts the plus-sign phase:

  ```text
  fourierIntegral ψ μ (coset indicator) y =
    ψ.complex (a * y) * ∫ t, ψ.complex (t * y) * L.indicator 1 t ∂μ.measure
  ```

  After unfolding `fourierIntegral`, the substitution `x = a + t` is
  `integral_add_left_eq_self`, the left-translation invariance of the Haar
  measure. The point `a + t` lies in the coset exactly when `t ∈ L`. The
  character satisfies `ψ((a + t) y) = ψ(ay) ψ(ty)` (`AddChar.map_add_eq_mul`).
  `integral_const_mul` then pulls out the constant `ψ.complex (a * y)`. This
  lemma needs neither compactness nor integrability.

- `subgroup_character_integral_of_trivial` assumes that `L` is open and that
  `ψ (t * y) = 1` for all `t ∈ L`. Then the integrand equals the indicator of
  `L` pointwise. `integral_indicator_const` evaluates the integral as
  `((μ.measure L).toReal : ℂ)`. Openness gives measurability of `L`.

- `subgroup_character_integral_of_nontrivial` assumes some `t₀ ∈ L` with
  `ψ (t₀ * y) ≠ 1`, and proves that the integral `I` over `L` is `0`. Translating
  by `t₀` (`integral_add_left_eq_self` again) and using
  `t₀ + t ∈ L ↔ t ∈ L` shows `ψ.complex (t₀ * y) * I = I`. If `I ≠ 0`, then
  `ψ.complex (t₀ * y) = 1` (`mul_eq_right₀`), so `ψ (t₀ * y) = 1` in the unit
  circle (`Circle.coe_eq_one`), a contradiction.

The two orthogonality lemmas are stated separately so that no decidability of
the triviality condition is needed.

## The annihilator of a valuation lattice

`Langlands.PadicField.TopologicalData.forall_mul_eq_one_iff_mem_additiveLattice`
states, for every `ψ`, `m` and `y`,

```text
(∀ t ∈ T.additiveLattice m, ψ (t * y) = 1) ↔
  y ∈ T.additiveLattice (T.additiveConductor ψ - m)
```

Write `L_k = T.additiveLattice k = π^(-k) O` and `n = T.additiveConductor ψ`.

- Forward direction: this is the imported
  `mem_additiveLattice_of_forall_mul_eq_one ψ m y`, after commuting `t * y`
  to `y * t`.
- Reverse direction: if `t ∈ L_m` and `y ∈ L_(n-m)`, then multiplicativity of
  `T.discreteValuation` gives `v(ty) ≤ exp(m) · exp(n - m) = exp(n)`. So
  `ty ∈ L_n`, and the first part of `additiveConductor_spec` says that `ψ` is
  trivial on `L_n`.

## Closing proof

The proof installs `T.topology`, `T.valuativeRel`, `T.localField` and
`borel F.Carrier` with its `BorelSpace` certificate, exactly as the target
does. It introduces `ψ`, `μ`, `m`, `a`, `y` and the target's local bindings
`C` and `indicatorC`.

1. Integrability is `coset_fourierIntegrand_integrable` for
   `L = T.additiveLattice m`. Its compactness and openness come from
   `T.isCompact_additiveLattice m` and `T.isOpen_additiveLattice m`.
2. For the value, `coset_fourierIntegral_eq` rewrites the integral as
   `ψ.complex (a * y)` times the character integral over `L_m`. The proof
   then splits on whether `y ∈ L_(n-m)`.
   - If `y ∈ L_(n-m)`: the annihilator lemma gives triviality of
     `t ↦ ψ(ty)` on `L_m`. `subgroup_character_integral_of_trivial` gives the
     mass `(μ(L_m)).toReal`, and the target indicator of `L_(n-m)` at `y` is
     `1`. Commuting the two factors gives the target.
   - If `y ∉ L_(n-m)`: the annihilator lemma gives some `t₀ ∈ L_m` with
     `ψ(t₀ y) ≠ 1`. `subgroup_character_integral_of_nontrivial` makes the
     integral `0`, and the target indicator at `y` is also `0`.

The phase is the plus-sign `ψ(a*y)` throughout, with no sign reversal. No
self-duality, Haar normalization, Fourier inversion, `SchwartzBruhat`
packaging or `PadicFourierDualityStatement` is used.

## Provenance and original sources

The target is an internal derived specialization, documented in
[the statement's provenance](PadicLatticeFourierStatement.md): Weil's formula
(2) in the proof of Chapter VII §2, Proposition 2, for one coset in dimension
one, written in the Library's lattice, conductor and Fourier conventions.

- André Weil, *Basic Number Theory*, second edition (1973), registered
  `weil-1973-basic-number-theory`, SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
  Chapter VII §2, Proposition 2, formula (2) and Corollary 1, printed p.107
  (PDF p.124). Chapter II §5, Definition 4 and Proposition 12, printed
  pp.41–42 (PDF pp.58–59), give the order of a character and the dual lattice
  `P^(-k-ν)` of `P^k`.
- John Tate, *Number theoretic background*, Corvallis Part II (1979),
  registered `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  §3.2, printed p.13 (PDF p.22): the plus-sign transform
  `f^(y) = ∫ f(x) ψ(xy) dx` and the integer `n(ψ)` of (3.2.6).

The Lean route matches Weil's argument: translation to the lattice, then
vanishing of the character integral unless the argument lies in the dual
lattice. Here the vanishing is proved directly by translation invariance
under one point `t₀`. The dual-lattice level `n - m` is obtained from the Library's
conductor API, as described above, not by quoting Weil's Proposition 12. Worker
741 read these source passages when writing the statement. No errata file for
either source was present in the public notes or the literature collection.

## Verification

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean
4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`). The
project's Lean service compiled the module with no errors and no warnings.
Declaration inspection of `Langlands.HarmonicAnalysis.padicLatticeFourier`
reports a theorem with universe parameter `u`, the type above, and only the
standard axioms. Exact-target validation and independent semantic review are
separate publication checks.
