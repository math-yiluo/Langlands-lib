# Casimir elements of dual families and the trace-form radical

Module `Langlands.LinearAlgebra.TraceFormCasimir`, namespace
`Langlands.LinearAlgebra.TraceFormCasimir`.

Two general facts used in the Casimir proof of Freudenthal's multiplicity
formula. The first is the commutation of a Casimir element (Humphreys,
*Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.2), stated
for an associative algebra with a trace-like linear form and without a basis.
The second is a consequence of Cartan's criterion (Humphreys §4.3 and §5.1):
the trace form of a linear Lie algebra with no nonzero nilpotent ideal has a
commutative radical. The module works with Mathlib's Lie bracket
`⁅x, y⁆ = x y - y x` on an associative ring (`LieRing.ofAssociativeRing`, a
local instance).

## Commutation of the Casimir element

`commute_sum_mul`. Let `A` be a `k`-algebra, `T : A →ₗ[k] k` a linear form with
`T (x y) = T (y x)`, `g` a subspace of `A`, and `b d : ι → A` finite families.
Assume every `v ∈ g` expands in two ways:

- `v = ∑_a T (v d_a) b_a`, and
- `v = ∑_a T (b_a v) d_a`.

If the commutators `x b_a - b_a x` and `x d_a - d_a x` all lie in `g`, then `x`
commutes with `Ω = ∑_a b_a d_a`.

The families need not lie in `g`, and `g` need not be closed under the
bracket; the lemma only needs the commutators with `x` to lie in `g`. In the
application `g` is a Lie algebra of endomorphisms, `b` and `d` are dual bases of
`g` for the trace form, and `x ∈ g`.

Proof. `x Ω - Ω x = ∑_a ((x b_a - b_a x) d_a + b_a (x d_a - d_a x))`. Expand
the first commutator with the first expansion and the second with the second
expansion. After swapping the order of summation in the second double sum, the
coefficient of `b_c d_a` is

`T ((x b_a - b_a x) d_c) + T (b_a (x d_c - d_c x)) = T (x (b_a d_c)) - T ((b_a d_c) x)`,

which is zero.

## The radical of the trace form

Let `k` be a field of characteristic zero, `U` a finite-dimensional `k`-space,
and `g` a Lie subalgebra of `End k U`.

- `toEnd_eq`, `traceForm_eq`: the action of `x ∈ g` on `U` is `x` itself, so
  Mathlib's trace form `LieModule.traceForm k g U x y` is `trace (x y)`.
- `commute_of_trace_mul_eq_zero`. Assume that every Lie ideal of `g` whose
  elements are all nilpotent endomorphisms is zero. If `x, y ∈ g` satisfy
  `trace (x z) = 0` and `trace (y z) = 0` for all `z ∈ g`, then `x y = y x`.

Proof. Let `R` be the orthogonal complement of `g` for the invariant trace
form. It is a Lie ideal of `g` (Mathlib's `LieAlgebra.InvariantForm.orthogonal`),
and `x, y ∈ R`. The trace form of `R` acting on `U` is the restriction of the
trace form of `g`, so it vanishes. By Cartan's criterion in Mathlib
(`LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`), the derived
algebra `⁅R, R⁆` acts nilpotently on `U`. Mathlib's
`LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap` identifies the derived
algebra of `R` with the ideal `⁅R, R⁆` of `g`. So every element of `⁅R, R⁆` is a
nilpotent endomorphism, and the hypothesis gives `⁅R, R⁆ = 0`. In particular
`x y - y x = ⁅x, y⁆ = 0`.
