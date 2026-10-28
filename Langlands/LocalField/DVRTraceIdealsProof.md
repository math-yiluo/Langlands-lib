# Exact trace images of DVR ideal powers

`Langlands.LocalField.dvrTraceIdeals.{uA,uB,uK,uL}` proves exactly the published
proposition `Langlands.LocalField.DVRTraceIdeals.{uA,uB,uK,uL}` from
`Langlands.LocalField.DVRTraceIdealsStatement`. There are no outer hypotheses.
The four carriers have independent universes, and all ring, field, algebra,
fraction-field, scalar-tower, finiteness, separability and integral-closure
structures are those quantified by that proposition.

Write `mA` and `mB` for the maximal ideals. Under the literal supplied
equalities `Ideal.map (algebraMap A B) mA = mB ^ e` and
`differentIdeal A B = mB ^ d`, with `0 < e`, the theorem proves, for every
`n : ℕ` and `y : K`,

```
(∃ x : B, x ∈ mB ^ n ∧ Algebra.trace K L (algebraMap B L x) = y) ↔
  (∃ a : A, a ∈ mA ^ ((d + n) / e) ∧ algebraMap A K a = y).
```

Natural division gives the floor exponent. The proof includes `n = 0` and
`d = 0`. Torsion-freeness of `B` over `A` is derived using the published
`isTorsionFree_of_isFractionRing_tower`, as in the target proposition.

## Implemented proof

All auxiliary declarations are in
`Langlands.LocalField.DVRTraceIdealsAux`. They are internal steps of this
proof, derived from Mathlib's integral trace, fractional-ideal duality and DVR
ideal theory.

For an ideal `J` of `B`, the definition

```
traceIdeal J := (J.restrictScalars A).map (Algebra.intTrace A B)
```

is an ideal of `A`. It is the actual image under an `A`-linear map.
`Algebra.algebraMap_intTrace` identifies this integral trace, after applying
`A → K`, with the supplied field trace `Algebra.trace K L` on `B → L`.

The first three lemmas establish a scaled codifferent criterion.
`trace_inv_mul` moves the inverse of a scalar from `A` through the field trace,
using the supplied tower `A → K → L`. For `a ≠ 0`,
`trace_div_mem_range_iff` says that
`(algebraMap A K a)⁻¹ * Tr(x)` belongs to the image of `A` in `K` exactly when
`intTrace(x)` belongs to the principal ideal `(a)`. Its proof uses
`Algebra.algebraMap_intTrace` and injectivity of `A → K`.

`scaled_mem_dual_iff` then proves

```
(a⁻¹) * J ≤ FractionalIdeal.dual A K 1
  ↔ ∀ x ∈ J, Algebra.intTrace A B x ∈ Ideal.span {a},
```

where the left side is an inequality of fractional ideals in `L`, with `a`
mapped through the supplied `A → L`. In one direction, dual membership is
tested at `1 ∈ B`. In the other, for every `b ∈ B`, the element `x * b`
still belongs to `J`, so the same trace condition verifies the entire dual
membership test.

`traceIdeal_le_span_iff` uses the genuine different. The identity
`coeIdeal_differentIdeal A K L B` identifies its fractional ideal with
`(FractionalIdeal.dual A K 1)⁻¹`. The codifferent and the scalar fractional
ideal are nonzero, so fractional-ideal inversion and multiplication transform
the preceding criterion into

```
traceIdeal J ≤ Ideal.span {a}
  ↔ differentIdeal A B * J ≤ Ideal.span {algebraMap A B a}.
```

This is the principal-ideal form of the inverse-different trace criterion.
No different or trace-image hypothesis is substituted for Mathlib's objects.

For `J = mB ^ n`, `traceIdeal_le_pow_iff` chooses an irreducible uniformizer
`π` of `A` and writes `mA ^ r = (π ^ r)`. The given ideal-map equality
identifies the extended principal ideal with `mB ^ (e * r)`. The given
different equality identifies the product on the other side with
`mB ^ (d + n)`. Strict antitonicity of maximal-ideal powers in the DVR `B`
therefore gives, for every natural `r`,

```
traceIdeal (mB ^ n) ≤ mA ^ r ↔ e * r ≤ d + n.
```

`traceIdeal_eq_pow` first deduces that this trace ideal is nonzero. Otherwise
it would be contained in `mA ^ (d + n + 1)`, forcing
`e * (d + n + 1) ≤ d + n`; this contradicts `e ≥ 1`.
Mathlib's `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible` now expresses
the trace ideal as `mA ^ s`. Put `q = (d + n) / e`. Applying the containment
criterion at `s` gives `s ≤ q`. Applying it at `q`, using the natural-division
inequality, gives `mA ^ s ≤ mA ^ q`, hence `q ≤ s` by strict antitonicity.
Thus `s = q` and the trace ideal is exactly `mA ^ q`.

The final theorem converts that ideal equality to the pointwise target.
For a trace preimage `x`, it chooses `Algebra.intTrace A B x` on the right.
Conversely, membership of `a` in the trace ideal unfolds to a single
`x ∈ mB ^ n` with `Algebra.intTrace A B x = a`, by the definition of
`Submodule.map`. Applying `Algebra.algebraMap_intTrace` produces the required
field-trace equality. This step supplies one actual preimage for each element,
including when the exponent is zero.

## Sources and scope

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979, source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`:

- Chapter III §3, printed p.50 / PDF p.57, defines the codifferent by integral
  trace pairings and the different as its inverse.
- Chapter III §3, Proposition 7 and its proof, printed pp.50–51 / PDF pp.57–58,
  give the fractional-ideal trace-containment criterion. The implemented
  principal-ideal criterion follows this argument using Mathlib's actual dual.
- Chapter V §3, Lemma 4 and its proof, printed p.83 / PDF p.90, recover the
  floor exponent of the trace ideal from those containments.

The original passages were read, together with Jean-Pierre Serre,
*Corrections to J-P. Serre's books* (2019), source
`serre-book-corrections-2019`, SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
Local Fields entries on PDF pp.2–3. No listed correction changes the cited
different or trace formulas.

As documented by the published target, its DVR formulation is a derived
generalization of Serre's Lemma 4, which is stated for a totally ramified
cyclic extension of prime degree. The implemented argument needs only the
finite separable fraction-field extension, integral closure and module
finiteness, together with the two supplied ideal-power equalities. It uses
no Galois, completeness, p-adic or residue-field hypotheses, and no host
trace theorem or downstream norm theorem. The generic containment lemmas
and the explicit nonzero-image argument above explain the implemented route.

## Authors

Worker 107 authored this proof and its English companion. The imported target
interface was formalized by Worker 726 and specified by Worker 512; its
statement and import closure are preserved. No unreviewed peer draft is reused
in this proof module.
