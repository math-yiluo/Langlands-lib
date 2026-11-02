# Proof of the Hilbert–Schmidt vector-space, adjoint and ideal laws

`Langlands.Analysis.OperatorIdeals.hilbertSchmidtIdeal` proves exactly
`HilbertSchmidtIdealStatement.{u, v, w}` from
`Langlands.Analysis.HilbertSchmidtIdealStatement`. Its only universe
parameters are the independent levels `u`, `v` and `w` of the spaces `E`,
`F` and `G`. After introducing the three spaces and their nine instances
(`NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` for each),
it returns the six clauses of the target conjunction in order, using the
public theorems described below. The predicate is the existing
`IsHilbertSchmidt` from `Langlands.Analysis.OperatorIdeals`: some subset
`s : Set E` indexes a Hilbert basis `b` of `E` for which
`fun i => ‖A (b i)‖ ^ 2` is summable. No separability, countability or
finite-dimensionality assumption is added anywhere in the module.

The module imports the published statement by Lean name, together with
Mathlib's infinite sums in `ℝ≥0∞` and the `norm_num` and `linarith`
tactics. It proves its own coefficient-sum facts and does not import the
separately published basis-independence theorem
`hilbertSchmidtBasisIndependence`.

## Section variables

The section declares `E : Type u`, `F : Type v`, `G : Type w`, and index
types `ι : Type z` and `κ : Type t`. Each of `E`, `F` and `G` carries
`NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` section
instances. Lemmas that do not need some completeness instance remove it
with `omit … in`, as stated below. The auxiliary levels `z` and `t` occur
only in the private lemmas; the final theorem does not use them.

## Parseval and the adjoint identity

The private lemma `ideal_basis_hasSum_norm_sq` proves Parseval's identity
`HasSum (fun i => ‖⟪b i, x⟫‖ ^ 2) (‖x‖ ^ 2)` for any Hilbert basis
`b : HilbertBasis ι ℂ E` and any `x : E`, without completeness of `E`.
It applies `lp.hasSum_norm` with exponent `2` to the coordinate vector
`b.repr x` in `ℓ²`, then rewrites with `HilbertBasis.repr_apply_apply`,
`Real.rpow_two` and the fact that `b.repr` is a linear isometry
equivalence. The private lemma `ideal_basis_ennreal_norm_sq` restates this
in `ℝ≥0∞`: the sum of `ENNReal.ofReal (‖⟪b i, x⟫‖ ^ 2)` equals
`ENNReal.ofReal (‖x‖ ^ 2)`, by `ENNReal.ofReal_tsum_of_nonneg`.

The private lemma `ideal_basis_ennreal_adjoint` takes a bounded map
`A : E →L[ℂ] F`, a Hilbert basis `b : HilbertBasis ι ℂ E` and a Hilbert
basis `d : HilbertBasis κ ℂ F`. It proves, in `ℝ≥0∞`,

`∑' i, ofReal (‖A (b i)‖ ^ 2) = ∑' j, ofReal (‖A.adjoint (d j)‖ ^ 2)`.

The calculation expands each `‖A (b i)‖ ^ 2` by Parseval on `d`, exchanges
the two nonnegative extended sums with `ENNReal.tsum_comm`, which holds for
arbitrary index types, rewrites `⟪d j, A (b i)⟫` as
`⟪A.adjoint (d j), b i⟫` with `ContinuousLinearMap.adjoint_inner_right`,
uses `norm_inner_symm` to reach `‖⟪b i, A.adjoint (d j)⟫‖`, and collapses
each inner sum by Parseval on `b`.

The private lemma `ideal_adjoint_summable` deduces that real summability of
`fun i => ‖A (b i)‖ ^ 2` implies real summability of
`fun j => ‖A.adjoint (d j)‖ ^ 2`. Summability makes the left extended sum
finite (`Summable.tsum_ofReal_ne_top`), the identity above makes the right
sum finite, and `ENNReal.summable_toReal` with
`ENNReal.toReal_ofReal` returns real summability.

## Adjoint invariance and every domain basis

`isHilbertSchmidt_adjoint` proves that `IsHilbertSchmidt A` implies
`IsHilbertSchmidt A.adjoint`. It takes the witnessing basis of `A`, chooses
a Hilbert basis of `F` from `exists_hilbertBasis ℂ F`, and applies
`ideal_adjoint_summable`. `isHilbertSchmidt_adjoint_iff` proves
`IsHilbertSchmidt A ↔ IsHilbertSchmidt A.adjoint`; the reverse direction
applies the forward direction to `A.adjoint` and rewrites with
`ContinuousLinearMap.adjoint_adjoint`.

The private lemma `ideal_summable_basis` proves that a Hilbert–Schmidt `A`
is square summable on every Hilbert basis `b : HilbertBasis ι ℂ E`. It
transfers summability from the witnessing basis to the adjoint on a chosen
basis of `F`, then applies `ideal_adjoint_summable` to `A.adjoint` with
target basis `b` and rewrites `A.adjoint.adjoint` to `A`.

## Vector-space laws

`isHilbertSchmidt_zero` omits `CompleteSpace F`. It takes a Hilbert basis
of `E` from `exists_hilbertBasis ℂ E`; the squared-image family of the zero
map is identically zero, hence summable.

`isHilbertSchmidt_add` takes the witnessing basis `b` of `A` and obtains
summability of `B` on the same `b` from `ideal_summable_basis`. It then
compares `‖A (b i) + B (b i)‖ ^ 2` with the summable nonnegative family
`2 * (‖A (b i)‖ ^ 2 + ‖B (b i)‖ ^ 2)` by `Summable.of_nonneg_of_le`. The
pointwise inequality follows by `nlinarith` from the triangle inequality,
nonnegativity of the norm, and `0 ≤ (‖A (b i)‖ - ‖B (b i)‖) ^ 2`.

`isHilbertSchmidt_smul` omits `CompleteSpace E` and `CompleteSpace F`. On
the witnessing basis, `‖(c • A) (b i)‖ ^ 2 = ‖c‖ ^ 2 * ‖A (b i)‖ ^ 2` by
`norm_smul` and `mul_pow`, so the family is a constant multiple of a
summable family.

## Composition laws

`isHilbertSchmidt_postcomp` omits all three completeness instances. For
`A : E →L[ℂ] F` and `B : F →L[ℂ] G`, it keeps the witnessing basis of `A`
and compares `‖B (A (b i))‖ ^ 2` with `‖B‖ ^ 2 * ‖A (b i)‖ ^ 2`. The
pointwise bound squares the operator-norm estimate `B.le_opNorm (A (b i))`
using `sq_le_sq₀`.

`isHilbertSchmidt_precomp` handles `A : E →L[ℂ] F` and `C : G →L[ℂ] E`.
By `isHilbertSchmidt_adjoint_iff` it suffices to show that
`(A.comp C).adjoint` is Hilbert–Schmidt. `ContinuousLinearMap.adjoint_comp`
rewrites this adjoint as `C.adjoint.comp A.adjoint`, and
`isHilbertSchmidt_postcomp` applies to the Hilbert–Schmidt map `A.adjoint`
supplied by `isHilbertSchmidt_adjoint`.

## Scope and provenance

The statement Markdown records the motivating Getz–Hahn Definition 9.1.1
and equation (9.3) and explains the derived rectangular, arbitrary-index
scope. This proof is an internal derivation. Its route is not attributed
to a written source proof. The module makes no canonical-norm, trace-class,
compactness or convolution claim. Worker 116 wrote the implementation, and
Worker 1257 prepared this final description for submission.
