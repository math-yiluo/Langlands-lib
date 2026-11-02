# Proof of Hilbert–Schmidt basis independence

`Langlands.Analysis.OperatorIdeals.hilbertSchmidtBasisIndependence` proves
exactly `HilbertSchmidtBasisIndependenceStatement E F ι κ` from
`Langlands.Analysis.HilbertSchmidtBasisStatement`. Its binders are those of
the statement definition: explicit `E : Type u`, `F : Type v`, `ι : Type w`
and `κ : Type z`, with independent universe levels, followed by the instances
`NormedAddCommGroup E`, `InnerProductSpace ℂ E`, `NormedAddCommGroup F` and
`InnerProductSpace ℂ F`. For every bounded complex-linear map
`A : E →L[ℂ] F` and Hilbert bases `b : HilbertBasis ι ℂ E` and
`c : HilbertBasis κ ℂ E`, it proves that `‖A (b i)‖²` is summable if and only
if `‖A (c j)‖²` is summable, and that the two real sums are equal when the
first family is summable. No separability or countability assumption is used.

The statement's Markdown describes `E` and `F` as complex Hilbert spaces, but
the elaborated statement definition takes no `CompleteSpace` instance: its
section declares `CompleteSpace E` and `CompleteSpace F`, and Lean omits them
because the definition body does not use them. The Lean target, and hence
this theorem, therefore covers all complex inner product spaces `E` and `F`,
which is formally stronger than the Hilbert-space reading. The first three
sections below prove the complete case, and the section after them reduces the
general case to it.

## Parseval in extended nonnegative reals

Throughout the private lemmas, `E` and `F` are complex inner product spaces
carrying section instances `CompleteSpace E` and `CompleteSpace F`; the two
Parseval lemmas use neither. The private lemma `basis_hasSum_norm_sq` obtains
Parseval's identity `HasSum (fun i => ‖⟪b i, x⟫‖²) (‖x‖²)` for a Hilbert basis
`b` of any inner product space. The coordinate representation `b.repr` is a
linear isometric equivalence onto `ℓ²`, its coordinates are the inner products
`⟪b i, x⟫`, and Mathlib's `lp.hasSum_norm` at exponent `2` gives the
squared-norm sum of an `ℓ²` element. The lemma `basis_ennreal_norm_sq` moves
this identity to `ℝ≥0∞`: the sum of `ENNReal.ofReal ‖⟪b i, x⟫‖²` is
`ENNReal.ofReal ‖x‖²`.

## Comparison through a codomain basis

`basis_ennreal_sum_adjoint` fixes a domain Hilbert basis `b` indexed by `ι`
and a codomain Hilbert basis `d` with an auxiliary index type `τ` in its own
universe. It proves, in `ℝ≥0∞`,

`∑ i, ‖A (b i)‖² = ∑ j, ‖A† (d j)‖²`,

where `A†` is `ContinuousLinearMap.adjoint A` and each squared norm is cast by
`ENNReal.ofReal`. Parseval in `d` expands each `‖A (b i)‖²` as
`∑ j, ‖⟪d j, A (b i)⟫‖²`. The nonnegative double sum is interchanged with
`ENNReal.tsum_comm`, which needs no summability hypothesis. The adjoint
identity `⟪d j, A x⟫ = ⟪A† (d j), x⟫` (`ContinuousLinearMap.adjoint_inner_right`)
and symmetry of the norm of an inner product (`norm_inner_symm`) rewrite each
term as `‖⟪b i, A† (d j)⟫‖²`. Parseval in `b` then collapses each inner sum to
`‖A† (d j)‖²`. The adjoint uses completeness of both `E` and `F`.

`basis_ennreal_sum_eq` chooses a codomain Hilbert basis by Mathlib's
`exists_hilbertBasis ℂ F`, which needs no separability. Applying the previous
lemma to `b` and to `c` with the same codomain basis identifies both
domain-basis sums with one codomain sum. Hence the two extended nonnegative
sums are equal, including when they are infinite.

## Real summability and equality

`basis_summable_transfer` assumes that `‖A (b i)‖²` is summable in `ℝ`. Then
its `ENNReal.ofReal` sum is finite (`Summable.tsum_ofReal_ne_top`), so the
equal sum over `c` is finite. A finite extended nonnegative sum has summable
real parts (`ENNReal.summable_toReal`), and `ENNReal.toReal_ofReal` on the
nonnegative squares identifies those real parts with `‖A (c j)‖²`. Applying the
lemma in both directions gives the summability equivalence.

The private theorem `basis_independence_complete` states the target's two
conclusions for complete `E` and `F`. Its summability equivalence is the
transfer lemma in both directions. For the equality clause, both real families
are summable, so `ENNReal.ofReal_tsum_of_nonneg` writes `ENNReal.ofReal` of
each real sum as the corresponding extended nonnegative sum. These sums are
equal by `basis_ennreal_sum_eq`. Applying `ENNReal.toReal` and using
nonnegativity of the real sums (`tsum_nonneg`) gives the required equality of
real sums.

## Removing the completeness assumptions

The public theorem introduces `A`, `b` and `c` and reduces to
`basis_independence_complete` in two steps.

- The domain is complete because it has a Hilbert basis: `b.repr` is a linear
  isometric equivalence from `E` onto `ℓ²(ι, ℂ)`, which is complete, so
  `b.repr.toIsometryEquiv.completeSpace` gives `CompleteSpace E`.
- The codomain is replaced by its completion. The composite
  `A' = UniformSpace.Completion.toComplL ∘L A : E →L[ℂ] Completion F` is a
  bounded complex-linear map into a complete inner product space (Mathlib's
  `Mathlib.Analysis.InnerProductSpace.Completion`). The embedding preserves
  norms (`UniformSpace.Completion.norm_coe`), so `‖A' x‖ = ‖A x‖` for every
  `x`.

Rewriting with this norm identity turns the conclusion of
`basis_independence_complete A' b c` into the target's conclusion for `A`.

## Provenance and scope

The statement's motivation is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and (9.3), the independence
assertion on printed pp. 240–241, and Exercise 9.1 on printed p. 267. The
statement's Markdown records the source fingerprints, the reading of the
author's errata and the derived extension to arbitrary basis indices and
rectangular bounded operators. The proof route described here is an
implementation choice using Mathlib's Hilbert-basis, adjoint and `ℝ≥0∞`
summation APIs. It is not attributed to a written proof in the source, which
leaves the assertion as an exercise.

The theorem proves only this basis-independence proposition. It does not
define a Hilbert–Schmidt predicate or norm, and it proves no ideal law,
adjoint invariance of a Hilbert–Schmidt norm, compactness, trace-class or
trace result, integral-kernel description or automorphic application. Those
remain separate obligations.

The complete-case proof was written by Worker 116 and adopted for this
exact-target proof task by Worker 1246, who added the reduction removing the
completeness assumptions.
