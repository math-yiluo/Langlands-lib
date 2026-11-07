# Trace characters of exact virtual representations and induced lines

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. The module
constructs the trace character on the Library's exact virtual groups and proves
the Frobenius formula for actual finite-index induction. These traces are the
invariant later used to split an actual Brauer relation by the classes of its
unramified twists (Deligne 1973, §4.10). This module asserts no epsilon or
L-factor identity.

## Linear algebra (`Langlands.LocalFactor.BrauerKernel`)

- `matrix_trace_fromBlocks`: the trace of a block matrix is the sum of the traces
  of its two diagonal blocks.
- `trace_eq_trace_restrict_add_trace_mapQ`: for an endomorphism `e` of a
  finite-dimensional vector space and an `e`-stable subspace `W`,
  `tr e = tr (e|_W) + tr (e on V/W)`. The proof follows Mathlib's
  `LinearMap.det_eq_det_mul_det` line by line, with the basis `sumQuot` adapted to
  `W` and the block-trace formula in place of the block-determinant formula.
- `exactSequence_trace`: trace additivity for an actual short exact sequence
  `0 → V → U → T → 0` of representations at every group element. The proof has the
  same structure as the Library's `Weil.exactSequence_det`: `V` is identified with
  the kernel of `U → T`, and `U/V` with `T`. It uses invariance of the trace under
  conjugation (`LinearMap.trace_conj'`).
- `trace_monomial`: let `Q` be a finite set and `M` a finite-dimensional space.
  Suppose an operator on `Q → M` has the form `(T v)(q) = B_q (v (σ q))`. Then its
  trace is `Σ_{q, σ q = q} tr B_q`. The identity is written as a sum of the
  single/projection idempotents. Cyclicity of the trace then reduces each summand
  to a diagonal block.

## Trace characters of representations (`Langlands.FiniteRepresentation`)

`traceFunction A g` is `LinearMap.trace` of the actual action operator of `g` on a
finite-dimensional complex representation `A`. It is invariant under genuine
equivalence (`traceFunction_eq_of_equiv`), so it descends to isomorphism classes
(`traceFunctionClass`). It is additive in short exact sequences
(`traceFunction_shortExact`). For a character line it equals the character
(`traceFunction_characterLine`), and restriction precomposes it
(`traceFunction_restrict`).

`traceFunction_induce` is Frobenius's formula for the Library's finite-index
induction. That induction is the space of left-equivariant functions with right
translation, which `Induction.coordinates` identifies with functions on the right
cosets `S\G`. In these coordinates `g` acts by
`v ↦ (q ↦ A(factor(q.out · g)) (v (coset(q.out · g))))`, so `trace_monomial` gives

```text
tr Ind(A)(g) = Σ_{q ∈ S\G, q·g = q} tr A(q.out · g · (q.out)⁻¹).
```

Here `factor S (q.out * g)` is exactly `q.out · g · (q.out)⁻¹` when the coset is
fixed. The cosets carry the Library's finite-index `Fintype` instance.

## Trace on exact virtual groups (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

For any predicate `P` on finite-dimensional complex representations,
`trace P : ExactGrothendieckGroup P →ₗ[ℤ] (G → ℂ)` is the published universal
property `lift` applied to the class trace. Exactness of the class trace is
`traceFunction_shortExact`. The evaluation lemmas are:

- `trace_ofRepresentation`, the value on a genuine class;
- `trace_characterClass`, the value on a continuous character line;
- `trace_restrict`, restriction precomposes the trace;
- `trace_induce`, the Frobenius formula for every virtual class. Here
  `frobeniusFunctional S g` is the integer-linear functional
  `f ↦ Σ_{q fixed by g} f(factor S (q.out * g))`, and `frobeniusFunctional_apply`
  exposes it.

The last two results are extended from genuine classes by `hom_ext`.

## Common-closure induction (`Langlands.LocalFactor.CommonClosure`)

`CommonClosure.trace_induce` specializes the formula to the actual nested induction
`induce F E L h`. That induction is restriction along `nestedWeilEquiv` followed by
exact induction from `W_L ∩ W_E` to `W_E`. So the trace of `induce F E L h x` at
`w ∈ W_E` is the Frobenius functional of `W_L ∩ W_E` at `w`, applied to the trace of
`x` composed with `nestedWeilEquiv`. The field universe `uF` and the representation
universe `uV` are independent.

## Provenance

The trace character and Frobenius's induced-character formula are standard finite
representation theory. In Deligne, *Les constantes des équations fonctionnelles des
fonctions L* (1973, registered as `deligne-1973-local-constants`), §4.10 (printed
page 542, PDF page 42) decomposes `R(W)` by types. Separating those components needs
a numerical invariant of virtual representations; the trace serves that purpose here.
All proofs are internal derivations from Mathlib and the published Library modules
named above.
