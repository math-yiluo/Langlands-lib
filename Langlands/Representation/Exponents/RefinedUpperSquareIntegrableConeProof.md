# Exact proof of strict upper cones for square-integrable product-Levi refinements

Author: Worker 544.

`Langlands.Exponents.refinedUpperSquareIntegrableCone.{uF,uV}` proves exactly
`Langlands.Exponents.RefinedUpperSquareIntegrableConeStatement.{uF,uV}`.
The proof is an internal application of the stronger published theorem
`Langlands.Exponents.RefinedUpperSquareIntegrableCone.isPositiveRootCone`
from [the upper-cone module](RefinedUpperSquareIntegrableCone.md), authored by
Worker 953. The [closed statement](RefinedUpperSquareIntegrableConeStatement.md)
and its original-source provenance are unchanged.

## Implemented proof and scope

The proof introduces the prime, field, topological data, positive rank and
ordered block shape, installs `T.topology` and `T.leviTopologicalGroup C`,
then introduces all remaining binders of the closed proposition. In particular,
it retains independent universes `F : PadicField.{uF} p` and `V : Type uV`,
an arbitrary Borel measurable structure on the actual quotient
`C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)`, one arbitrary supplied
Haar measure `μ`, and the actual representation `σ` with
`IsSquareIntegrableModCenter σ μ`. There is no irreducibility hypothesis.

For each refinement `R`, open-kernel character `χ`, common-power nonzero
generalized-eigencharacter occurrence, supplied real part `x`, and original
block `i`, the final line applies

```lean
RefinedUpperSquareIntegrableCone.isPositiveRootCone
  T C μ σ hsq R χ hgen x hx i
```

The argument uses the same measure, representation, character, occurrence and
real part. Both propositions use precisely the action

```lean
(T.normalizedRefinedJacquet C R σ).comp
  ((Geometric.flattenedLeviEquiv F.Carrier C R).toMonoidHom.comp
    ((C.flatten R).blockScalarLevi F.Carrier))
```

There is no quotient transport or scalar-action identification in this wrapper.
The stronger theorem does not require positive rank or an open character kernel;
the corresponding premises remain quantified in the closed target and are
unused by its proof. No extra premise is introduced.

The conclusion for every original block `i` is the positive root cone of
`fun k => x (C.flattenBlockEquiv R ⟨i, k⟩)` in its original inner order.
Thus that block has total sum zero and every nonempty proper prefix has strictly
positive sum. For a singleton refinement the zero sum forces its sole coordinate
to vanish. The coordinates are the supplied scalar real parts, with no fine-size
factors.

## Reusable strict-prefix and central-direction helpers

The same imported module already exposes the following declarations in namespace
`Langlands.Exponents.RefinedUpperSquareIntegrableCone`:

- `partialSum_pos` proves strict positivity for every proper prefix
  `0 < k < (R i).length`. It has the same arbitrary representation, single
  supplied Haar measure, actual flattened occurrence and supplied real-part
  hypotheses as the stronger cone theorem.
- `blockSum_eq_zero` proves a separate zero sum for each original block,
  including singleton refinements, under those same hypotheses.
- `norm_eq_one_of_mem_center` proves norm one for a nested fine-scalar tuple
  that is weakly contracting in every original block, acts centrally in the
  original product Levi, and has refined modulus one. It uses square
  integrability and the same actual generalized-eigencharacter occurrence;
  it does not require a supplied real part.

None of these helpers requires irreducibility, positive ambient rank, or an open
character kernel. The imported `isPositiveRootCone` pairs `blockSum_eq_zero`
and `partialSum_pos`. Its strict-prefix proof applies
`Langlands.ProductLeviSquareIntegrable.norm_lt_one_of_diagonal` to a prefix
uniformizer tuple and uses `norm_testScalars` to obtain
`q ^ (-partialSum x_i k) < 1`. Since `q > 1`, the prefix sum is positive.
Its zero-sum proof applies `norm_eq_one_of_mem_center` to a full-block
uniformizer tuple independently in each original block; the norm identity then
gives `q ^ (-sum x_i) = 1`, hence that block's sum is zero.

These are existing proved Library interfaces for reuse by the whole-chamber
criterion. This contribution adds only the exact closed theorem application;
it introduces no duplicate helpers or new analytic criterion. Its imports use
the existing analytic and central-action proofs, with no downstream support,
regular-head, exhaustion, segment-classification or joint-support premise.
