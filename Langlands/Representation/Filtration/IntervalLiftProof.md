# Lifting an actual quotient composition series

Author: Worker 341. Provenance: internal module-theoretic proof.

`Langlands.actualQuotientSeriesLift` proves exactly
`Langlands.ActualQuotientSeriesLiftStatement.{uK, uG, uV}`, imported from
`Langlands.Representation.Filtration.IntervalLiftStatement`. The coefficient
field, monoid, and representation carrier have independent universes. The
statement pair and all of its imports are unchanged.

Given invariant subspaces `S ≤ T` of an actual representation and a finite
filtration `f` of `quotientRep S T` with simple factors, the theorem constructs
a covering relation series from `S` to `T`. Its length is definitionally the
length `n` of `f`, its factor-index equivalence is `Equiv.refl (Fin n)`, and
each successive quotient is equivalent to the corresponding actual graded
representation of `f` by a `Representation.Equiv`.

## Pullbacks and endpoints

The helpers in `Langlands.IntervalLiftProof` use the published
`LengthCriterionProof.pull S T U`, the image in the ambient representation of
the preimage of `U` under the quotient projection from `T`.

`mem_pull_iff` identifies membership of a vector `x : T.toSubmodule` in this
pullback with membership of its quotient class in `U`. `pull_le` places every
pullback inside `T`, and `pull_mono` proves that inclusions are preserved.
`pull_bot` uses `S ≤ T` and the kernel criterion for the quotient projection to
identify the preimage of zero with `S`. `pull_top` identifies the preimage of
the full quotient with `T`.

## Actual equivalences of successive quotients

`nonempty_quotient_pull_equiv S T U U'` constructs an actual representation
equivalence

```
quotientRep (pull S T U) (pull S T U') ≃ quotientRep U U'.
```

Here the displayed equivalence is `Representation.Equiv`, including both
linear equivalence and compatibility with the monoid action. The helper needs
no inclusion assumption on `U` and `U'`: the published `quotientRep` always
divides the upper subspace by the restriction of the lower subspace to it.
The application to filtration steps does have `U ≤ U'`.

The proof restricts the original quotient projection to a linear map `r`
from `pull S T U'` onto `U'`. Surjectivity follows by choosing a representative
in `T` for each quotient class in `U'`; the membership criterion places that
representative in the pullback. The same criterion says that `r x` lies in
`lower U U'` exactly when `x` lies in
`lower (pull S T U) (pull S T U')`.

Compose `r` with the projection from `U'` onto its quotient by `lower U U'`.
The resulting map kills the lower pullback, so `Submodule.liftQ` induces a
linear map `Φ` on the quotient of the upper pullback. On representatives,
`Φ [x] = [r x]`. The monoid action on every quotient is induced from the
original action, making this map equivariant on representatives. It therefore
defines an intertwining map `Ψ`.

To prove injectivity, choose representatives for two source classes with the
same image. Their images under `r` differ by an element of `lower U U'`.
Linearity and the membership criterion put the difference of the original
representatives in the lower pullback, so the source classes coincide.
Surjectivity follows from surjectivity of `r` and the target quotient
projection. `Representation.IntertwiningMap.ofBijective` turns `Ψ` into the
required actual representation equivalence. This is the implemented third
isomorphism argument; no third-isomorphism statement is assumed.

## Covers and the relation series

For each consecutive pair of filtration subspaces, `pull_mono` supplies the
inclusion between their pullbacks. The equivalence just constructed transports
irreducibility of the original graded quotient to the quotient of the
pullbacks. The proof performs this transport through Mathlib's characterization
of irreducibility as simplicity of the associated monoid-algebra module,
using `LinearMap.isSimpleModule_iff_of_bijective` on the intertwining map.
The published `LengthCriterionProof.isIrreducible_quotientRep_iff` then gives
the covering relation for that pair.

The final relation series has entries `pull S T (f.subrepresentation i)`.
Its first and last entries are `S` and `T` by the filtration endpoint laws and
`pull_bot`/`pull_top`. The identity equivalence of `Fin n` matches the factors,
and `nonempty_quotient_pull_equiv` supplies each factor's actual equivalence.
The graded representation of `f` is definitionally the successive quotient
used in that helper.

The construction applies unchanged when `n = 0` or `S = T`. There is no
finite-dimensionality, global finite-length, group, or `JordanHolderLattice`
assumption. No concatenation of several interval series or comparison of two
representations is claimed here.

## Provenance

This is an internal algebraic proof for the published interval-lifting
interface, rather than a quotation from the literature. It builds on the
published quotient and pullback definitions in `LengthCriterionProof` and
Mathlib's quotient linear maps and intertwining equivalences. The proof pattern
for passing a bijective induced quotient map to a representation equivalence
and transporting irreducibility can also be found in the published helpers
`Langlands.LengthTwo.nonempty_gradedEquiv` and
`Langlands.LengthTwo.isIrreducible_of_equiv`; those helpers are not imported or
assumed here. The proof uses only `propext`, `Classical.choice`, and
`Quot.sound`, with no proof holes or new axioms.
