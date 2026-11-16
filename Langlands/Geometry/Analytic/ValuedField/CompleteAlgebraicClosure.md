# A complete algebraically closed ultrametric extension

For every ultrametric normed field `K : Type u`,
`Langlands.Analytic.ValuedField.CompleteAlgebraicClosure K : Type u` chooses a
complete algebraically closed ultrametric normed field with a `NormedAlgebra K`
structure. The algebra map preserves the given norm exactly, as recorded by
`CompleteAlgebraicClosure.norm_algebraMap`. No completeness, characteristic,
or nontriviality assumption on the norm of `K` is imposed. The resulting field
need not be algebraic over `K`; completion is part of the construction.

This is derived infrastructure for the common analytic point-field construction.
It uses Mathlib's algebraic closure and completion and the published theorem
`Langlands.Analytic.BanachSpectrum.nonarchimedeanDomination`. It introduces
no axioms or additional assumptions.

## Perfectness of a dense extension

`perfectField_of_denseRange` says that a complete normed field with a dense
perfect subfield is perfect. The two fields may lie in independent universes.
Choose the exponential characteristic `p` of the source and transport it
along the injective algebra map. This includes characteristic zero, where
`p = 1`. Frobenius has distance equal to the `p`th power of the original
distance. The proof establishes that it is uniform inducing, so its range
is complete and closed. Perfectness of the dense source puts the image of
that source in the Frobenius range. The range is therefore dense, hence all
of the target, which proves perfectness.

## Algebraic closedness of a dense extension

`isAlgClosed_of_denseRange_nontrivial` treats a complete nontrivially normed
ultrametric field with a dense algebraically closed subfield. The proof is
adapted from Jiedong Jiang's Apache-2.0 Mathlib module
`Mathlib.Analysis.Normed.Field.Dense`, at Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; the Lean header preserves attribution.
The Mathlib theorem uses characteristic zero for separability. Here the
preceding lemma supplies perfectness of the target, which supplies the same
separability for every irreducible polynomial.

For a monic irreducible polynomial over the target, pass to its splitting
field with the spectral norm and fix a root. The minimum distance from that
root to its other conjugates gives a positive Krasner bound. Approximate
the polynomial by a monic polynomial over the dense subfield. Continuity
of roots supplies a sufficiently close root of the approximating polynomial.
Since the source is algebraically closed, this root lies in the target.
Krasner's lemma then puts the original root in the target.

`isAlgClosed_of_denseRange` also covers a trivial norm. Mathlib's dichotomy
gives either a discrete topology or an equivalent nontrivially normed field
structure. In the discrete case, density makes the injective algebra map
surjective. Pulling a polynomial back along the resulting ring equivalence
and transporting a root proves algebraic closedness. This argument works
across independent universes.

## Construction and chosen structures

`exists_completeAlgebraicallyClosed_extension` starts with the algebraic
closure `E` of `K` in the same universe. Its spectral algebra norm extends
the norm of `K` and is nonarchimedean. Nonarchimedean domination gives a
normalized multiplicative ring seminorm below it. Since `E` is a field,
multiplicativity and normalization make its kernel zero, giving an absolute
value and a normed field structure on `E`.

The restriction to `K` is a contractive multiplicative seminorm, so
`BanachSpectrum.field_apply` identifies it with the original norm. This
gives a `NormedAlgebra K E` structure. The completion of `E` inherits the
ultrametric inequality by density and is algebraically closed by
`isAlgClosed_of_denseRange`. Its scalar structure is the completion scalar
structure induced from this normed algebra.

`CompleteAlgebraicClosure` chooses a witness to this proved existence
statement. Its field, ultrametric, completeness, algebraic closedness, and
normed algebra instances are chosen successively from that same witness.
Thus the algebraic and metric structures used by the conclusion are
coherent. The final norm identity is the usual norm identity for a normed
algebra into a normed field.
