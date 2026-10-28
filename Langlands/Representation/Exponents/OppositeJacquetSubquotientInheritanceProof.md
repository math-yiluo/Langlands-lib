# Refined opposite exponents through arbitrary Jacquet subquotients

Author: Worker 514.

The theorem
`Langlands.glOppositeJacquetSubquotientExponentInheritance.{uField,uSource,uSubquotient}`
proves exactly the published proposition
`Langlands.GLOppositeJacquetSubquotientExponentInheritanceStatement.{uField,uSource,uSubquotient}`.
The field, source carrier and arbitrary subquotient carrier have independent
universes. The theorem preserves the actual normalized opposite quotients,
every block shape and refinement, and the supplied character without inversion
or conjugation.

This is a derived internal proof of the published algebraic inheritance
statement. Its provenance is the decomposition into exactness, normalized
transitivity, flattening and full-dual spectral inheritance described in the
statement's paired Markdown. It uses those published constructions and proof
theorems by import. It makes no further claim about the original literature.

## Exactness on the actual subquotient

Write `O := CuspidalJacquetMultiplicity.oppositeJacquet T C A`.
The statement supplies an invariant subspace `U` of `O` and a surjective
intertwiner `q : U → S`. The proof bundles the actual inclusion as `i`.
`Parabolic.isAdmissible_standardOppositeJacquet` gives admissibility of `O`
from that of `A`, and its smoothness component supplies the hypothesis for
`T.normalizedRefinedOppositeJacquetMap_injective`. Thus the descended map
`iq` from the refined opposite quotient of `U` into that of `O` is injective.
No smoothness or admissibility assumption on `S` is used.

The descended map `rq` of `q` is surjective. Given a refined class of `S`,
`refinedOppositeJacquetMk_surjective` supplies a representative in `S`;
surjectivity of `q` lifts it to `U`. The refined class of that lift maps to
the required class by the defining representative formula. This directly
proves the surjection needed here, without imposing any additional
right-exactness premise.

## Normalized comparison and the invariant range

`Parabolic.normalizedOppositeRefinementTransitivity` supplies `Et`, the
equivariant linear equivalence from the refined opposite quotient of `O`
to the composed opposite quotient of `A`.
`Parabolic.flattenedOppositeJacquetComparison` supplies `Ef`, the equivariant
linear equivalence from that composed quotient, pulled back along
`flattenedLeviEquiv`, to the standard opposite quotient for `C.flatten D`.
Both are the published comparisons of the actual normalized actions. The
proof uses their equivariance and bijectivity; their additional representative
compatibility conclusions are not needed.

The homomorphism `scalars` sends a flattened block-scalar tuple through
`(C.flatten D).blockScalarLevi` and then `flattenedLeviEquiv`. Restricting the
refined action on `U` along it gives the representation `R`. Composing
`iq`, `Et` and `Ef` gives an intertwiner
`J : R → T.splitCentreOppositeJacquet (C.flatten D) A`.
Its equivariance follows successively from the three maps' intertwining
identities. It is injective since `iq` is injective and both comparisons
are equivalences.

The actual subrepresentation `J.range` is therefore invariant under the
flattened block scalars. `LinearEquiv.ofInjective` identifies the refined
quotient of `U` with this range by a linear equivalence `e`. The identity
`he` proves that `e` respects the scalar action, using the equivariance of
`J` and equality of subtype elements.

## The nonzero scalar quotient and spectral detection

Surjectivity of the refined quotient map converts the statement's
representative-wise equation for `φ` into the equation `heigen'` for every
vector of the refined opposite quotient of `S`.
Define the linear functional on the invariant range by

```text
f = φ ∘ rq ∘ e⁻¹ : J.range → ℂ.
```

A nonzero linear functional to a field is surjective. Thus `φ ≠ 0`,
surjectivity of `rq` and bijectivity of `e` make `f` surjective, in particular
nonzero. The identity `he`, equivariance of `rq` and `heigen'` prove
`f(a · u) = ψ(a) • f(u)` for every block-scalar tuple and range vector.
This is an actual nonzero one-dimensional scalar quotient of the invariant
subspace; no equivariant extension to the ambient Jacquet module is chosen.

`glDualJacquetFiniteness`, applied to `A` and the flattened shape, gives
spanning of the full algebraic transpose dual by the generalized components
indexed by `T.IsDualJacquetExponent (C.flatten D) A`. Only its spanning
conclusion is needed here. The transpose action is definitionally the action
in `T.splitCentreDualJacquet (C.flatten D) A`.
`scalarSubquotientDualSpectrum` applied to `J.range`, the nonzero quotient
`f` and this indexing predicate yields occurrence of the same character `ψ`.
That published algebraic theorem uses surjective restriction of full duals
and independence of generalized weight spaces, rather than an equivariant
extension of an eigenfunctional. The final pair uses the given open-kernel
hypothesis and the detected nonzero exponent-one space.

## Dependency and scope audit

The six direct imports are the target statement and the published exactness,
transitivity, flattened-comparison, full-dual finiteness and scalar-subquotient
proof modules. The finiteness proof also imports the published standard
opposite admissibility proof used above. Their project import closure contains
159 modules. Its only modules with `Tempered` in their names are
`Classification.TemperedSupportStatement`,
`Classification.TemperedInductionStatement` and `Classification.Tempered`.
These supply ambient definitions and proposition interfaces through
`DualJacquetStatement`; no tempered-classification proof is imported or used.
In particular, the ordinary tempered-support proposition is present as an
unused definition in that ambient statement module, not as a premise or
proved ingredient of this theorem.

The implemented proof uses no weakly critical refinement or support theorem,
critical-to-minimal equivalence, tempered discrete-series support, tempered
block exhaustion, unitarity, genericity, regular exhaustion, or equal-exponent
grouping. Its ingredients do not consume the downstream analytic
class-exponent or scalar-layer temperedness conclusions. The statement pair
and its imported pairs are unchanged.

The proof adds no irreducibility, admissibility, unitarity, central character,
tensor decomposition, finite dimension or finite length hypothesis on `S`.
It covers the unrefined case by the same construction. It proves algebraic
opposite dual-exponent inheritance only; analytic estimates and temperedness
remain separate conclusions.
