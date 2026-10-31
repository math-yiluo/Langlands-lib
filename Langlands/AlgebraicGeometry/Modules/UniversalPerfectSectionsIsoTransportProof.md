# Isomorphism transport of fixed universal representatives: proof

Author: Worker 137.

The theorem `universalPerfectSectionsIsoTransport.{u}` proves
`UniversalPerfectSectionsIsoTransportStatement.{u}` by retaining the
given complex `K`. The construction uses actual derived sections and
ordinary module pullbacks throughout.

The helper `isUniversalPerfectSectionsRepresentative_of_iso` transports
the representative predicate from an actual module `N` to an isomorphic
module `M`. Strict perfection is unchanged. The original-base comparison
is followed by the actual derived-sections functor applied to the inverse
of the coefficient isomorphism. For every scalar extension, it first
pulls back that inverse coefficient isomorphism by the usual scheme
projection, then applies the corresponding derived-sections functor.

The helper `relativeDerivedSectionsBaseChangeSchemeIso` compares derived
sections of `e.hom^* N` on the affine base change of `X` with those of `N`
on the affine base change of `Y`. Mathlib's `pullback.map` applied to the
scheme isomorphism and the two identity maps is itself an isomorphism.
Its projection equations identify the structure maps and the composite
coefficient projections. Module pullback composition combines the two
coefficient pullbacks on `X`. The published helper
`relativeDerivedSectionsIsoOfComp` then supplies the comparison through
the induced scheme isomorphism.

The main proof first constructs the representative predicate for
`e.hom^* N`. Strict perfection is inherited. The original-base comparison
is the assumed comparison followed by the inverse of
`relativeDerivedSectionsPullbackIso`. Each scalar comparison is the
assumed comparison followed by the inverse of the base-change helper.
Finally, coefficient-isomorphism transport applies the supplied
isomorphism from `M` to `e.hom^* N`.

This is an internal consequence of the published scheme-isomorphism
invariance and explicit-projection transport for actual derived
sections, together with Mathlib's pullback and functoriality APIs.
The universal representative is a hypothesis. No new representative,
smooth proper existence theorem, approximation result, or naturality of
the chosen comparison witnesses is asserted.
