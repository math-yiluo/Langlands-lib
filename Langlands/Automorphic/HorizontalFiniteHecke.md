# Smooth finite actions and Hecke integration on horizontal cochains

This internal construction uses an actual number field `F`, natural matrix
rank `n`, and the existing `OperatorRealization F n`, an invariant subspace
of the actual stable automorphic functions. Its finite translation, compact
action, horizontal full-compact-equivariant alternating maps and differential
are the existing constructions. The field and coefficient module have independent universes.

The reduced complex Lie algebra is finite dimensional over `ℂ`: the real
matrix Lie algebra is the matrix space over the finite product of real and
complex infinite-place coordinates; its reduced Lie subalgebra is a subspace,
and extension of scalars to `ℂ` preserves finite generation. Local instances
use these actual spaces. No dimension bound or choice of a model Lie algebra
is added as a hypothesis.

`horizontalAlternatingInclusion` is the subtype inclusion from the existing
horizontal cochains into the actual alternating maps. It is equivariant
because finite translation postcomposes only the values.
`horizontalFiniteRepresentation_isSmooth` transfers the finite-dimensional
domain result `AlternatingCoefficients.isSmooth` through this injective map,
using the already proved smoothness of the realized finite translation.

For any complex coefficient module `V` with any representation `τ` of the
full standard infinite compact group, the finite action on `S.Space ⊗[ℂ] V`
is smooth: it acts only on the automorphic factor, and every algebraic tensor
is a finite sum of pure tensors. The analogous injective alternating-map
inclusion proves smoothness of the existing tensor horizontal cochains in
all degrees. No topology or finite-dimensionality is required on `V`.

When `n` is nonzero, `horizontalCyclesFiniteInclusion` is the existing
cycle-subtype inclusion as a bundled finite intertwiner. This inclusion and
the cycle and cohomology smoothness results specialize
`Langlands.Cohomology.Lie.Horizontal` from `HorizontalCohomologyHecke`
to the original compact submodule, conjugation representation, realized
compact representation and finite chain action. Smoothness transfers
through the inclusion's injectivity and then through the surjective existing
cohomology class projection. These are the kernels of the actual horizontal
differential and their quotients by its image boundaries, with zero
boundaries in degree zero.

Given a Borel measurable structure and a Haar measure `μ` on the actual
finite adelic general-linear group, `horizontalHeckeAction`,
`tensorHorizontalHeckeAction`, `horizontalCyclesHeckeAction` and
`horizontalCohomologyHeckeAction` integrate those same smooth finite actions
using the existing `Hecke.heckeAction`. They are nonunital complex algebra
homomorphisms from the existing measure-indexed finite Hecke algebra. Its
convolution normalization and all algebra laws are inherited, with no new
choice of measure normalization.

The actual differential, cycle inclusion and cohomology class projection
commute with these Hecke actions. The cycle and cohomology integration
constructions and the three compatibility laws specialize the generic
`HorizontalCohomologyHecke` constructions. Their proofs apply the existing
`integratedAction_intertwiner` to the corresponding original finite
intertwiner. Thus the quotient operator is induced by the same integrated
operator on cycle representatives.

The provenance is internal finite-dimensional linear algebra, smoothness
transfer, and already constructed Hecke integration. No new external-source
identification is claimed. No admissibility, finite-dimensionality of
cohomology, nonvanishing, spectral occurrence, arithmetic comparison or
existence of an automorphic realization is established here.
