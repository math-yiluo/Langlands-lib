# Finite étale geometry of the supplied-family full-level parameter

For an actual supplied abelian scheme `A` over `S`, positive `n`
invertible in the global sections of `S`, and any natural number `g`,
`torsionTupleScheme_finiteEtale` proves that the structure map of the
ordered torsion tuple scheme is finite and étale.

The proof uses the existing finite étale multiplication-kernel theorem
for each of its finitely many factors. The published morphism property
`finiteEtale` has composition, base-change, identity and cancellation
properties. Consequently its over-category has finite limits, preserved
by the forgetful functor to `Over S`. The product comparison isomorphism
transfers the finite étale property to the exact chosen product used by
`torsionTupleScheme`.

The full-level locus is already proved clopen in this tuple scheme.
Its inclusion is an open immersion with closed range and therefore a
closed immersion. This proves
`fullLevelParameterInclusion_isClosedImmersion`. Finiteness of this
inclusion and its being étale, followed by composition with the tuple
structure map, prove `fullLevelParameterScheme_finiteEtale`.
`fullLevelParameterFiniteEtaleCover` packages this exact parameter as an
actual object of the category `Cover S` of finite étale schemes over `S`.
Forgetting this property gives the original parameter object by
definition. The locally noetherian conclusion over a locally noetherian
base follows from local finite type.

The provenance is internal: the argument combines the existing actual
parameter construction, finite étale torsion theorem, clopen full-level
locus and published categorical finite-limit machinery. It asserts
finite étale geometry for full levels on one supplied family. It makes
no assertion of nonemptiness, surjectivity, numerical degree, abelian
automorphism rigidity or existence of an ambient moduli scheme.
