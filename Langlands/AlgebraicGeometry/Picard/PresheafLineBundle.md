# Coherent line bundles on presheaves of families

For a scheme `S` and a presheaf `F : (Over S)ᵒᵖ ⥤ Type v`,
`PresheafLineBundle F` assigns an actual locally free sheaf of rank one to
every family `x ∈ F(T)`. For every slice morphism `a : T → U` and equality
`F(a)(x) = y`, it specifies an isomorphism from the pullback of the bundle of
`x` to the bundle of `y`. The isomorphisms obey the identity law and the
composition law, using the actual `LineBundle.pullbackId` and
`LineBundle.pullbackComp` comparisons. In particular, these are coherent
isomorphisms of sheaves, rather than equalities of isomorphism classes.
The equality in a morphism of families is explicit; its proof carries no
additional data.

This is an internal cartesian line-bundle interface on the category of
elements of `F`, written directly in slice-presheaf terms. It uses the
published actual line-bundle and pullback constructions. It makes no
assumption that `F` is small, a sheaf, or represented, and permits `v` to
differ from the universe of `S`.

`reindex` pulls this data back along a natural transformation of presheaves.
`baseChange` restricts the parameter base along any scheme morphism.
Their coherence laws are inherited from the original data.

If `e` is a supplied representation of `F` by `M`, `universal e` evaluates
the bundle on its universal family. `universalPullbackIso` identifies its
pullback along each classifying morphism with the bundle of the classified
family, by the naturality of `e`.

`transition` identifies the two pulled-back line bundles of families whose
restrictions to a common test scheme agree. `transition_self` and
`transition_trans` prove the identity and cocycle laws on that test scheme.
The latter proof cancels the middle cartesian isomorphism with its inverse
and composes the equality transports between the restricted families.

These are derived definitions and proofs. They provide data for polarized
descent; they neither construct a polarization for a particular moduli
problem nor prove effective descent of parameter schemes.
