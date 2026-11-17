# The canonical fppf quotient and its local scheme models

This is an internal construction from the published action, quotient, fppf
sheaf, and representability interfaces. It does not assert quotient
representability for arbitrary actions.

For a scheme action, `quotientSheaf` is the coequalizer of the action and
projection in actual fppf sheaves. Its canonical map is locally surjective
because coequalizers are epimorphisms and epimorphisms of sheaves of types are
locally surjective. For a free action, the local acting points glue by the
published `existsUnique_act_of_isFppfActionQuotient`; thus equality of quotient
images is equivalent to an actual orbit equation on the original relative
test.

`quotientWithParameter U` is the product of this quotient sheaf with the
represented sheaf of a scheme `U` over the base. The presentation by `X × U`
remains locally surjective: locally lift the first factor and keep the
restriction of the given `U`-point. Its kernel is precisely equality of the
`U`-points together with an orbit equation in `X`.

`exists_iso_quotientWithParameter` compares this presentation with a supplied
flat, surjective, locally finitely presented scheme morphism having the same
kernel on all relative tests. The published common-kernel presentation theorem
then gives an isomorphism from the supplied scheme's functor of points to the
quotient sheaf with parameter, compatibly with its class morphism.
