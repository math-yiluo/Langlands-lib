# Finite and local character models of actual automorphic Hecke lines

This internal construction identifies the existing actual automorphic line
of a finite-order Hecke character with explicit finite adelic and finite local
scalar representations. The number field has an arbitrary universe, the
matrix rank is any natural number, and the coefficient field is complex.
Finite order remains an explicit hypothesis on the supplied character.

`finiteModel` is the existing `characterRepresentation` of the published
continuous finite adelic determinant character. Its carrier is complex
scalars. `finiteModelEquiv` uses the already constructed scalar equivalence
onto the actual embedded line, and its intertwining equation is precisely
the proved finite operator formula. `finiteFormEquiv` composes this with the
existing faithful equivalence onto the finite invariant image in actual forms.
The inclusion theorem identifies its image with the constructed form
`g ↦ χ(det g) * c`. These are actual equivalences, with no occurrence or
factorization premise.

`localModel` uses the actual determinant character pulled back along the
one-place inclusion into the finite adelic group. The local action formula
specializes the finite one. `localModelEquiv` consequently identifies this
scalar representation with the whole local restriction of the actual line.
`localFormEquiv` composes it with the existing faithful local form equivalence.
Its inclusion again recovers the same actual form. These maps intertwine
the respective entire groups; they are algebraic representation equivalences.
No topology on the representation carrier or continuity of these linear maps
is asserted.

Smoothness of both scalar models is reflected by their injective
intertwiners into the already proved smooth actual actions. The actual finite
and local actions are irreducible: their carriers have dimension one, so the
published dimension-one theorem for smooth representations applies.
Admissibility uses the published all-open-subgroups convention. The inverse
scalar equivalence embeds the actual carrier into the finite-dimensional
scalar field, and every fixed-vector submodule is therefore finite-dimensional.

All these claims are internal consequences of the published realization,
restriction, scalar twist and smooth representation APIs. There is no new
original-literature identification. No prescribed-character extension,
classification of rank-one cusp forms, restricted tensor factorization,
almost-everywhere unramified assertion, Hecke eigenvalue computation or
local-global Langlands comparison is proved or assumed. Irreducibility of
the whole local restriction is specific here to this actual dimension-one
example; it is not asserted for arbitrary automorphic representations.
