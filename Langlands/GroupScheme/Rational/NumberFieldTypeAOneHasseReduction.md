# The Hasse kernel for forms of one-vertex groups and their Weil restrictions

A simply connected absolutely almost-simple group with one absolute simple
vertex has inner type `A₁`. Its single Cartan entry is two and every star
permutation fixes that vertex. `isTrivial_typeAOne_of_reducedNormLocality`
therefore uses the published inner type A reduction to reduced-norm locality.

A separable scalar extension embeds into the separable closure. An actual
isomorphism over the extension then identifies the geometric root data in the
two Tits indices over that closure. A Weyl group element corrects the
transported simple system to the other chosen simple system. The resulting
equivalence of vertices preserves all Cartan entries.
Simple connectedness and absolute almost-simplicity also transport and
reflect across the extension. These comparisons let
`isTrivial_typeAOneForm_of_reducedNormLocality` handle a form of a supplied
one-vertex group.

The Weil restriction result uses the actual cocycle transfer to the extension
field and tests the transferred cocycle on a finite Galois refinement there.
Local triviality is preserved at every place by the transfer. Triviality on
that refinement reflects to the original cover of the smaller field.

The arithmetic input is the reduced-norm local-to-global statement from
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7,
equation (6.39), printed p. 357. The use of the two kinds of one-vertex groups
in the trialitarian argument is in §6.8, printed pp. 374–375.
