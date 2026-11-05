# Quotients by central maximal split tori have split rank zero

Author: Worker 1467.

The imported `subgroupIntersection a q` is the actual group-scheme pullback of the
homomorphisms `a : T ⟶ C` and `q : G ⟶ C`, over any base scheme. The following
proofs use it as the preimage of a closed split torus under a quotient.

This is an internal derived consequence of the published central extension theorem
`CentralExtensionHopfSpec.isSplitTorus_of_split` and the definitions of a maximal
split torus and split rank. It is the anisotropy part of the algebraic route
motivated by Milne, *Algebraic Groups* (2017), Exercises 12-2 and 12-6 (printed
p.252, PDF p.268), rather than an implementation of a character classification.
The original page and the complete registered errata snapshot of 2 November 2026
were read; the Chapter 12 errata do not affect these exercises.

`IsMaximalSplitTorus.split_torus_quotient_eq_zero` takes an affine group scheme
over an arbitrary field, a central maximal split-subtorus inclusion `j`, an
actual fppf quotient `q` by its full all-test range, and a closed split torus `a`
in the quotient. It proves that `a` is the trivial homomorphism.

The proof forms the actual group-scheme pullback of `a` and `q`. Its projection
to the original group is closed, so its scheme is affine. The map from the
original maximal split torus into the pullback is central and closed. The other
projection is flat, surjective and locally of finite presentation by base
change. Its all-test kernel is proved equal to the range of that lifted torus.
The central extension theorem makes this pullback a split torus. Maximality of
`j` makes the lifted torus inclusion an isomorphism. Hence the pullback's map
to the quotient is trivial. Cancellation of its flat surjective projection,
which is an epimorphism of schemes, gives the asserted equality for `a`.

`IsMaximalSplitTorus.isAnisotropic_quotient` proves split rank zero for that
quotient. For a closed copy of a finite product of multiplicative groups the
first theorem makes its inclusion trivial. Closedness lets us cancel that
inclusion, forcing every coordinate cocharacter to vanish. Composing with its
matching coordinate character makes the identity of the multiplicative group
zero, contradicting `gmEndEquiv_id`. Thus the index type is empty, as required
by `isAnisotropic_iff`.

No smoothness or characteristic restriction is imposed. The quotient map is
used schematically, with its all-test kernel equality; there is no claim of
surjectivity on rational points. This module does not construct the torus part
or finite quotient of a group of multiplicative type.
