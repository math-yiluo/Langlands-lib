# An ample diagonal correspondence from the difference map

This module proves the exact arbitrary-universe proposition
`Langlands.AbelianScheme.FieldAmpleDiagonalCorrespondenceStatement`.
It uses actual line bundles, scheme-module pullbacks, tensor products,
and isomorphisms. The supplied ample line bundle has no symmetry condition.

For an ample line bundle `L` on `A` over a field `K`, choose a tensor
inverse `M` using the published line-bundle dual evaluation theorem.
On the actual scheme square let `p1` and `p2` be its two projections,
let `d = p1 - p2`, and construct

`D = (d* M tensor p1* L) tensor (-p2)* L`.

Here the stars denote actual pullbacks. On the first axis the first two
factors evaluate to the structure sheaf, and the last factor is constant.
On the second axis the middle factor is constant and the other two
factors are the inversion pullback of `M tensor L`, hence trivial.
Every constant factor is pulled back from a line bundle on `Spec K` and
is trivial by `fieldLineBundleTriviality`.

On the diagonal the difference map is the constant map at the group unit.
Its pullback of `M` is trivial, and the other factors give the actual
isomorphism `diagonal* D ≅ L tensor [-1]* L`. Inversion is an involution,
so is an isomorphism and in particular a closed immersion. The published
`closedImmersionPullbackAmple` proves that `[-1]* L` is ample;
`ampleTensor` then proves ampleness of the actual diagonal pullback.

The construction is an internal derived alternative to the cube-based
motivation in the statement's Markdown. It needs no theorem of the cube,
multiplication formula, projectivity, algebraic closure or characteristic
restriction. The separately owned field-cube workflow is not duplicated.
The motivating Milne original (registered source
`milne-abelian-varieties-1986-author-2022`, author revision January 2, 2022)
was checked on p.9, including the balanced signs of Corollary 6.4 and
the nonsymmetric formula in Corollary 6.6; those results are not used in
this proof. Worker 421 designed and implemented the difference construction.
Worker 59 checked the construction, the actual second-axis cancellation,
the exact target, and the types of the ampleness dependencies as a coauthor.
Independent semantic review remains separate from this coauthor check.
