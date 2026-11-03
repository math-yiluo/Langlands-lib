# Vector classification targets for smooth commutative groups

This pair states two structural prerequisites; it proves neither one.
All fields and group schemes range over arbitrary universe `u`.

`CommutativeUnipotentVectorCharZeroStatement` says that a smooth connected
commutative affine unipotent group over an algebraically closed field of
characteristic zero is a finite-dimensional vector group. This isolates the
classical structural input used in Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), proof of Theorem 3.3.11, printed p.115 / PDF
p.141: the last nontrivial descending-central-series term `N` is commutative,
and in characteristic zero the proof takes `Z = N` as its central vector
subgroup. That passage uses the input without proving the general
classification there. Our statement requests the general commutative result,
which is independent of that particular central-series construction. Its
algebraically closed scope is sufficient for the present application.

`SmoothCommutativePTorsionVectorStatement` is the final, connected
algebraically closed clause of CGP Lemma B.1.10, printed pp.565–566 / PDF
pp.591–592. It says that a smooth connected commutative affine group killed by
the characteristic prime `p` is a vector group. The exponent premise is
`x ^ p = 1` on every scheme over the ground field, so it asserts the actual
group-scheme multiplication law, including points over nonreduced and
nonaffine tests. No unipotence hypothesis is added to this second statement.
The source proves this classification using a composition series by additive
groups and the length-two Witt extension. Those arguments remain proof
obligations here; the statement alone supplies none of them.

The common conclusion uses the existing `IsVectorGroup`: for some natural
number `n`, the actual point group on every scheme test has a multiplicative
equivalence with the additive group of `n` global functions, natural under
all test morphisms. This is the functorial form of being isomorphic to the
standard vector group in CGP Definition A.1.1 and Example A.1.2, printed
p.466 / PDF p.492. Dimension zero and the trivial group are allowed. Smoothness
is locally of finite presentation, and affineness makes the structural map
quasi-compact, so the group is of finite type as in the cited source.

The characteristic-zero statement retains the Library's actual
`IsUnipotent`, defined by nonzero fixed vectors in every nonzero
finite-dimensional matrix representation. CGP Definition A.1.3 and
Proposition A.1.4, printed p.467 / PDF p.493, instead describe composition
series and triangular presentations. Establishing the classification for the
Library predicate, including any needed comparison with those formulations,
is part of the requested proof; no comparison theorem is assumed by this
pair. The commutative group objects and their laws are the existing actual
scheme constructions.

`CommutativeVectorClassificationStatement` is just the conjunction of the two
targets. Torus actions and equivariant linear structures are separate inputs.
These statements neither produce a central subgroup nor establish the exact
ordered-product theorem.

Source: registered `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The source locations above were read directly. A bounded check of the current
Library's notes and wiki paths found no CGP-specific errata file; the registered
author-books-page navigation note records only that no dedicated errata link
was found in that section, not a claim of global absence.
