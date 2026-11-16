# The split coroot torus quotient over a ring

This internal construction supplies the lattice and target torus in Brian
Conrad, *Reductive group schemes* (2014), Theorem 5.3.1, pp.160–163
(registered source `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
The coroot annihilator is the character lattice of the proposed quotient
of the maximal torus by the minimal subtorus containing every coroot.

`RootDatum.corootEvaluation` evaluates a character on a selected family of
coroots. Its kernel is the published `RootDatum.corootAnnihilator`.
For a finite root index set, the quotient lattice is isomorphic to the
image of this evaluation map in a finite free integer module; the theorem
`free_quotient_corootAnnihilator` uses this isomorphism and the freeness of
submodules over the principal ideal domain of integers.

For a coordinate split torus, `RelativeDerived.cocenterLattice` is the
annihilator of all coroots. `corootQuotient` is its actual diagonalizable
group scheme over the supplied ring. The lattice is a submodule of a
finite free integer module and is therefore free of finite rank. A choice
of basis identifies this group scheme with a finite split torus, proving
`isSplitTorus_corootQuotient` and `isTorus_corootQuotient` over every
commutative ring. These results supply the target torus; this module does
not yet construct a homomorphism from the ambient reductive group.
