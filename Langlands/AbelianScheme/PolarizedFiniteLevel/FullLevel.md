# Ordered full finite level on actual abelian schemes

This module implements the ordered full-level part of Mumford, Fogarty and
Kirwan, *Geometric Invariant Theory*, third edition (1994), Chapter 7,
Section 2, Definition 7.1, printed p.129 / one-based PDF p.142.
The registered original is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
retained as
`literature/Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition (1994), Chapter 6.pdf`.
The filename describes only part of the complete book. No source-specific
errata note was found in the checked project, workspace, or Library locations.

`SectionTuple A g n` is an ordered `Fin (2*g)`-tuple in the existing module
`GroupScheme.Tate.Level A.toGrp (Over.mk (𝟙 S)) n`. These are actual global
sections killed by the actual multiplication morphism. `fibreTuple` restricts
all these sections to the specified field-valued point. `IsFull` requires
that at **every** algebraically closed field-valued point this same ordered
tuple is a basis over `ZMod n`. `FullLevel` bundles the tuple and this property.
The definition does not assert global-section freeness, existence of such a
tuple, or merely the separate existence of unrelated fibre bases.

The definitions work in any fixed scheme universe `u`. They make sense for
every natural `n`; the ordinary moduli application restricts to `3 ≤ n` and
to bases on which `n` is invertible, as in the source. They do not implement
the source's special convention for level one.

`FullLevel.fibreCoordinates` is a residue-linear isomorphism from
`Fin (2*g) → ZMod n` to the actual torsion module at each geometric point.
Its formula is precisely the sum of coefficients times the restricted
sections. In particular it carries each standard basis vector to the
corresponding restricted section.

The transport results are internal consequences of the definition and
the existing actual torsion APIs. `levelIsoLinear` wraps postcomposition
by an actual abelian-scheme isomorphism and its inverse. Restriction
commutes with this map by associativity of actual section composition.
Mapping the fibre basis along that linear equivalence proves
`IsFull.mapIso` and constructs `FullLevel.mapIso`.

`pullbackTuple` restricts a global torsion section to the new base and
uses the inverse actual torsion pullback adjunction to regard it as a
section of the pulled-back abelian scheme. `fibreTuple_pullback` proves
its formula at each geometric point of the new base. Naturality in
the test scheme and associativity identify this with restriction of
the original section at the composite point. Mapping the original fibre
basis along the inverse residue-linear base-change equivalence proves
`IsFull.pullback` and constructs `FullLevel.pullback`. The base morphism
is arbitrary. Neither a numerical torsion-rank theorem nor an existence
theorem for full-level structures is used.
