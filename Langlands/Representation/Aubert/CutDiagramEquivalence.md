# Natural equivalences of signed cut diagrams

This internal construction extends `SignedCutComplex.Diagram` by
`Diagram.Equivalence`: a linear equivalence on each cut coordinate whose square
commutes with every inclusion map. The coefficient spaces of the two diagrams
may have independent universes. No new source theorem is asserted.

`totalEquiv` and `degreeEquiv` are the products of those equivalences over all
cut sets and over cut sets of a fixed cardinality. They commute with extension
by zero and restriction. Naturality and linearity show that the total
equivalence commutes with each insertion, including its unchanged exterior
coefficient `sign s i`. Summing gives the total differential square; extension
and restriction give `degreeEquiv_differential` for the homogeneous maps.

The final lemmas transport injectivity, middle range/kernel equality, and
vanishing through these actual equivalences. The exactness comparison uses the
standard commuting-square lemma for surjective, bijective and injective
vertical maps. These lemmas do not establish exactness for any diagram; their
purpose is to transfer it once established for an equivalent diagram.
