# Enumeration of actual torsion by a supplied ordered full level

This internal construction starts from the published ordered full-level
definition. It does not assert existence of a level structure.

`enumerateTuple` forms all finite residue-linear combinations of the supplied
global torsion sections. The coefficient tuples are functions from
`Fin (2*g)` to `ZMod n`. Restriction of this enumeration to any geometric
point is exactly the published `FullLevel.fibreCoordinates` equivalence.
Consequently the restricted enumeration is bijective. The finite-sum
construction also commutes with every actual abelian-scheme homomorphism and
every actual base morphism, through the existing torsion comparisons.

`torsionSection` uses the actual multiplication-kernel universal property to
turn each enumerated level element into a global section of the torsion
scheme. Its geometric coordinate formula proves that each geometric
torsion point arises from a unique coefficient tuple.

All these results hold for every natural level, including zero. They require
neither positivity nor invertibility of that level. The bijection concerns
restriction to each geometric point; no bijection between coefficient tuples
and all global torsion sections is asserted over an arbitrary base.

The construction and proofs are internal consequences of `FullLevel`,
`FibreDetection`, and the actual kernel and pullback APIs. No numerical
torsion-rank result, faithfulness theorem, canonical projective embedding or
moduli representability result is assumed or proved here.
