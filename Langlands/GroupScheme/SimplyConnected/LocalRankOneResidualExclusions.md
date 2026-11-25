# Exceptional residual indices and conditional removal of higher B

This internal assembly connects the general, unproved
`TypeBOddQuadraticPresentationStatement` with the concrete residual patterns
of the local rank-one enumeration. Every theorem remains conditional.
All fields, residue characteristics, and universe parameters are retained.

`TitsIndexData.HasExceptionalResidualRankOneIndex` is a predicate on an
actual `TitsIndexData` over any field: it is the disjunction of
`HasRankOneG2Index` and `HasRankOneD4InnerOrNoFixedLeafIndex`. It records the
precise two remaining patterns, including their entire Cartan matrix,
distinguished vertices and full absolute-Galois star conditions. Defining
this predicate neither realizes these patterns nor asserts their exclusion.
It packages the conclusion of the conditional reduction below.

`TitsIndexData.not_hasRankOneHigherBIndex_of_oddQuadraticPresentation`
assumes that general presentation and an actual local simply connected,
absolutely almost-simple group of split rank one. It excludes
`d.HasRankOneHigherBIndex`. The proof extracts its full type-B numbering and
rank at least three, then applies the conditional quadratic dimension
contradiction. Its singleton marking and trivial full star action are
not needed for this contradiction; they remain part of the excluded
concrete index predicate.

`localRankOneTitsIndex_or_G2_or_D4_of_oddQuadraticPresentation` takes four
explicit structural premises: actual semisimple component-factor
realization, the norm-one automorphism/opposite-algebra statement, E-type
kernel centre movement, and the general odd-quadratic type-B presentation.
For an actual irreducible Cartan type it applies the existing three-residual
reduction and rules out its higher-B branch by the first theorem. Its
conclusion is the disjunction of the five exact desired index alternatives
and the G2 or inner-or-no-fixed-leaf D4 pattern. These predicates preserve
the entire actual Cartan matrix, distinguished subset and required full
absolute-Galois star conditions.

`localRankOneTitsIndex_of_oddQuadraticPresentation_and_remaining_inputs`
adds absolute Cartan classification and two separate universal exclusions:
the concrete G2 residual and the concrete inner-or-no-fixed-leaf D4
residual, for every local simply connected absolutely almost-simple group
of split rank one. It returns the exact published
`LocalRankOneTitsIndexStatement.{u}`. The proof obtains the irreducible
Cartan type, applies the preceding disjunction, and contradicts either
remaining branch with the corresponding supplied exclusion.

The provenance is internal composition of the imported conditional
three-residual reduction and the conditional type-B dimension argument.
The underlying local anisotropic type-A theorem is already proved and
enters through the imported component-factor reduction. This file proves
none of its structural premises or its two remaining exclusions, and
therefore supplies no unconditional local rank-one enumeration. It uses
neither the downstream group-model classification nor local Kneser--Tits.
