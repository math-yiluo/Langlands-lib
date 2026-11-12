# The finite real-image input for absolute upper reciprocity

Author: Worker 5168.

This internal construction identifies the exact finite arithmetic input still
needed for the published `AbsoluteUpperReciprocityTheorems.{u}`. Its declaration
`absoluteUpperReciprocityFiniteRealEquiv` is an equivalence between the proof
types of that five-part absolute proposition and
`FiniteReciprocityRealUnitImages.{u}`. The construction does not assert either
proposition unconditionally.

All primes, fields in arbitrary universe `u`, base topological realizations,
continuous reciprocity candidates satisfying the geometric relation, finite
abelian extensions and their supplied realizations remain quantified exactly
as in the published statements. Both conductor clauses retain every continuous
complex quasicharacter. Images are literal subgroup images.

## Implemented maps

`absoluteUpperReciprocityTheorems_of_finiteRealImages` constructs the full
absolute conjunction from the finite real-image theorem. It applies the
published `absoluteReciprocityImages_of_finite` reduction. Both of that
reduction's arithmetic hypotheses are discharged, without new assumptions, by
the published theorems
`Langlands.Ramification.HerbrandBridge.absoluteUpperFiniteImage` and
`Langlands.Ramification.HerbrandBridge.absoluteUpperInertia`. Thus the result
includes natural and real upper-unit images and the actual inertia comparison.
The published
`absoluteReciprocityConductorConsequences_of_realImages` then supplies the
conductor-level and last-break equivalences for all continuous complex
quasicharacters.

The image reduction uses compactness and finite abelian restrictions to
identify closed literal subgroup images. The conductor reduction uses
injectivity of each normalized reciprocity candidate and the least unit level
of triviality. Those arguments are reused through their published proofs;
they are not reimplemented here.

`finiteReciprocityRealUnitImages_of_absolute` takes the real-image conjunct of
the full absolute proposition and maps its equality under restriction to each
finite abelian extension. The published absolute finite-image theorem
computes the restriction of the absolute abelian upper group.
`upperRamificationGroup_eq_of_realization` replaces the canonical extension
realization by the arbitrary supplied one. Composition of subgroup images is
the finite reciprocity image in the target statement.

These two functions are the maps of
`absoluteUpperReciprocityFiniteRealEquiv`. Their inverse laws follow from
proof irrelevance, since both sides are propositions.

## Provenance and remaining obligation

The construction is derived entirely from the named published Library results
and the published statement definitions. It introduces no external
mathematical input and changes none of their Lean or Markdown files.

This is a reduction, not an unconditional proof of the assigned absolute
target. The finite real-image theorem remains necessary; the construction
shows it is also sufficient with the now-published absolute arithmetic.
Once that finite theorem is proved, the forward helper gives an exact theorem
of type `AbsoluteUpperReciprocityTheorems.{u}` with no additional hypotheses.
