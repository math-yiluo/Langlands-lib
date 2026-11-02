# Finite type systems and finite tuple tails

This internal adapter connects the published stable-subalgebra system and
open-extension construction in the proof route for Stacks Proposition 70.8.1,
Tag 07SU. Its provenance is the registered collection
`stacks-noetherian-approximation-2026-11-01`, including Tags 07TR, 07TT, 07TU
for stable subalgebras and 07RN for affine open models. The tuple filtration
comes from Tag 0BBN in `stacks-stratification-2026-11-02`. All mathematics here
is derived from the imported, proved interfaces.

`IsCartesianHom.stableDiagram_locallyOfFiniteType` retains finite type over
the integers at every stable level of a cartesian comparison to an affine
finite type relation. The finite type property of the base coordinate ring
follows from the affine-open sections theorem. Transitivity of finite type
gives it for each finitely generated stable subalgebra, and the terminal-spectrum
lemma translates it to the object scheme of the corresponding stable level.

`FiniteTypeCartesianSystem E` records a cofiltered diagram of actual cartesian
relation morphisms, a cone whose point is the given relation `E`, and its
object-scheme limit property. Each level has compact object and arrow schemes,
an object locally of finite type over the absolute terminal scheme, a
quasi-separated arrow scheme, and a separated source map. Object transition
maps are affine. The structure does not assert that the level objects are
affine. Its `cone` is the cone formed from the recorded comparison.

`FiniteTypeCartesianSystem.nonempty_firstLevel_openExtension` applies the
proved open-extension theorem to these data. It additionally assumes a
separated source at the limit, affine nonidentity arrows at the limit, and
an open immersion of the limit object into an affine scheme.

`AffineFiniteTypeFirstLevel.system` constructs this system from an affine
relation with one affine finite type first level. It uses the existing stable
diagram and its cone at the original relation. The first level is Noetherian,
so the stable index is cofiltered and the original object is the limit.
All level object and arrow schemes are affine; compactness,
quasi-separatedness, separation of sources, and affineness of transition
maps follow from this. The preceding finite type lemma supplies absolute
finite type at every level.

`nonempty_affineFiniteTypeFirstLevel_tupleTail` assumes a system on the
restriction of a finite tuple tail to the next invariant threshold, with
`p < N + 1`. The existing recovery theorem proves that its nonidentity arrows
are affine. The open-extension theorem gives a first level on the ambient
tail object. Composing with the inverse of the actual recovery isomorphism
gives the cartesian comparison from the whole finite tuple tail. The system
on the next-threshold restriction is an input here; constructing it by a
change of quotient charts and completing descending induction remain
separate obligations.
