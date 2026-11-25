# The unique relative Levi containing a prescribed maximal torus

This proof composes the constructions of `TorusDynamicCover` and
`TorusLeviPresentationReduction` and of the modules they build on.

`Langlands.GroupScheme.relativeTorusLevi.{u}` proves exactly
`Langlands.GroupScheme.RelativeTorusLeviStatement.{u}`. For every scheme
`S`, reductive group scheme `G/S`, relative parabolic inclusion `i : P ⟶ G`,
and closed relative torus `t : T.toGrp ⟶ P` maximal on every residue fibre
of `P`, there is an actual relative Levi subgroup of `P` containing the
range of `t`. Every relative Levi containing that range has the same
subgroup functor range, with equality on every relative test scheme.
The theorem has no additional hypotheses and is universe polymorphic.

The implemented proof applies the published implication
`RelativeLevi.relativeTorusLevi_of_dynamicPresentation`. Its sole premise
is the existence of étale local dynamic presentations along the prescribed
torus. For arbitrary data under that premise,
`RelativeLevi.torusDynamicPresentationCover` constructs an actual small
étale cover and a `TorusDynamicPresentation` on each member. The proof
extracts each presentation's `cocharacter` and `represents` fields.
These are cocharacters of the direct pullbacks of the original torus,
and their composites through the pulled-back `t` and `i` represent the
actual pulled-back parabolic on every test scheme, including monomorphy.
The cover constructor needs fewer hypotheses, so the original closedness
hypothesis on `t` is unused in this extraction.

The imported reduction constructs the relative unipotent radical on this
same cover, obtains unique local dynamic Levi witnesses, and uses effective
descent and equality of closed subgroup ranges to produce the global Levi,
torus containment and uniqueness. The present theorem discharges its
presentation premise with the published cover construction.

This proof is an internal composition of Library results. The target's
source correspondence with Conrad (2014), Proposition 5.4.5, is recorded in
`TorusLeviStatement.md`; the implemented route is described above and does
not add a separate transcription claim.
