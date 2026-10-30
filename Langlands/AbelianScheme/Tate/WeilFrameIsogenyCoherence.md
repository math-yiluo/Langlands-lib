# Coherence of actual Weil-compatible frame isogenies

Worker 142. This derived unit constructs direct composite and inverse transport
equivalences for the full and away Weil-compatible frames of actual abelian
schemes over a common quasi-separated base. It uses the same constructed duals,
dual geometry, inverse Poincare evaluations, integral dual-valued maps and
rational algebra actions as `WeilFrameIsogeny`. The intermediate endpoint data
are shared in the composite. Dual-map additivity is explicit for each ordered
pair used in the calculation.

For rational isogenies `e : A -> B` and `f : B -> C`, assume that they intertwine
the specified algebra actions, and that their actual rational dual pullbacks
satisfy `e^vee lamB e = q lamA` and `f^vee lamC f = r lamB`, with rational units
`q,r`. The definitions `weilAdelicFrameIsogenyComp` and its prime-to counterpart
apply the existing compatible-frame transport to `e.trans f` with multiplier
`q*r`. The required multiplier equation is proved by
`IsRationalDualPullbackMultiple.comp`; the algebra-intertwining equation is
proved by `rationalIntertwines_comp`. Thus neither compatibility equation for
the composite is an additional assumption. Extensionality on equivalences,
compatible-frame subtypes and linear equivalences reduces equality with
successive frame transport to `rationalHomMap_comp`. The first map applies
`e`, and the second applies `f`.

The identity-frame laws use the actual identity isogeny, its algebra
intertwining law and the derived unit multiplier equation
`IsRationalDualPullbackMultiple.id`. Extensionality then reduces them to
`rationalHomMap_identity`. The inverse definitions apply the existing transport
to `e.symm` with multiplier `q^-1`; the geometric equation is the previously
proved `IsRationalDualPullbackMultiple.inv`, and the algebra equation is
`rationalIntertwines_inverse`. The inverse-compatible-frame equivalence equals
the inverse of the forward equivalence by extensionality: both underlying
maps are the actual rational Tate map of `e.inv`.

The named finite Weil transition and rational Weil functoriality inputs remain
explicit in these constructions. The same scalar comparison is used for
modules and the actual Tate twist; the away version uses the coupled away
comparison and orders coprime to an arbitrary natural modulus. These laws do
not require choosing roots of unity or a twist trivialization. The integral
dual-valued maps are not asserted to be polarizations. No frame nonemptiness,
nondegeneracy, finite-dimensional PEL specialization, topology or fixed-level
coherence is asserted in this unit.

The provenance is restriction of the existing actual Tate isogeny maps to the
already constructed compatible-frame subsets, with the actual Hom0 dual
pullback coherence laws supplying the geometric equations. Harris--Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), printed
p.18 and Section III.1, pp.90--92, supplies the rational-isogeny convention and
the motivating PEL level and isogeny relation. The present calculations are
derived Library consequences, rather than additional geometric existence
theorems attributed to that passage. No source-specific errata note was found
in the consulted project notes.
