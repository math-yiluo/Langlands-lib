# Actual comparison maps between supplied dynamic quotients

Worker 708. This internal construction works over every base scheme
`S : Scheme.{u}` and for actual group schemes `G,H` over `S`.

Given a homomorphism `f : G → H`, a cocharacter `χ` of `G`, and supplied
relative maps `q : G → Q` and `r : H → R`, assume the exact right-coset fiber
conditions for `P_G(χ)` and `P_H(χ ≫ f)` respectively on every test scheme.
Assume also that `q.left` is flat, surjective and quasi-compact. The
construction `Dynamic.suppliedQuotientMap` descends `f ≫ r` through `q` to
an actual relative morphism `Q → R`. The proof uses dynamic functoriality
`parabolic_le_comap` to check that the map is constant on `q`'s fibers.
Effective-epimorphism descent supplies the map and its factorization.
`fac_suppliedQuotientMap` states this factorization, and
`suppliedQuotientMap_unique` proves its uniqueness.

If `f` is a closed subgroup embedding,
`suppliedQuotient_fiber_iff` uses the published all-test identity
`parabolic_eq_comap_of_isClosedSubgroup`: an orbit in a closed subgroup
extends precisely when its ambient orbit extends. It follows that `q` and
`f ≫ r` have identical fibers on every relative scheme test. The generic
fpqc argument in `HomogeneousQuotientMonomorphism` then proves
`mono_suppliedQuotientMap`. No rational-point replacement is made, and no
lifting on the original test is assumed. In particular arbitrary nonaffine
and nonreduced tests remain included.

Finally `suppliedQuotient_isProper_of_closed_comparison` records the
conditional properness consequence: if this same comparison is a closed
immersion and `R.hom` is proper, then `Q.hom` is proper by composition.
This lemma neither supplies closedness nor constructs a proper ambient
quotient. Its source is exactly the original supplied `Q`; it does not
replace that scheme by another quotient model.

These constructions require neither smoothness nor affineness of `G` or
`H`, reductivity, connectedness, a field base, or a covering property of
`r`. They retain every cocharacter, including trivial and central ones.
They use effective-epimorphism descent, fpqc local lifts, general dynamic
functoriality and closed-subgroup orbit-extension reflection. No Borel,
regular cocharacter or rank-one input occurs. The provenance is internal,
with no new external geometric theorem. The unit is a comparison step
toward the affine homogeneous space route to
`DynamicQuotientProperStatement`; the affineness and closedness arguments
required for that route remain open.
