# The unique Levi containing a torus in a dynamic presentation

Worker 592.

This derived construction supplies the local algebraic step of the relative
torus–Levi theorem. Its inputs explicitly include
`DynamicRelativeLeviStatement` and `RelativeUnipotentRadicalStatement`;
it does not prove either statement.

`RelativeLevi.TorusLeviWitness t` records an actual relative Levi inclusion,
containment of the image of the prescribed commutative group `t`, and
uniqueness of its subgroup functor among all relative Levi subgroups
containing that image. All containments and equalities concern points on
every test scheme, including nonreduced tests.

`RelativeLevi.torusDynamicLeviWitness` constructs such a witness over any
base scheme when `G` is reductive and a cocharacter `nu` of the prescribed
commutative group dynamically presents the supplied inclusion `i : P ⟶ G`.
No torus property or fibrewise maximality is used in this local step; those
properties enter the separate local presentation theorem.

The published arbitrary-base `dynamicBaseRepresentability` constructs
representatives of the dynamic unipotent and centralizer functors. The
canonical `centralizerToParabolic` supplies the inclusion of the latter in
`P`. The supplied dynamic structure statement makes it a relative Levi and
makes the factored dynamic unipotent subgroup a relative unipotent radical.
The prescribed commutative group factors through the centralizer by
`Dynamic.torusFactor`, and cancellation of the represented parabolic
inclusion proves containment in the Levi inside `P`.

For another relative Levi containing that group, its multiplication
isomorphism and the normality of its radical supply `leviRetraction`.
The supplied radical statement identifies this radical's all-test range
with the dynamic radical's range. Monomorphy of `i` then identifies the
retraction's kernel, viewed in `G`, with the dynamic unipotent functor.
Factoring the prescribed group through the other Levi also factors `nu`
through it. The theorem
`DynamicLeviConjugacy.range_eq_centralizer_of_cocharacter_factors`
identifies its ambient range with the same dynamic centralizer.
Postcomposition by the monomorphic `i` reflects range inclusions, yielding
the required equality inside `P`.

The provenance is internal composition of the cited Library constructions
and the two explicit proposition inputs. This module supplies neither
étale local presentations nor effective descent of the uniquely specified
Levi. Those remain separate obligations in the full arbitrary-base theorem.
