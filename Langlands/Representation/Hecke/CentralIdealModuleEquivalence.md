# Modules over a central Hecke ideal

This derived unit implements the module-category argument used in Renard
(9 July 2026), VI.7.4, printed pp.185–186 / PDF pp.191–192. Its inputs are a
Hausdorff locally compact nonarchimedean group with Borel structure, a left Haar
measure, smoothness of the left regular test-function representation, and an
idempotent categorical central operator `z` on smooth complex representations
with carrier universe `max u v`. The group universe `u` and the auxiliary carrier
universe `v` are independent.

`centralFixedProperty z` selects the actual smooth objects satisfying
`z.app V = 𝟙 V`. The functor `centralIdealModuleFunctor` sends such an object
to its integrated Hecke action restricted to the actual nonunital subring
`centralIdeal μ hl z`. Projecting a Hecke idempotent fixing a given vector gives
an ideal idempotent fixing that vector, proving nondegeneracy.

An ideal-linear map between fixed objects respects the full Hecke action:
every Hecke element acts in the same way as its central projection. The
published III.1.4 full Hecke functor therefore supplies the corresponding smooth
morphism. This proves fullness; retention of the entire additive map proves
faithfulness.

For essential surjectivity, `centralIdealExtend` pulls an arbitrary nondegenerate
ideal module back through the nonunital ring retraction
`centralIdealProjection`. It is a nondegenerate full Hecke module because every
ideal idempotent remains a Hecke idempotent and the projection fixes the ideal.
The published III.1.4 reconstruction gives `centralIdealRecovered`. Its
integrated action is the extended module action. Idempotence of the projection
and `central_app_eq_id_iff` show that this smooth object is fixed by `z`.
`centralIdealRecoveredIso` identifies its restricted module with the original
ideal module by the identity of their additive carrier.

These three properties construct `centralIdealModuleEquivalence`. Its forward
functor is the actual restriction functor. The natural isomorphism
`centralIdealModuleEquivalence_comparison` identifies its composition with the
nondegenerate-module inclusion with the smooth inclusion followed by the
published Hecke functor, the ambient-module inclusion, and actual scalar
restriction. This comparison is the reflexive isomorphism after unfolding the
specified functors.

The result is derived from the published central multiplier and ideal
constructions and the proved III.1.4 equivalence. No Bernstein decomposition,
existence of Bernstein projectors, or identification of a Bernstein block with
the fixed-object category is assumed silently or proved by this unit.
