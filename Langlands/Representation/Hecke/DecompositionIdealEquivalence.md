# Smooth decomposition factors as central-ideal modules

This derived unit connects the generic central-ideal module equivalence to the
actual factors of a supplied smooth category decomposition. It is infrastructure
for Renard (9 July 2026), VI.7.4, printed pp.185–186 / PDF pp.191–192.

Each factor is assumed closed under actual smooth isomorphisms. Its canonical
central projector acts identically on precisely the objects of the factor.
For the reverse implication, the chosen coproduct inclusion of the selected
component and its projection are inverse when the central projector is the
identity. Thus the object is isomorphic to that component and belongs to the
same factor.

`centralProjectorFixedEquivalence` identifies the full factor with the full
category of objects fixed by its canonical projector. Composing this with
`centralIdealModuleEquivalence` gives `decompositionIdealEquivalence`, an
equivalence to nondegenerate modules over the actual central Hecke ideal.
Its forward functor retains each additive carrier and restricts the integrated
Hecke action to that ideal. `decompositionIdealEquivalence_comparison` gives
the exact natural comparison with the specified ambient inclusion and scalar
restriction; it is reflexive after unfolding the actual functors.

The group, topology, measure and regular-smoothness hypotheses are those of the
central multiplier construction. The factor index has an independent universe.
The decomposition and closure under isomorphism are explicit hypotheses; this
unit does not prove the unconditional Bernstein decomposition.
