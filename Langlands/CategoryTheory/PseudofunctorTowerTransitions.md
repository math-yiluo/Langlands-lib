# Pointed transitions on a tower

This internal categorical lemma concerns an arbitrary category-valued
pseudofunctor on a locally discrete category. It retains independent
universes for the base objects and morphisms and the fibre objects and
morphisms.

The input is a sequence of base objects, a specified map from each later
object to each earlier object, specified adjacent maps, their identity and
successor composition equations, and actual fibre objects with actual
adjacent transition isomorphisms. `hasTransition` proves that the displayed
map from stage m to stage n carries the stage-m object to an object
isomorphic to the stage-n object whenever n is at most m.

The proof inducts on the later stage. The base case uses the original
pseudofunctor identity comparison. The successor case uses the original
composition comparison for the displayed composite, applies the action
functor to the adjacent isomorphism, and composes with the inductive
isomorphism. `transitionIso` chooses an actual isomorphism from this proved nonemptiness. No identity or composition law is asserted for the choices.

`actionObjectCongr` transports an action object along an equality of its source test and heterogeneous equalities of the arrow and fibre object. Its proof eliminates those equalities.

The construction is derived directly from Mathlib's pseudofunctor
comparisons. Its intended application is to the existing actual pointed
Picard deformation pseudofunctor; it asserts no geometric existence result.
