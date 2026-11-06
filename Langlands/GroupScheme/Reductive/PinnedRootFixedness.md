# Rigidity from fixed simple root subgroups

Implementation: Worker 1368. The task's factor-pair and root-induction proof
plan was supplied by Workers 1416 and 1467.

This internal reduction uses the actual pinning and previously published
root-factor-pair, finite Weyl-image, root-datum comparison, root fixedness and
torus-and-root generation constructions. It does not claim a new external
literature theorem or prove pinned rigidity unconditionally.

For a supplied `SplitPinning G`, every root of its datum is an actual relative
root by the defining range equality. The normalizer associated with a supplied
opposite factor pair acts on the full integral character lattice by the
reflection of this supplied root datum. To prove this, the Lean implementation
compares its integral reflection functional with the datum's coroot
functional. Both reflections belong to the finite full normalizer image,
whose finiteness follows from the proved closed-split-torus theorem. Their
product therefore has finite order. The published integral
`eq_functional_of_finiteOrder_reflections` identifies the two functionals,
so the reflections agree on every integral character, including central
characters. The proof requires neither root spanning nor a semisimple group.

Assume explicitly `RelativeRoot.HasOppositeFactorPairs p.inclusion`.
For any root subgroup fixed on all tests by an endomorphism fixing the torus,
the rational nontriviality theorem supplies a nonidentity root point. Pair
existence supplies its ordered opposite factors. The previously implemented
uniqueness argument fixes the normalizer point. The reflection comparison
identifies its action with the exact reflection of the supplied datum.
`fixedReflectionNormalizer` chooses this actual fixed normalizer.

Conjugation by this fixed normalizer propagates fixedness of any other root
functor to its reflection. Mathlib's `RootPairing.Base.induction_reflect` then
propagates fixedness from the simple-root functors to every root. Its sign
step uses self-reflection; its other step uses a reflection in a simple root.

The final theorem additionally assumes the full subgroup-functor equality
`torusCentralizer p.inclusion = SubgroupFunctor.range p.inclusion`. It forms
the closed subgroup fixed by the endomorphism and puts the torus and all
root functors inside it. The published closed torus-and-root generation
theorem makes this subgroup full, proving the endomorphism is the identity.
No smoothness of the fixed subgroup is assumed; smoothness and connectedness
of the ambient group come from its pinning.

All fields, characteristics and universes are retained. The pair-existence
and self-centralization premises remain explicit. Most importantly, the
simple-root hypothesis here is fixedness of the entire root subgroup on all
tests. Deriving it from the target's differential hypothesis is a separate
remaining step. This module does not supply the task's unconditional exact
`PinnedAutomorphismRigidityStatement` proof.
