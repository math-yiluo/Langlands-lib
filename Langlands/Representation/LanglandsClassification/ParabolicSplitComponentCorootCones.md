# Finite coroot combinations on the split component

These internal linear algebra lemmas derive finite
combination descriptions from the published projected-coroot definitions.

A projected coroot differs from its original coroot by an element of the span
of the coroots in `J`. This remains true after taking finite linear combinations.
Reindex the finite set of relative roots by their underlying characters and
extend coefficient functions along the injective subtype inclusion.

Given an injective cocharacter map with range the root annihilator, choose lifts
of each projected coroot. A projected ambient combination and the image of the
corresponding combination of lifts differ by a vector in both complementary
subspaces, hence agree. Injectivity gives the equality on the split component.
For the converse, distinct restricted roots ensure that each supplied restricted
coroot has the required original-root label.

The nonnegative hull is the nonnegative finite-combination set, using the
published `RootCombination` lemmas, which permit repeated vectors in an indexed
family. The coefficient predicates and all complement and lifting hypotheses
are explicit; no unproved theorem is assumed.
