# Actual Levi cocenter root-model assembly from structural inputs

Authors: Worker 1293 (assembly), Worker 1632 (supporting constructions and interfaces).

This internal supporting construction retains the actual rational torus,
its selected common finite Galois splitting field, the actual ambient and
centralizer root data on that field, and the base change of the original
separating cocharacter. It takes four named structural inputs:
`RootDatumExistenceStatement`,
`DerivedSubgroupSemisimpleStatement`,
`DerivedMaximalTorusProductSurjectivityStatement`, and
`DerivedMaximalTorusIntersectionStatement`, all at arbitrary universe `u`.
None of these propositions is proved by this module.

`characterLattice.cocenter_coweight_comparison_of_structuralInputs`
constructs the full actual character comparison for compatible actual
ambient and centralizer data over a field with split tori. It passes to
the algebraic closure, canonically transports the two root data and the
same cocharacter, and uses the published `maximalTorusBaseChange` proof.
The geometric subgroup-torus construction supplies an actual split
maximal torus of the actual derived subgroup inside the prescribed torus.
The supplied root-existence proposition provides its actual root datum.
Connected reductivity of the derived subgroup follows from the published
smoothness, connectedness and normal-subgroup results.

Over the closure, the supplied semisimplicity, product-surjectivity and
full-intersection propositions supply the remaining geometric premises
of the actual coweight-character comparison. The quotient uses the full
actual derived range and its proved base-change compatibility. Root
selection is transported through the actual character lattice
equivalence and the actual integer pairing. The canonical base-change
comparison reflects injectivity and the entire image-annihilator
identity to the original field.

`TorusCentralizerFiniteGaloisModel.cocenterRootDescent` applies that
comparison to the retained finite-field model and constructs a genuine
root base and `CocenterRootDescentData`. Its cocharacter is the canonical
base change of the original-field separating cocharacter, whose ordinary
Galois fixedness was already proved. The actual cocenter pullback is the
base change of the original composite through the quotient. The
published coweight-face construction provides the corrections, the
simple-coroot permutation and the invariant selected subset. These
ordinary Galois representations remain over the finite splitting field
and the original field, independent of the algebraic closure used for
the character comparison.

`splitTorusCentralizerCocenterRootModel_of_structuralInputs` packages
these data into the exact public
`SplitTorusCentralizerCocenterRootModelStatement`, preserving arbitrary
universe `u` and the actual group maps. Its four structural premises
remain explicit, so this is a conditional supporting assembly, not an
unconditional proof of that proposition. No simple connectedness,
perfectness, characteristic restriction, chosen parabolic, or integral
coroot-generation premise is introduced.

The provenance is composition of the imported constructions and the
explicit structural propositions. No literature theorem is transcribed.
The proof never substitutes a permutation lattice for the actual
character pullback and never replaces the retained rational torus or
chooses a new separating cocharacter over the closure.
