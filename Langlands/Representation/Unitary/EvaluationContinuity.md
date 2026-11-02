# Continuous completed actions from finite orbits and faithful evaluations

This internal construction extends the published positive-form completion
without choosing a topology on its original algebraic complex carrier. The
group has a topology, its action is a representation, and a positive invariant
form is supplied. The group, carrier and evaluation index have independent
universes. No topological-group law, compactness or measurability is needed.

The additional input is an injective complex-linear map `I` from the carrier
into complex-valued functions on an arbitrary index type. For each original
vector the algebraic orbit span must be finite dimensional, and each scalar
evaluation of its orbit must be continuous in the group variable.

`continuous_normedOrbit_of_finite_evaluations` first treats one such vector.
Map its finite orbit span into the form-dependent normed carrier. On this
finite-dimensional subspace, compose the inverse carrier identification with
the faithful function realization. The resulting injective linear map into
the product of copies of the complex numbers is a closed embedding by
Mathlib's finite-dimensional topological vector-space theorem. Continuity of
each evaluation therefore proves continuity of the orbit in the subspace,
and hence in the form norm. No evaluation is required to be continuous or
bounded on the whole normed carrier.

`continuous_completedAction_of_embedded_orbits` proves joint continuity of
the completed action whenever all embedded algebraic orbits are continuous.
It applies Mathlib's dense-set Lipschitz continuity theorem: the embedded
carrier is dense in its completion, and each extended operator has Lipschitz
constant one. Thus continuity of orbits on that dense set suffices.

`completedContinuousActionOfFiniteEvaluations` combines these two steps and
bundles the existing completed representation action as a continuous map on
the product of the original group topology and the actual Hilbert completion.
Its application formula is the existing completed representation, so its
action laws, norm preservation and embedded-vector formulas are unchanged.
These hypotheses are checked in the automorphic application; this module
alone asserts no finite-orbit or evaluation-continuity existence theorem.

The provenance is internal composition of the published invariant-form
completion and actual finite-orbit-span constructions with Mathlib's
finite-dimensional embedding and dense Lipschitz continuity theorems. No new
original-literature identification is asserted.
