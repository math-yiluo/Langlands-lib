# Finite-length components of the actual rational-point duality targets

Author: Worker 196.

This internal construction restricts the two closed rational natural-duality
propositions to finite-length smooth complex representations. Those closed
propositions and the required closed finite-length admissibility propositions
remain explicit premises. The construction supplies components and proves
their inherited naturality; it does not prove the closed duality or
admissibility propositions or the final commutation theorem.

`standardCocharacterForDuality` chooses a cocharacter from the existence
clause of `StandardCocharacterStatement`. The result is a subtype carrying
the exact `IsStandardCocharacter i ν (rootSet i ν I)` proof. Thus forming
the opposite rational-point subgroup requires no new existence premise.
No uniqueness or compatibility among different cocharacter choices is
asserted.

`finiteLengthInductionDualityIso` chooses one coherent family from
`RationalNaturalInductionDualityStatement` for the displayed field, group,
torus, generic cocharacter and actual simple-root subset. For a finite-length
object `A` of the literal standard Levi,
`standardLevi_isAdmissible_of_hasFiniteLength` derives admissibility from the
explicit `DynamicLeviFiniteLengthAdmissibleStatement` premise. Evaluating
the selected coherent family at that object and admissibility proof gives
`(iP(A)).contragredient ≅ iP(A.contragredient)`.
Here `iP` is exactly the normalized induction functor of the standard
semidirect decomposition. Closedness of the parabolic and radical and
continuity of the actual Levi projection are retained from the original
closed duality target.

`finiteLengthInductionDualityIso_naturality` specializes the naturality
clause of that same selected coherent family. For every actual intertwiner
`f : A ⟶ B` between finite-length Levi objects it states
`(iP(f))∨ ≫ E_A.hom = E_B.hom ≫ iP(f∨)`.
The family is selected before its input object, so the result does not use
unrelated choices of objectwise isomorphisms.

`finiteLengthJacquetDualityIso` similarly selects a coherent family from
`RationalNaturalJacquetDualityStatement`. The explicit
`RationalPointsFiniteLengthAdmissibleStatement` premise derives
admissibility of a finite-length ambient object `A`. Its component is
`rP(A.contragredient) ≅ (rO(A)).contragredient`.
The opposite functor uses the actual inverse-cocharacter radical, its
derived semidirect decomposition with the literal standard Levi, and its
proved closedness.
`finiteLengthJacquetDualityIso_naturality` specializes the same family's
contravariant naturality to every actual ambient intertwiner:
`rP(f∨) ≫ E_A.hom = E_B.hom ≫ (rO(f))∨`.

The topology is the canonical `RationalPointFamily.pointTopology`.
The field is any nonarchimedean local field, and the ambient group scheme
is any connected reductive group. The subset labels are the actual
`SimpleRoot i ν`, including empty label types and empty subsets.
All representation carriers have universe `max (u + 1) v`, with independent
`u` and `v`. The original positive half-normalization for induction and
negative half-normalizations for the actual standard and opposite Jacquet
functors are unchanged. No characteristic-zero, splitness or quasisplitness
restriction is introduced.

The provenance is internal logical specialization and choice from explicit
closed propositions. The only admissibility discharger invoked here is
`standardLevi_isAdmissible_of_hasFiniteLength`, itself the all-test
standard-Levi equality applied to the explicit closed dynamic-Levi premise.
No classification, character-independence, geometric-lemma, adjointness
or cuspidal-support theorem is invoked. The future proofs supplied for
the closed premises retain their own declaration-level dependency
obligations. The paired duality targets document the original source
correspondence; this file makes no additional literature assertion.

The local topology instance has the explicit declaration name
`rationalFiniteLengthDualityPointTopology` so this module can be imported together with
the rational alternating-operator and reduction modules. Its value is still
exactly `pointTopology`; no mathematical declaration changes meaning.
