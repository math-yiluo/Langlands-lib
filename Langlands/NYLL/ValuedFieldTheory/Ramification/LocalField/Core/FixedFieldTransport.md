# Chosen local valuation rings and fixed-field restriction

This internal module in `Langlands.NYLL.PortInternal.FltBridge` proves the
fixed-field restriction step used by the exact M327.009 proof. Worker 296
derives it from the published chosen-valuation existence and uniqueness,
the NYLL/FLT comparison in `FLTComparison`, and the published FLT quotient
theorem. Its parameters are `K L : Type`, fields with K-algebra structure,
finite dimensionality and Galoisness, and K's published nonarchimedean
local-field hypotheses. There is no chosen topology on L.

## Chosen action and FLT hypotheses

`chosenRing K L` is exactly the valuation subring of
`chosenLocalExtensionCompleteDVF K L`. `chosenAction K L` is the action from
`FLTComparison`, with the local extension witness chosen from the published
`chosenLocalExtension_properties` and the published uniqueness theorem at
comparison universe 0. Neither is registered as a global instance.

`chosenResidueFinite` uses the published module finiteness of the target
valuation ring over the base valuation ring and Mathlib
`IsLocalRing.ResidueField.finite_of_finite`. The base residue field is the
finite canonical residue field `𝓀[K]`.

`source_lower_map K L H n`, for a normal subgroup H of `Gal(L/K)`, applies
`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`
to the chosen ring. The action is faithful by fraction-ring extensionality;
the ring is a DVR. The fixed ring of the full automorphism group has residue
field embedding into the finite residue field of the chosen ring, hence
its residue field is finite and the residue extension is separable.
The result states that the image of the natural lower group at n in G/H
is the fixed-subring lower group at `Nat.ceil (herbrandPhi R H n)`.

## Identifying the fixed ring

For a Galois intermediate field E in L, `chosen_mem_iff` states that an element
of E belongs to its chosen valuation ring exactly when its image in L belongs
to L's chosen valuation ring. Comap L's valuation along E's inclusion. The
base extension witness follows directly from the two base extension
comparisons at values <= 1. Uniqueness for the chosen E valuation then gives
valuation equivalence, and hence the stated ring-membership equivalence.

For normal H, `fixedRingEquiv` is the ring equivalence from
`FixedPoints.subring (chosenRing K L) H` to
`chosenRing K (IntermediateField.fixedField H)`. It preserves the underlying
element of L; `chosen_mem_iff` supplies the valuation-ring membership in each
direction. `fixedRingEquiv_smul` proves equivariance under the quotient
representative g and the actual normal restriction of g, using
`AlgEquiv.restrictNormalHom_apply`.

## Upper restriction for every real index

`local_upper_rat_eq` and `local_exists_rat_upper_const` specialize the generic
comparison and rational constancy interval to the actual published
`localUpperRamificationGroup K L` with its local chosen extension witness.

For q >= 0 rational, `local_map_fixed_rat` factors normal restriction through
`IsGalois.normalAutEquivQuotient`. The published
`IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`
applied to `source_lower_map` identifies the quotient image with the upper
group of the fixed subring. Equivariant upper transport through
`fixedRingEquiv` identifies that group with the chosen ring's upper group
of the actual fixed field. The rational comparison on both sides gives
the required NYLL equality.

For t >= 0 real, `local_map_fixed` chooses the minimum of the two rational
endpoints supplied by the source and fixed-field constancy intervals; the
upper groups at that rational index equal their groups at t. At t <= -1,
both groups are full by the published nonpositive laws and normal
restriction is surjective. For -1 < t < 0 both groups equal their index-zero
groups by those laws, so the rational-zero result applies.
Thus `local_map_fixed` has no index restriction.

## Provenance and source route

The target is NYLL M327.009, pinned source
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean:610–733`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. This derived proof replaces the
original `upperRamificationGroup_quotient` and fixed-field valuation-ring
comparison from M326 and Core.lean:343–608. It uses the already published
FLT lower quotient and upper quotient theorems by Lean name, and explicitly
checks their DVR, faithful-action, finite-group and residue-separability
hypotheses. The source's separate NYLL M308–M326 constructions are not assumed.

The fixed-subring construction, residue-field embedding and equivariance
strategy follow the published
`Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`, whose supplied
p-adic ring is replaced by NYLL's chosen ring and whose relative-integer
membership lemma is replaced by chosen-valuation uniqueness. All generic
transport lemmas are reused by name. The FLT source pin and retained notices
are recorded in `FLTComparison.md`; NYLL's notices remain under
`licenses/NYLL/`. No new global extension instance or axiom is introduced.
