# Finite length of actual opposite Jacquet modules from rational duality

Author: Worker 196.

This internal conditional adapter derives finite length and admissibility for
the actual opposite normalized Jacquet module used in the rational-point
commutation problem. It does not prove rational Jacquet duality, finite-length
admissibility, or the closed commutation target. Its premises name those
outstanding results explicitly.

The field is any nonarchimedean local field `k : Type u`. The ambient group
scheme is connected reductive, and the topology on its identity-test rational
points is exactly `RationalPointFamily.pointTopology`. The indices are literal
finite subsets of `SimpleRoot i ν`; the chosen standard cocharacter `ζ`
satisfies `IsStandardCocharacter i ν (rootSet i ν I) ζ`. The opposite subgroup
is the contraction subgroup of the inverse cocharacter, with its actual
negative Haar half-normalization. The two universe parameters `u` and `v`
are independent, with representation carriers in `max (u + 1) v`. No
nonemptiness, splitness, quasisplitness, or characteristic-zero premise is
added.

`standardLevi_compactOpenCofinal` selects a standard cocharacter from the
existing `StandardCocharacterStatement`. Its all-test standard-Levi equality
identifies the literal standard Levi subgroup with the actual dynamic
centralizer on the identity test. Rewriting by this equality reduces the
claim to `General.dynamicCentralizer_compactOpenCofinal`. Affineness and
local finite type follow from the displayed connected-reductive hypothesis.
The lemma assumes the ambient group topology and derives cofinality for
the exact standard Levi with the subgroup topology.

`standardLevi_isAdmissible_of_hasFiniteLength` uses the same all-test equality
to specialize `DynamicLeviFiniteLengthAdmissibleStatement` to every
finite-length smooth complex representation of this standard Levi.
The closed admissibility proposition remains an explicit premise.

`oppositeJacquet_finiteLength_admissible_of_rationalDuality` starts with a
finite-length ambient object `A`, ambient smooth-dual finite-length
preservation `hc`, and finite-length preservation `hrFl` for standard
normalized Jacquet restriction `rP`. The closed
`RationalPointsFiniteLengthAdmissibleStatement` gives admissibility of `A`.
The closed `RationalNaturalJacquetDualityStatement` therefore supplies an
actual isomorphism
`rP(A.contragredient) ≅ (rO(A)).contragredient`.
The left side has finite length by `hc` and `hrFl`;
`SmoothRep.hasFiniteLength_of_iso` transfers this to the right side.

The standard-Levi admissibility specialization makes this smooth dual
admissible. Derived Levi compact-open cofinality and
`SmoothRep.isAdmissible_contragredient_iff` then imply admissibility of
`rO(A)`. The published generic
`SmoothRep.contragredient_hasFiniteLength`, applied to the finite-length
admissible dual, gives finite length of the smooth bidual.
`SmoothRep.bidualIso` identifies `rO(A)` with that bidual, and
`hasFiniteLength_of_iso` transports finite length back.
`oppositeJacquet_preservesFiniteLength_of_rationalDuality` packages this
conclusion as the existing `PreservesFiniteLength` predicate.

`oppositeJacquetFiniteLengthObject` constructs an object of the published
`SmoothRep.FiniteLengthObject ℂ (levi i ν I)` from an actual finite-length
ambient object. Its representation is the actual normalized opposite Jacquet
module, and its finite-length certificate is the preceding derived proof.
Thus `FiniteLengthGrothendieckGroup.ofObject` can take its class in the
existing exact Grothendieck group. The construction adds no generators,
relations, or equivalence to a different group.

The implementation uses only the objectwise component of the closed natural
duality premise. It adds no separate opposite-Jacquet finite-length premise
and no separate Levi contragredient-preservation premise. It does not
alter the final commutation proposition or discharge its representation
prerequisites.

The provenance is internal composition of published equality, topology,
smooth-duality, and module-length results. No new literature assertion is
made. The direct generic dual-length proof is
`Langlands.Representation.Smooth.Contragredient.FiniteLengthProof`:
it uses finite group-algebra length induction, admissibility of subobjects
and quotients, irreducibility transfer through admissible biduality, and
exactness of the smooth dual. Through `Category.Contragredient` it imports
`Classification.SupercuspidalContragredientAux`, whose generic separation
and admissible irreducibility-transfer lemmas support that argument.
The current adapter invokes no classification, character-independence,
geometric-lemma, adjointness, or cuspidal-support theorem. The actual proof
dependencies of any future supplied closed duality or admissibility results
remain separate from these conditional implications.

The local topology instance has the explicit declaration name
`rationalOppositeJacquetPointTopology` so this module can be imported together with
the rational alternating-operator and reduction modules. Its value is still
exactly `pointTopology`; no mathematical declaration changes meaning.
