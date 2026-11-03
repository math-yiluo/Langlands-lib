# A common contracting element for opposite rational-point radicals

Worker 127 wrote the proposition and this explanation. Workers 118, 480 and
15 contributed its fixed-element, cofinality and actual-opposite requirements
and distinguished them from the existing weaker adapter.

`Langlands.Aubert.General.RationalPointFamily.RationalOppositeIwahoriBasisStatement`
is a proposition definition awaiting proof. It isolates the structural
existence input for the published generic stable-pairing construction on the
actual rational-point group. This file proves no existence theorem.

## Scope and actual subgroups

The structural prefix agrees with
`RationalNaturalJacquetDualityStatement`: every nonarchimedean local field
`k : Type u`, every connected reductive group scheme over `Spec k`, an actual
maximal split torus map `i`, a generic cocharacter `ν`, the displayed
`StandardCocharacterStatement`, every finite simple-root subset `I`, and
every actual standard-cocharacter witness `ζ` for its root set. Positive
characteristic, nonsplit and non-quasisplit groups, empty simple-root types
and empty finite subsets are retained.

The ambient group is `RationalPoint k G.X` with the canonical `pointTopology`.
Affineness of `G` and the monomorphism of `i` are extracted before installing
that topology. Local compactness, the nonarchimedean group property and
Hausdorffness refer to this topology. The standard radical's closedness `_hU`
is retained from the consumer's structural prefix, although the concluding
basis predicate itself does not use this proof.

Write `U = unipotent i ν I`, `M = levi i ν I` and
`O = oppositeUnipotent i ζ`. These are literal subgroups of the same ambient
rational-point group. In particular, `O` is the identity-test value of the
dynamic unipotent subgroup for the inverse of `ζ`, as defined in
`RationalOppositeParabolic`. It is not replaced by a root-generated opposite
subgroup or a conjugate. The statement assumes no actual-root sign reversal,
root-system assertion or comparison with
`SpecialCompact.standardOppositeUnipotentPoints`.

## Quantifier order and contraction conditions

For each complete set of structural parameters, the conclusion chooses one
element `g` before every ambient identity neighborhood. This element
commutes with every element of the literal subgroup `M`. The conclusion
`Jacquet.HasOppositeIwahoriContractionBasis U M O g` then means:

For every ambient open set `W` containing `1`, there exists an ambient open
subgroup `K` which is compact, is contained in `W`, and satisfies both
`Jacquet.IsIwahoriContraction K U M O g` and
`Jacquet.IsIwahoriContraction K O M U g⁻¹`.

For the first contraction predicate, the imported definition requires:

- `g ∈ M`;
- a factorization of each element of `K` as a product in
  `(K ∩ O)(K ∩ M)(K ∩ U)`;
- conjugation by `g` preserving `K ∩ U`, and conjugation by `g⁻¹`
  preserving `K ∩ M` and `K ∩ O`;
- for every element of `U`, some nonnegative power of conjugation by `g`
  carrying it into `K`;
- for every ambient open subgroup `L`, a single nonnegative power of
  conjugation by `g⁻¹` carrying all of `K ∩ O` into `L`.

The second predicate makes exactly these requirements with `U` and `O`
interchanged and `g` replaced by `g⁻¹`. Its factorization order is therefore
`(K ∩ U)(K ∩ M)(K ∩ O)`. The membership of `g` in `M` is already part of the
first predicate; no additional membership premise is supplied. Taking
`W` to be the whole group supplies such a `K`, even when the radicals or
root labels are empty.

The element `g` may depend on `I` and `ζ`; the statement makes no simultaneous
choice across different structural parameters. For each such choice it is
the same `g` for all neighborhoods and both orientations. Cofinality is in
the ambient group, not merely in its Levi subgroup.

## Provenance

This is a derived existence target for the actual-subgroup specialization of
the public internal definition
`Jacquet.HasOppositeIwahoriContractionBasis`. The need for a central element
chosen before the basis is explicit in
`Jacquet.stablePairingDataOfIwahoriContractions`. The imported definition and
construction are conditional and do not prove this new existence statement.

The source background is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
registered as `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Section III.4 and Lemma III.4.1 on PDF p. 5 provide an ambient
identity-neighborhood basis of compact opens adapted to all standard
parabolics. Its Iwahori-factorization definition includes conjugation
inclusions for every element of the contracting chamber. Sections III.5–6,
PDF pp. 5–8, use contracting elements, canonical stable-image lifts and the
opposite-Jacquet pairing. The original page images distinguishing the two
radicals were checked. No separate errata file for this source was found
in the inspected public notes or source folder.

The present proposition is not a verbatim restatement of III.4.1. It packages
the actual dynamic opposite, centrality, a fixed contracting element, both
factorization orders, exhaustion and uniform contraction at canonical
topology. A proof must construct those ingredients and justify this full
scope. In particular, a basis conditional on an element of a strict chamber
does not establish the required existence of that element.

## Existing interfaces and consumer obligations

The public `Jacquet.HasIwahoriContractionBasis U M O` is weaker: its element
may depend on the compact open and its cofinality requirement concerns only
the Levi. The special-compact
`SimultaneousBasisJacquetAdapterStatement` targets that weaker predicate.
The present statement cannot be discharged by renaming that adapter.

`SpecialCompact.SimultaneousStandardBasisAt` records simultaneous
factorization, expansion and power-basis conditions for elements in its
actual strict chambers. It supplies neither a proof that those chambers
contain a compatible element nor a comparison between its standard
opposite and the `oppositeUnipotent i ζ` used here. The stronger joint
special-compact existence statement is itself a target. Those structural
existence and comparison obligations remain necessary in any proof using
that route; they are not added as premises here.

Once proved, this statement and the public standard and opposite
semidirect decompositions provide the structural inputs to
`Jacquet.stablePairingDataOfIwahoriContractions`.
`Jacquet.IwahoriStablePairingAdmits` separately derives the analytic
stable-pairing conditions for admissible representations. Actual opposite
Haar-character reciprocity, normalization transport and coherent bundled
naturality are separate requirements for the final rational natural
Jacquet-duality theorem.

No representation, pairing, compact-limit, strict-chamber nonemptiness,
root-system or Haar-compatibility hypothesis is assumed in the present
existence result. This proposition definition invokes no classification,
character independence, geometric lemma, adjointness or cuspidal-support
theorem and proves none of the final duality assertion.
