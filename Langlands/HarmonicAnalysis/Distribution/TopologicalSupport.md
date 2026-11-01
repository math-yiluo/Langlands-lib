# Topological support and compactly supported distributions

This module constructs the support and E′(X) of Renard II.1.2 on the existing
algebraic distributions. The declarations are in
`Langlands.HarmonicAnalysis.Distribution`. Worker 6 authored the construction
and initial paired explanation; Worker 128 audited the original passage,
the source scope, and the complete construction, and prepared this pair for
focused construction task `77b131cb-8b53-44cc-9165-5da55a5940af`.

## Source and mathematical objects

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**, II.1.2, printed p.31 / PDF p.37, defines the support
of a distribution as the complement of the union of the open sets where
its restriction vanishes. The following paragraph defines E′(X) as the
space of distributions with compact support.

The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 6 read the complete original II.1.2 passage. Worker 128 independently
read PDF pages 36–38, including the function, distribution, support, pairing
and vector-valued paragraphs, and visually checked the definitions on PDF37.
This unit implements the support and E′ constructions and their intrinsic laws.

The existing `SchwartzBruhat X` consists of actual locally constant complex
functions on the supplied topological space with compact topological
support. The existing `Distribution X` is its full algebraic complex dual.
The actual linear map `restrictOpen hU` is dual to extension of test functions
by zero from the open subtype U, with its induced topology. Its evaluation
is `D (SchwartzBruhat.extendZero hU f)`. There is no topology or continuity
condition on the distributions.

## Support definition and scope

For an arbitrary `X : Type u` with `[TopologicalSpace X] [T2Space X]`,

```lean
support D :=
  (⋃₀ {U : Set X | ∃ hU : IsOpen U, restrictOpen hU D = 0})ᶜ
```

This is literally the source's open-restriction definition. Hausdorffness
is needed by the existing zero-extension map; the definition itself does
not require local compactness or total disconnectedness.
`isClosed_support` proves closedness by taking the complement of an open
union. `not_mem_support_iff` unpacks the union: a point lies outside the
support exactly when it belongs to an open U with zero actual restriction.
`support_zero` uses U equal to the entire space, whose restriction of the
zero distribution is zero.

For a closed subset Z, `restrictOpen_compl_eq_zero` says that
`D ∈ supportedOn Z` forces the restriction to the open complement to vanish.
Here the existing `supportedOn Z` means that D annihilates every test
function vanishing pointwise on Z. Every zero extension from the complement
has that pointwise vanishing property, so applying D gives zero.
Consequently `support_subset_of_mem_supportedOn` places the topological
support in Z. These two laws use only Hausdorffness and the stated
closedness.

The reverse implication requires the source's locally profinite hypotheses:
`[LocallyCompactSpace X] [TotallyDisconnectedSpace X]` in addition to
Hausdorffness. For every closed Z,

```lean
support D ⊆ Z ↔ D ∈ supportedOn Z
```

is `support_subset_iff_mem_supportedOn`. A point outside Z lies outside the
topological support, so the neighborhood criterion supplies a neighborhood
with zero open restriction. The published `openRestrictionLocality` theorem
then proves the annihilator condition. Its finite compact-cover argument
is reused by Lean name, rather than assumed as an extra premise or repeated.
The other implication is the Hausdorff law already described. The closedness
of Z is explicit; the equivalence is not asserted for arbitrary subsets.

The three topological classes are precisely equivalent to Renard's
`Langlands.Topology.IsLocallyProfinite X`, by the published
`Langlands.Topology.isLocallyProfinite_iff_mathlib`. The existing extraction
lemmas install these classes locally when the input is the source
predicate. The constructions use the actual supplied topology throughout.
There is no countability, second-countability, ambient compactness,
nonemptiness, measure, group or representation assumption.

## Compactly supported distributions

Under the three source topological classes, `compactlySupported` is an
actual complex submodule of `Distribution X`, with carrier exactly

```lean
{D | IsCompact (support D)}
```

Its membership law is `mem_compactlySupported_iff`. Its subtype is the
source space E′(X), with the inherited complex vector-space operations.
It is not an externally supplied subspace or a space of continuous duals.

The support bridge applied to the closed set `support D` first proves
`mem_supportedOn_support`. Monotonicity of the existing annihilator
submodules and their addition law then give
`support_add_subset`: the support of D + E lies in the union of the two
supports. The scalar closure law gives `support_smul_subset`: the support
of c • D lies in the support of D. The latter statement includes c = 0
and makes no equality claim.

The zero support is empty and hence compact. A sum support is closed and
contained in a compact union of two compact supports, hence compact.
A scalar multiple support is closed and contained in the original compact
support, hence compact. These prove all three submodule closure fields,
using Mathlib's `IsCompact.of_isClosed_subset`.

`mem_compactlySupported_iff_exists_compact` proves the equivalent compact
carrier formulation:

```lean
D ∈ compactlySupported ↔
  ∃ K : Set X, IsCompact K ∧ D ∈ supportedOn K
```

Forwards choose the actual support itself. Backwards a compact K is closed
in the Hausdorff space, so the established bridge puts `support D` inside K;
closedness of the support gives its compactness. Empty spaces, empty
supports and K = ∅ are included in the same arguments.

## Provenance, dependencies and remaining scope

The support and compact-support carrier transcribe Renard. The neighborhood,
closed-support bridge and submodule laws are intrinsic deductions ensuring
the two constructions agree with the existing Library convention.
They import `Distribution.OpenRestrictionLocalityProof`, which brings in
the published subspace maps, pointwise support submodules and locality proof.
The locality proof's authorship and finite-cover route remain as documented
in its existing paired Markdown.

The published `closedPushforwardSupportedEquiv` in
[SupportedRestriction](SupportedRestriction.md) already identifies
`supportedOn Z` with `Distribution Z` for closed Z. The bridge here shows
that its supported submodule is precisely the space described by Renard's
topological support condition, so that the existing equivalence applies
with the source convention.
This module adds no closed restriction from arbitrary ambient distributions.

The E′–C∞ duality pairing, vector-valued functions and tensor injections,
the full exact-sequence statements and tensor products of distributions
remain separate successor units. This construction does not claim proofs
of those assertions.
