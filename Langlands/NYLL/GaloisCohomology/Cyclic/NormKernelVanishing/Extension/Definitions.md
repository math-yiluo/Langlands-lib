# NYLL M004.002–M004.005: extension fixed representations and the cyclic norm-kernel vanishing condition

## Source

The paired Lean file extracts four consecutive declarations from Naganori
Yamaguchi's ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` (SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`).
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source`. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Source declaration (docstring – end) | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M004.002 | `CyclicCohomology.extensionSubgroup`, `abbrev` at line 51 (lines 47–54) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (line 39) |
| M004.003 | `CyclicCohomology.extensionFixedRepresentation`, `noncomputable def` at line 61 (lines 56–68) | `Langlands.NYLL.CyclicCohomology.extensionFixedRepresentation` (line 49) |
| M004.004 | `CyclicCohomology.IsContinuousDiscreteRepresentation`, `def` at line 73 (lines 70–77) | `Langlands.NYLL.CyclicCohomology.IsContinuousDiscreteRepresentation` (line 61) |
| M004.005 | `CyclicCohomology.SatisfiesCyclicNormKernelVanishing`, `def` at line 90 (lines 79–102) | `Langlands.NYLL.CyclicCohomology.SatisfiesCyclicNormKernelVanishing` (line 75) |

The section context is source lines 26–32: `namespace CyclicCohomology`,
`noncomputable section`, `open CategoryTheory` and `universe u`. The adapted
file reproduces it inside `namespace Langlands.NYLL.CyclicCohomology`.

## The declarations

**`extensionSubgroup`** (M004.002). Telescope: implicit `{G : Type u}` at an
arbitrary universe `u`, instance-implicit `[Group G]` and
`[TopologicalSpace G]`, explicit closed subgroups `K L : ClosedSubgroup G` and
an explicit containment proof `_hLK : L.toSubgroup ≤ K.toSubgroup`. The value is
the subgroup `L.toSubgroup.subgroupOf K.toSubgroup : Subgroup K.toSubgroup`,
that is `L` regarded as a subgroup of `K`, via Mathlib's `Subgroup.subgroupOf`.
In the source's reading `K` and `L` are `G_K` and `G_L` for an abstract
extension `L | K`. The containment proof is unused in the body, as in the
source. It remains a reducible `abbrev`.

**`extensionFixedRepresentation`** (M004.003). Telescope: implicit
`{G : Type}` (universe zero), `[Group G]`, `[TopologicalSpace G]`, then explicit
`A : Rep.{0} ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup` and the explicit normality argument
`hnormal : (extensionSubgroup K L hLK).Normal`. The result type is
`Rep ℤ (K.toSubgroup ⧸ extensionSubgroup K L hLK)`. Its quotient group
structure is the source's: Mathlib's quotient group, whose normality instance
is the local `hnormal`. The value is the actual Mathlib construction
`Rep.quotientToInvariants (Rep.res K.toSubgroup.subtype A) (extensionSubgroup K L hLK)`.
It restricts `A` along the inclusion `K.toSubgroup →* G`, takes the invariants
of `L` viewed inside `K`, and lets `K ⧸ L` act on them. In the source's reading
this is the `G(L | K)`-module `A_L = A^{G_L}`. The term is
noncomputable data, not supplied data or a placeholder.

**`IsContinuousDiscreteRepresentation`** (M004.004). Telescope: `{G : Type}`,
`[Group G]`, `[TopologicalSpace G]`, `A : Rep.{0} ℤ G`. The value is the
`Prop`: with the local topology `⊥` on `A.V` (the discrete topology, since
Mathlib orders topologies by reverse inclusion),
`Continuous fun p : G × A.V => A.ρ p.1 p.2`. The product carries the product
of the given topology on `G` and `⊥`. This is the source's continuity condition
on a discrete `G`-module. No continuity statement for another topology on
`A.V` is involved, and no global topology instance on `A.V` is introduced.

**`SatisfiesCyclicNormKernelVanishing`** (M004.005). Telescope: `{G : Type}`,
`[Group G]`, `[TopologicalSpace G]`, `A : Rep.{0} ℤ G`. The value is the `Prop`
that, for all, in this order,

1. `K L : ClosedSubgroup G`,
2. `hLK : L.toSubgroup ≤ K.toSubgroup`,
3. `hnormal : (extensionSubgroup K L hLK).Normal`,
4. `hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)`,
5. `g : K.toSubgroup ⧸ extensionSubgroup K L hLK`,
6. `_hg : ∀ x, x ∈ Subgroup.zpowers g`,

the actual Tate cohomology object
`tateCohomology (extensionFixedRepresentation A K L hLK hnormal) (-1)` is zero
(`CategoryTheory.Limits.IsZero`). The `Fintype` instance required by Mathlib's
`tateCohomology` is the local `Fintype.ofFinite` from `hfinite`. The quotient
group structure uses the local instance `hnormal`. As the source's docstring
states, `hnormal` expresses that `L | K` is Galois, `hfinite` that it is finite,
and `g, _hg` that its Galois group is cyclic with generator `g`. The predicate
therefore states that `H⁻¹(G(L | K), A_L) = 0` for every finite cyclic abstract
extension `L | K`.

No profiniteness of `G`, continuity of `A` or other premise is added. As the
source's docstring notes, these are ambient hypotheses of the source
construction and not part of this condition. The predicate is a source
definition, so it keeps its source name without a `Statement` suffix.

## Original-to-adapted map and modifications (Worker 133)

- **Extraction**: only source lines 47–102 (M004.002–M004.005) and the section
  context of lines 26–32 are taken. M004.001 (`isCyclic_of_generator`), M004.006
  and M004.007 are not part of this unit. The first is unused here. M004.006 and
  M004.007 already exist in the Library as
  `Langlands.NYLL.CyclicCohomology.finiteCyclicH1IsoTateHMinusOne` and
  `Langlands.NYLL.CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZeroStatement`.
- **Namespace**: `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
  The section's `noncomputable section`, `open CategoryTheory` and
  `universe u` are kept. The section is closed by an explicit `end`, as at
  source line 148.
- **Imports**: the source imports
  `Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`,
  `Mathlib.RepresentationTheory.Invariants`,
  `Mathlib.Topology.Algebra.Group.ClosedSubgroup` and
  `Nyll.GaloisCohomology.Cyclic.TateComparison`. These four declarations use
  only Mathlib constants. The adapted file imports
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic` (for
  `tateCohomology`), `Mathlib.RepresentationTheory.Invariants` (for
  `Rep.quotientToInvariants` and `Rep.res`) and
  `Mathlib.Topology.Algebra.Group.ClosedSubgroup`. The focused check below
  confirms that this set suffices.
- **Declarations**: binders, binder kinds, universes, types and bodies are
  unchanged, including the `by exact` body of M004.003 and the
  `letI` instances of M004.004 and M004.005. The underscore names `_hLK` and
  `_hg` and the explicit `hnormal` are kept. No Library or Mathlib definition
  existed for these four constructions over closed subgroups. The existing
  Library uses of `quotientToInvariants` (for example in
  `Langlands/ClassFieldTheory/Local/FixedFieldStageRestriction.lean`) concern
  specific unit representations, not an arbitrary `A` and closed subgroups
  `K`, `L`. The adapted bodies reuse Mathlib's `Subgroup.subgroupOf`,
  `Rep.res`, `Rep.quotientToInvariants` and `tateCohomology` directly.
- **Docstrings**: the module docstring is replaced by a modification notice
  that keeps the source's convention remark. The source says the
  construction writes multiplicative modules with a right action. Here an
  abelian group is a `ℤ`-linear left representation, and passing between the
  two replaces a generator by its inverse without changing the quotients.
  Declaration docstrings are the source's, with "this construction" changed
  to "the source" and the M004.005 docstring condensed.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The focused module compiles with no errors or warnings. Inspection of
  `SatisfiesCyclicNormKernelVanishing` reports `statement_returns_prop: true`,
  no universe level parameters and only the axioms `propext`,
  `Classical.choice` and `Quot.sound`.
- A private probe module reproduces source lines 1–5 and 26–102 verbatim,
  with the source's Mathlib imports. The unavailable NYLL import is replaced
  by `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`, and the
  section is closed. The probe imports this file and proves by `rfl` that the
  complete unapplied original and adapted constants are equal: `extensionSubgroup.{u}`
  at an arbitrary universe, `extensionFixedRepresentation`,
  `IsContinuousDiscreteRepresentation` and `SatisfiesCyclicNormKernelVanishing`.
  It also assigns each adapted constant to its explicitly written source
  telescope, and checks by `rfl` that `extensionFixedRepresentation A K L hLK hnormal`
  equals
  `Rep.quotientToInvariants (Rep.res K.toSubgroup.subtype A) (L.toSubgroup.subgroupOf K.toSubgroup)`.
  The `#print` output shows the binder kinds above: `hnormal` is explicit,
  and only `Group` and `TopologicalSpace` are instance-implicit.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. As a private development check, `Mathlib/RepresentationTheory/Invariants.lean`,
  `Mathlib/RepresentationTheory/Rep/Res.lean` and
  `Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean` were
  fetched at that commit from `raw.githubusercontent.com`. Each is
  byte-identical to the project's pin, with SHA-256 respectively
  `e03761020de06e1843a7294e04d0ced3ef9bfab3d6ba3798b401f72a2c2d1810`,
  `920567d8902528136b31c95856921c77c41d08f8eb39178a231245ea69e70d57` and
  `296dabdbf04196374a3378c9d1c9ad80b74adb25961757954b92181c71fc620f`.
  The registered source `mathlib-065356127b1d-rep-closedsubgroup` records
  `Rep/Basic.lean` and `ClosedSubgroup.lean` as byte-identical. In the
  supplement's compare record, the only change to
  `Mathlib/Algebra/Group/Subgroup/Map.lean`, which defines `subgroupOf`, is in
  the proof of `map_symm_eq_iff_map_eq`.

## Scope

This unit supplies two constructions (a subgroup and a representation) and two
predicates. It proves nothing about them. It asserts no host class-formation,
cup-product, Tate, transfer or cohomological-reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
