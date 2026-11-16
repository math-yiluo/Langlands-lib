# NYLL M076.012: `intermediateSubgroup_isClosed`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_isClosed`
has the telescope `{G : Type u_1} [Group G] [TopologicalSpace G]
[IsTopologicalGroup G] {K : ClosedSubgroup G}
(L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)` and type
`intermediateSubgroup_isClosedStatement L S`, the published target
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_isClosedStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements`.
It says that the inverse image `L.intermediateSubgroup S` in `G_K` of a
subgroup `S ≤ G(L/K)` under the quotient map is closed for the subspace
topology on `G_K`.

## Implemented proof

Write `H = extensionSubgroup K L.field L.below` for `G_L` inside `G_K`.

1. `intermediateSubgroup_eq_iUnion_cosets_local` (private; local copy of
   source M076.009, lines 139–154): as sets,
   `L.intermediateSubgroup S = ⋃ q ∈ S, L.intermediateCoset q`. An element
   `x` of the inverse image lies in the coset of its own class
   `L.extensionQuotientMk x ∈ S`; conversely an `x` in the coset of some
   `q ∈ S` has class `q ∈ S`. Both memberships hold by definition, as in the
   source's uses of `mem_intermediateSubgroup_iff` (M076.002) and
   `mem_intermediateCoset_iff` (M076.006), which are here replaced by
   `change` and `rfl`.
2. `intermediateCoset_isClosed_local` (private; same statement as source
   M076.011, lines 165–168): choose a representative `r` of `q` by
   surjectivity of `QuotientGroup.mk'`. The coset of class `q` is then the
   preimage of `H` under the continuous map `x ↦ r⁻¹ * x`, because
   `mk r = mk x ↔ r⁻¹ * x ∈ H` (Mathlib's `QuotientGroup.eq`). Since `H` is
   closed by the published theorem
   `Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed` (M020.008), the
   preimage is closed.
3. The theorem unfolds its target with `change`, rewrites with step 1, and
   applies `Set.Finite.isClosed_biUnion`: `S` is a finite set because
   `L.extensionQuotient` is finite (the published instance
   `extensionQuotient_finiteInstance`), and every member of the union is
   closed by step 2.

## Dependencies

- Imported published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements`
  (the target and, through it, `intermediateSubgroup`, `intermediateCoset`
  and the `FiniteGaloisSubextension` data and instances) and
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U008.Proofs`
  (`Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed`).
- The source proof also cites M076.009 (routed to Task
  `333af9cf-9695-44da-ba45-07815b6c6b71`) and M076.011 (staged by this task
  as candidate `7786d562-bfc2-456c-bf03-ca29a11211a1`). Neither is in the
  Library at this file's base, so both statements are proved here as private
  theorems under non-conflicting names; no published or candidate name is
  redeclared.
- Mathlib: `Set.mem_iUnion₂`, `QuotientGroup.mk'_surjective`,
  `QuotientGroup.eq`, `IsClosed.preimage`, `Continuous.mul`,
  `Set.toFinite` and `Set.Finite.isClosed_biUnion`.
- Axioms: `propext`, `Classical.choice` and `Quot.sound` only.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
(file SHA-256 `f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`),
lines 172–178 (M076.012), with the cited units at lines 139–154 (M076.009)
and 165–168 (M076.011). The readable pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 756, 16 November 2026:

- The namespace is prefixed with `Langlands.NYLL`; the source imports are
  replaced by the two published modules above, and the unused
  `open KummerTheory` is dropped.
- The theorem's type is the published `Statement` applied to the source
  parameters; the source section instance `[IsTopologicalGroup G]` and
  `{K : ClosedSubgroup G}` are explicit binders, matching the statement's
  telescope.
- The source's local `let : Finite L.extensionQuotient := L.finite` is
  dropped, because the published instance supplies the same finiteness.
- The two cited unpublished results are proved locally as described above;
  the coset closedness uses a preimage of `G_L` under left translation by
  `r⁻¹` instead of the source's image of `G_L` under right translation by
  `r`.

The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract topological-group result. It supplies no host
class-formation, cup-product, transfer, Tate-cohomology or reciprocity
theorem.
