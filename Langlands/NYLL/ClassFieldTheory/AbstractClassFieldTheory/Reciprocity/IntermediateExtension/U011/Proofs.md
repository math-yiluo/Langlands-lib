# NYLL M076.011: `intermediateCoset_isClosed`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.intermediateCoset_isClosed`
has the telescope `{G : Type u_1} [Group G] [TopologicalSpace G]
[IsTopologicalGroup G] {K : ClosedSubgroup G}
(L : FiniteGaloisSubextension K) (q : L.extensionQuotient)` and type
`intermediateCoset_isClosedStatement L q`, the published target
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.intermediateCoset_isClosedStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements`.
It says that the canonical coset
`L.intermediateCoset q = {x | L.extensionQuotientMk x = q}`, the fiber over
`q ∈ G(L/K)` of the quotient map `G_K → G(L/K)`, is closed in `G_K` with its
subspace topology.

## Implemented proof

The proof follows the source proof (lines 165–171) and its private helpers.
Write `r = Quotient.out (L.extensionQuotientMulEquiv q) : K.toSubgroup` for a
chosen representative of `q` and `H = extensionSubgroup K L.field L.below`
for `G_L` regarded as a subgroup of `G_K`.

1. `mem_representativeIntermediateCoset_iff` (private; source M076.007,
   lines 93–128): `x` lies in the image of `H` under right multiplication by
   `r` if and only if `L.extensionQuotientMk x = q`. For `x = h * r` with
   `h ∈ H`, the classes of `h * r` and `r` agree by
   `QuotientGroup.eq_iff_div_mem`, since `(h * r) / r = h`; the class of
   `r` is `q` by `Quotient.out_eq'`. Conversely, if `x` has class `q`, then
   `x / r ∈ H` by `QuotientGroup.eq_iff_div_mem`, and `x = (x / r) * r`.
   The source rewrites with `extensionQuotientMk_apply` (M040.012); here the
   same definitional identity is used through `change` and `rfl`, because
   `extensionQuotientMulEquiv` is `MulEquiv.refl`.
2. `intermediateCoset_eq_representativeIntermediateCoset` (private; source
   M076.008, lines 130–134): by extensionality and step 1, the canonical
   coset equals that right translate of `H`.
3. `representativeIntermediateCoset_isClosed` (private; source M076.010,
   lines 156–163): the right translate of `H` is closed, because right
   multiplication by `r` is a closed map of the topological group
   `K.toSubgroup` (Mathlib's `isClosedMap_mul_right`) and `H` is closed by
   the published theorem
   `Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed` (M020.008).
4. The theorem unfolds its target with `change`, rewrites with step 2 and
   concludes with step 3.

## Dependencies

- Imported published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements`
  (the target and, through it, `intermediateCoset`, `FiniteGaloisSubextension`,
  `extensionQuotient`, `extensionQuotientMk` and `extensionQuotientMulEquiv`)
  and
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U008.Proofs`
  (`Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed`).
- Mathlib: `Quotient.out_eq'`, `QuotientGroup.eq_iff_div_mem`,
  `isClosedMap_mul_right` and the topological-group instance on a subgroup.
- No unpublished theorem is used, no published name is redeclared, and no
  axiom beyond `propext`, `Classical.choice` and `Quot.sound` is used.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
(file SHA-256 `f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`),
lines 78–82 (M076.005), 93–134 (M076.007, M076.008), 156–171 (M076.010,
M076.011). The readable pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 756, 16 November 2026:

- The namespace is prefixed with `Langlands.NYLL`; the source imports are
  replaced by the two published modules above; the unused
  `open KummerTheory` is dropped and `extensionSubgroup_isClosed` is cited by
  its full published name.
- The theorem's type is the published `Statement` applied to the source
  parameters, and the source section instance `[IsTopologicalGroup G]` and
  `{K : ClosedSubgroup G}` are written as explicit binders of the theorem,
  matching the statement's telescope.
- The source-private definition `representativeIntermediateCoset`
  (M076.005) is not declared; its body, the image of `H` under
  `fun y => y * r`, is written inline in the three private helpers, which
  keep their source names and are private to this module.
- In helper M076.007 the rewrite by `L.extensionQuotientMk_apply` and the
  unused local `L.normal` instance are replaced by a `change` and `rfl`
  for the same definitional equation.

The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract topological-group result. It supplies no host
class-formation, cup-product, transfer, Tate-cohomology or reciprocity
theorem.
