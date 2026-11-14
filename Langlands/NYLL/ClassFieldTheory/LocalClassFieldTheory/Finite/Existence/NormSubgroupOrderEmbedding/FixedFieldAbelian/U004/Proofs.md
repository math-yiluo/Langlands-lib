# NYLL M300.004: the represented fixed field is abelian Galois

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_fixedField_isAbelianGaloisStatement`
with the complete source telescope:

```lean
theorem finiteAbelianSubextension_fixedField_isAbelianGalois
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_fixedField_isAbelianGaloisStatement K L
```

The namespace is `Langlands.NYLL.LocalClassFieldTheory`. Here `K` is an
arbitrary field in universe zero, and `L` is the published finite abelian
subextension package over the closed subgroup fixing the bottom intermediate
field of `SeparableClosure K / K`. Writing
`E = abstractFixedField K (SeparableClosure K) L.field`, the conclusion is
exactly Mathlib's `IsAbelianGalois K E`: the concrete fixed field is Galois
over `K` and its actual automorphism group is commutative. No Galois,
commutativity, valuation or local-field hypothesis is supplied to this theorem.
Finite dimensionality is constructed locally in the proof; it is not an
additional conclusion of the target.

## Implemented proof

The proof follows the pinned source's quotient transport argument.

1. Install finiteness of the quotient over the abstract absolute base using
   the published `finiteAbelianSubextension_finite_over_absoluteBase`
   (M300.001). Apply `abstractFixedField_finiteDimensional` (M099.005) to
   obtain a local `FiniteDimensional K E` instance. Apply
   `abstractFixedField_isGalois_of_base_normal` (M299.005) to the published
   `finiteAbelianSubextension_normal_over_absoluteBase` (M300.002) to obtain
   a local `IsGalois K E` instance. The normality instance for the relative
   subgroup over `intrinsicAbstractBase K` comes from `L.normal`.
2. Use `closedFixingSubgroup_abstractFixedField_eq` (M099.002) to recover
   `L.field` from `E`. Extensionality then identifies its relative extension
   subgroup with the one in the package. Membership in these two subgroups
   reduces definitionally to membership of the underlying automorphism in
   the corresponding closed subgroup, so `change` and the recovered equality
   suffice.
3. Compose `L.extensionQuotientMulEquiv`,
   `QuotientGroup.quotientMulEquivOfEq` for that equality, and the published
   `baseFixingExtensionQuotientEquivGaloisGroup` (M089.011). This constructs
   `e : L.extensionQuotient ≃* Gal(E / K)`.
4. The published `CommGroup L.extensionQuotient` instance uses the package's
   commutativity field. For arbitrary automorphisms, apply injectivity of
   `e.symm` and its multiplication law to transport `mul_comm` to
   `Gal(E / K)`. Together with the local Galois instance this constructs the
   required `IsAbelianGalois` structure.

All prerequisites are imported by their published Lean module names; this
module introduces only the requested theorem and no global instance.

## Provenance and modifications

The proof is adapted by Worker 667 from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean#L83-L124),
unit M300.004, lines 83–124. The source file's SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
The source is retained in the project's registered collections
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`. No NYLL erratum is recorded in
the current Library's errata notes.

The modifications are:

- Prefix the source namespace with `Langlands.NYLL`, give the source section
  parameters `(K : Type) [Field K]` explicitly on the theorem, and express
  its result as the published proposition target applied to `K` and `L`.
  The source binder kinds, order and universe-zero scope are preserved.
- Replace the broad source imports with the target statement and focused
  published proof/definition modules supplying the prerequisites above.
  Keep the `noncomputable section` and used namespace openings; omit the
  unused `LocalFieldTheory` and `KummerTheory` openings.
- Replace the two source `mem_extensionSubgroup_iff` rewrites in the subgroup
  equality proof (line 117) with `change`, using the published definition
  of `extensionSubgroup`. The rest of the proof, including the local
  finiteness/Galois setup and quotient equivalence, follows source lines
  91–124.
- Add focused module documentation, a modification notice and a shorter
  theorem docstring describing the exact conclusion.

The original copyright and author header is retained. The existing
`licenses/NYLL/LICENSE` (Apache-2.0) and `licenses/NYLL/NOTICE` are unchanged.
The theorem is an adaptation of the pinned original proof, not an original
mathematical assertion.

## Development verification

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, development check
`ffdce8f4-a88a-469f-b42a-7cf5671155f8` compiled this exact theorem module
with zero errors and warnings. Declaration inspection reported a theorem
with no universe parameters and only `propext`, `Classical.choice` and
`Quot.sound` as axioms. Candidate validation and independent semantic
review remain separate publication requirements.
