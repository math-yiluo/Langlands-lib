# NYLL M006.025: cardinal image–kernel factorization

The paired Lean file proves the published proposition
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_eq_map_mul_inf_kerStatement`
under the source-adapted name
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_eq_map_mul_inf_ker`.
It retains independent universes `u v`, implicit groups `G : Type u` and
`D : Type v`, explicit `d : G →* D`, implicit subgroups `L K`, and explicit
`hLK : L ≤ K`, in that order. The theorem's declared type is exactly the
named target applied to `d hLK`.

It equates `Cardinal.lift.{v} (relativeIndexCardinal hLK)` with the product
of `Cardinal.lift.{u}` of the image inclusion index and `Cardinal.lift.{v}`
of the kernel-intersection inclusion index. All indices are cardinalities
of actual coset spaces; no finiteness or subgroup-normality premise is added.

## Implemented proof and dependencies

Set `S = K ⊓ (L ⊔ d.ker)`. The containment `hLK` gives `L ≤ S`, and
intersection gives `S ≤ K`. The published theorem
`relativeIndexCardinal_mul` factors the index of `L ≤ K` as the product
of the indices of `L ≤ S` and `S ≤ K`. `Cardinal.lift_mul` lifts that
product to the common universe. The published
`relativeIndexCardinal_kernel_eq_saturation` identifies the first factor
with the index of `L ⊓ d.ker ≤ K ⊓ d.ker`, and
`intersectionIndexCardinal_image_eq_saturation` identifies the second
factor with the lifted index of `L.map d ≤ K.map d`. Unfolding
`relativeIndexCardinal` exposes the common intersection-index expressions
for these rewrites. Finally, `mul_comm` puts the image factor first.

The direct imports are the target module `Indices.U023.Statements` and
the three proof modules `Indices.U014.Proofs`, `Indices.U023.Proofs`, and
`Indices.U024.Proofs`, all under
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree`.
The cardinal definitions come from the transitive import
`Indices.U010.Definitions`. The tower proof uses the published coset-tower
equivalence; the image and kernel proofs use equivalences of actual coset
spaces. This file introduces no duplicate prerequisite theorem or new data
construction. The target Lean/Markdown pair and its imports are unchanged.

## Source and adaptation

This is source unit M006.025 of Naganori Yamaguchi's ClassFieldTheory,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`:
docstring lines 267–269, theorem signature 270–277, proof 278–312.
Source file SHA-256:
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
The registered originals are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 189 extracted the theorem, prefixed its namespace with
`Langlands.NYLL`, replaced the broad source import with focused published
imports, and used the published Prop-valued target as the result type.
The proof first unfolds that target. Its local kernel equality is supplied
directly by the published theorem through definitional equality, replacing
the source's `simpa only [relativeIndexCardinal]`. The saturated subgroup,
cardinal lifts, factor order and remaining proof steps follow the source.

The original copyright and author header remain in the Lean file. The
Apache-2.0 files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
retained unchanged. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This support proof asserts no host class-formation, cup, transfer, Tate or
reciprocity result.
