# NYLL M010.035: cardinal fundamental identity

This proof adapts Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`:

- `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
  lines 273–282 (M010.035), file SHA-256
  `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
- `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`,
  lines 267–312 (M006.025), file SHA-256
  `da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.

Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The theorem
`Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal`
has exactly the published same-name `Statement` applied to `(E, D)` as its
type. Its parameters are implicit `{G : Type u} [Group G]
[TopologicalSpace G]`, then explicit `(E : AbstractExtension G)`
and `(D : DegreeData G)`. It equates the degree cardinal with the product
of the universe-`u` lift of the Type-zero relative residue cardinal and
the relative ramification cardinal. Infinite cardinalities are included.

The imported theorem `relativeIndexCardinal_eq_map_mul_inf_ker` implements
the source M006.025 argument. For a homomorphism
`d` and an inclusion `L ≤ K`, factor the relative index through
`K ⊓ (L ⊔ ker d)`. Apply the published `relativeIndexCardinal_mul`
(M006.014), then identify the inner index with the kernel-intersection
index using `relativeIndexCardinal_kernel_eq_saturation` (M006.024)
and the outer index with the lifted image index using
`intersectionIndexCardinal_image_eq_saturation` (M006.023). Commutativity
puts the factors in the required order. Both independent universes and
their lifts are preserved by this theorem.

The final proof applies this theorem to `D.degree.toMonoidHom` and `E.below`,
unfolds the three abstract-extension cardinal definitions and simplifies
the Type-zero lift. Its proof route is the source route. The direct imports
are the published `AbstractExtension.CardinalStatements` target and the
`Indices.U025.Proofs` module. No finite-index, normality, profiniteness or topological-group
hypothesis is added.

Worker 183 extracted the proof, prefixed the namespace with
`Langlands.NYLL`, used the published proposition as the theorem's type
and originally kept M006.025 local under a private name. Integration replaces
that duplicate with the published M006.025 theorem, with the same cardinal identity. The original
copyright and author header is retained. See `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support proof supplies no host reciprocity assertion.
