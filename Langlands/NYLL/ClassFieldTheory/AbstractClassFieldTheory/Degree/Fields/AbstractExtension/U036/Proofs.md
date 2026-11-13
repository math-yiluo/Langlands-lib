# NYLL M010.036: cardinal residue-degree compatibility

This proof adapts Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
lines 286–302 (M010.036). The file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The theorem
`Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`
has exactly the published same-name `Statement` applied to `(E, D)` as its
type. Its parameters are implicit `{G : Type u} [Group G]
[TopologicalSpace G]`, then explicit `(E : AbstractExtension G)`
and `(D : DegreeData G)`. The product is the relative residue cardinal
followed by the absolute residue cardinal of the base, and equals the
absolute residue cardinal of the extension field. These cardinals all
lie in universe zero; no lift is introduced.

The proof changes the target to intersection indices of the actual degree
images. The published `DegreeData.fieldImage_eq_map` (M010.011) identifies
the two absolute degree images with subgroup images. Apply the published
`relativeIndexCardinal_mul` (M006.014) to the image-subgroup tower
`d(E.field) ≤ d(E.base) ≤ ⊤`; unfolding its proposition wrapper and
`relativeIndexCardinal` gives the required identity in the source factor
order. This is the original proof route and includes infinite indices.

The direct imports are the published `AbstractExtension.CardinalStatements`
target, `Fields.U011.Proofs` and `Indices.U014.Proofs`. M010.035 is not a
dependency. No finiteness, normality, profiniteness or topological-group
hypothesis is added.

Worker 183 extracted the proof, prefixed its namespace with
`Langlands.NYLL`, used the published proposition as its type and
explicitly unfolded the product theorem's `Statement` wrapper in the
final simplification. The original copyright and author header is retained.
See `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support proof supplies no host reciprocity assertion.
