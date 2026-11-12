# The norm as a product of embeddings into a separably closed field

`Langlands.NYLL.LocalClassFieldTheory.algebraMap_norm_eq_prod_embeddings_of_isSepClosed`
proves the already published proposition
`Langlands.NYLL.LocalClassFieldTheory.algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement`.
Its complete telescope is:

```lean
(k Ω E : Type) [Field k] [Field Ω] [Field E]
[Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
[FiniteDimensional k E] [Algebra.IsSeparable k E]
(x : E) :
algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement k Ω E x
```

All three fields are in universe zero. The field parameters `k`, `Ω` and `E`
and the element `x` are explicit; every instance argument is retained in the
published target's order. The equation is

```lean
algebraMap k Ω (Algebra.norm k x) = ∏ σ : E →ₐ[k] Ω, σ x
```

The ambient field is assumed separably closed. No algebraic closedness,
normality or Galois hypothesis is added.

## Implemented proof

Let `L = IntermediateField.adjoin k ({x} : Set E)`, the simple intermediate
field `k⟮x⟯`. The proof follows the pinned source's reduction.

1. `Algebra.IsSeparable.isIntegral k x` supplies integrality of `x`.
   `Algebra.isSeparable_tower_bot_of_isSeparable k L E` installs separability
   of `L / k` locally. The standard intermediate-field instances supply its
   algebra structures, scalar tower and finite dimension.
2. `Algebra.norm_eq_norm_adjoin k x` expresses the norm from `E` as the norm
   of the canonical generator of `L`, raised to `Module.finrank L E`.
   `map_pow` moves this power through `algebraMap k Ω`.
3. `IntermediateField.adjoin.powerBasis_gen` identifies the canonical generator
   with the generator of `IntermediateField.adjoin.powerBasis hx`.
   `IsSepClosed.splits_codomain`, applied to that generator's separability,
   supplies the splitting hypothesis for `Algebra.norm_eq_prod_embeddings_gen Ω`.
   This computes the generator's norm as the product over `L →ₐ[k] Ω`.
   The remaining separability premise of that norm theorem is discharged by
   `Algebra.IsSeparable.isSeparable k _`.
4. The published theorem
   `Langlands.NYLL.LocalClassFieldTheory.prod_embeddings_algebraMap_powerBasisGen_eq`
   (M164.002), applied to `L`, `E` and this power basis, identifies that product
   raised to `Module.finrank L E` with the product over `E →ₐ[k] Ω`.
   Its symmetric equality closes the goal after simplification by
   `IntermediateField.adjoin.powerBasis_gen` and
   `IntermediateField.AdjoinSimple.algebraMap_gen`.

The module re-enables the existing
`Langlands.NYLL.PortInternal.M164.d001` with `attribute [local instance]`.
It supplies exactly the target's `Fintype (E →ₐ[k] Ω)`. The enumeration of
`L →ₐ[k] Ω` in the norm theorem and in M164.002 is explicitly
`PowerBasis.AlgHom.fintype` of the same power basis. No instance is defined
or exported globally by this proof module.

The only direct imports are the unchanged published
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.Statements`
and
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.U002.Proofs`.
The statement module already imports
`Mathlib.FieldTheory.PrimitiveElement`, `Mathlib.FieldTheory.IsSepClosed`,
`Mathlib.RingTheory.Norm.Transitivity` and `Mathlib.RingTheory.AlgebraTower`.
The U002 proof contains the separably closed embedding-count argument; this
module reuses it rather than repeating it. Mathlib's
`Algebra.norm_eq_prod_embeddings` requires an algebraically closed ambient field,
so it does not directly close this target.

## Source, attribution and modifications

This adapts only M164.003 from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean`,
theorem lines 69–92, signature lines 69–74. The complete 94-line original was
read. Its verified SHA-256 is
`a8ed280bf8d7b6c67a804e2f364286aff6857b9e49222e3d21481dcf652fe9d0`.
The readable original is
[SeparableNormProduct.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean>).
The collection is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL erratum was present in the current Library's `notes/errata` lookup.

The original copyright, Apache-2.0 license and author header are retained
verbatim, followed by a modification note. The unchanged Library
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are byte-identical to the
pinned originals, with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Original authorship is Naganori Yamaguchi (assisted by OpenAI Codex);
Worker 169 adapted this proof.

The adaptation extracts the theorem into the required `U003/Proofs.lean` file,
adds the `Langlands.NYLL` namespace prefix, and replaces the literal equation
in the theorem's signature with the published Prop target. The proof first
unfolds that target, then retains the original proof body and proof route,
calling the separately published M164.002 theorem under its adapted name.
It reuses the already published M164.001 local instance instead of redeclaring
it and replaces the original four direct Mathlib imports with the two
published module imports above. The published target pair and imported
Lean/Markdown pairs are unchanged.

## Development validation and scope

The complete theorem compiled with no errors or warnings after importing the
independently published M164.002 proof, using project Lean environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Declaration inspection reports
kind `theorem`, no universe level parameters, and exactly the axioms
`propext`, `Classical.choice` and `Quot.sound`. Development compilation and
inspection are not independent acceptance or publication.

This support result has no host class-formation, cup-product, Tate,
transfer or reciprocity conclusion.
