# NYLL M164.002: product of embeddings in a separable tower

`Langlands.NYLL.LocalClassFieldTheory.prod_embeddings_algebraMap_powerBasisGen_eq`
proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.prod_embeddings_algebraMap_powerBasisGen_eqStatement`.
Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.Statements`.
The published statement and its imports are unchanged.

The theorem retains the complete source telescope in its original order and
with its original binder kinds: explicit `k Ω : Type`, their fields, `Algebra k Ω`
and `IsSepClosed Ω`; implicit `L E : Type`, their fields, the three source
algebras and `IsScalarTower k L E`; finite dimensionality and separability of
`L/k`, separability and finite dimensionality of `E/k`; and the explicit power
basis `pb : PowerBasis k L`. All four fields have universe zero.

For these data, the theorem asserts

\[
\prod_{\sigma:E\to_k\Omega}\sigma(\operatorname{algebraMap}_{L,E}(pb.gen))
=\left(\prod_{\tau:L\to_k\Omega}\tau(pb.gen)\right)^{[E:L]}.
\]

Here `[E:L]` means `Module.finrank L E`. The left product uses the published
local instance `Langlands.NYLL.PortInternal.M164.d001`; the right product uses
the explicitly specified `PowerBasis.AlgHom.fintype pb`. The proof re-enables
M164.001 locally and uses the same right-hand enumeration. Its conclusion is
the published proposition itself, which preserves both enumerations exactly.

## Implemented proof and dependencies

After unfolding the target, `FiniteDimensional.right k L E` supplies finite
dimensionality of `E/L`, and
`Algebra.isSeparable_tower_top_of_isSeparable k L E` supplies its separability.
`Fintype.prod_equiv algHomEquivSigma` reindexes a `k`-embedding of `E` as a
pair consisting of its restriction `σ : L →ₐ[k] Ω` and an extension over that
restriction. The value of the generator depends only on `σ`; the final
compatibility goal is closed by `AlgHom.comp_apply` for the actual tower map
`IsScalarTower.toAlgHom k L E`.

`Finset.univ_sigma_univ` and `Finset.prod_sigma` split the product into its
fibers. In the fiber of `σ`, the proof installs the algebra structure
`σ.toRingHom.toAlgebra` on `Ω` over `L`. `Finset.prod_const` makes that fiber's
product a power of `σ pb.gen`. After `Finset.card_univ` and
`Fintype.card_eq_nat_card`, `AlgHom.natCard_of_splits L E Ω` identifies the
exponent with `Module.finrank L E`. Its splitting condition follows from
`IsSepClosed.splits_codomain` applied to
`Algebra.IsSeparable.isSeparable L x` for each `x : E`. Finally,
`Finset.prod_pow` gives the required power of the product.

The ambient field is assumed separably closed throughout. The proof does not
invoke Mathlib's `Algebra.prod_embeddings_eq_finrank_pow`, whose ambient field
is assumed algebraically closed. The mathematical ingredients used here are
the Mathlib embedding equivalence, finite-separable embedding count and
splitting of separable polynomials. The statement module also imports norm
transitivity, but this proof uses no norm-product theorem or reciprocity result.

## Source and adaptation

The proof is extracted directly from Naganori Yamaguchi (assisted by OpenAI
Codex), *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean`,
theorem signature lines 37–46 and proof lines 46–65 (M164.002).
The complete 94-line source file was read; its SHA-256 is
`a8ed280bf8d7b6c67a804e2f364286aff6857b9e49222e3d21481dcf652fe9d0`.
The readable original is
[SeparableNormProduct.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean>).
The source collection is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 126 preserved the upstream copyright, Apache-2.0 license and author
header. The adaptations are the `Langlands.NYLL` namespace prefix, extraction
to the required `U002.Proofs` module, import of the published statement module,
local re-enabling of its existing M164.001 instance, and replacement of the
displayed equation in the theorem's type by the published proposition, unfolded
as the first proof step. The proof after unfolding follows the pinned source
verbatim. No compatibility patch or unpublished draft was reused.

The retained license and notice are
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE); their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals. The current Library has no NYLL errata entry.
This unit proves M164.002 only; it supplies no host class-formation, cup-product,
Tate-cohomology, transfer or reciprocity theorem.

## Development validation

The focused module compiled without errors or warnings in the project Lean
service using environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Lean
4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
A separate Lake build and theorem inspection also succeeded. The inspection
reports a theorem with no universe parameters and exactly the axioms
`propext`, `Classical.choice` and `Quot.sound`. Development validation is not
independent semantic acceptance or publication.
