# Separable field norms as products of embeddings: M164.002–003 targets

This module states two propositions from NYLL's `SeparableNormProduct.lean`.
It also contains the source's local `Fintype` instance M164.001, which both
statements use. Neither statement is proved here.

Throughout, `k` is a field and `Ω` is a separably closed field with a
`k`-algebra structure. `Ω` is **not** assumed algebraically closed, normal over
`k`, or Galois over `k`. All fields are in `Type` (universe 0), as in the source.
Neither definition has universe parameters.

## The local instance M164.001

```lean
noncomputable local instance _root_.Langlands.NYLL.PortInternal.M164.d001
    {k E T : Type} [Field k] [Field E] [Field T]
    [Algebra k E] [Algebra k T]
    [FiniteDimensional k E] [Algebra.IsSeparable k E] :
    Fintype (E →ₐ[k] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k E)
```

For a finite separable extension `E / k` and any field `T` over `k`, this
instance lists the `k`-algebra embeddings `E →ₐ[k] T` through Mathlib's
primitive-element power basis `Field.powerBasisOfFiniteOfSeparable k E`.
`PowerBasis.AlgHom.fintype` builds the list from the roots of the generator's
minimal polynomial in `T`.

The instance is local, as in the source. Its attribute ends at
`end Langlands.NYLL.LocalClassFieldTheory`, so importing this module does not
add a global instance. Mathlib's global instance `minpoly.AlgHom.fintype` is
still the one found outside this module. A development check outside the module
confirmed by `rfl` that `inferInstance : Fintype (E →ₐ[k] T)` is
`minpoly.AlgHom.fintype k E T`. Inside the module, Lean tries the local instance
first because it was declared later. With explicit printing, the products over
`E →ₐ[k] Ω` in both statements below elaborate as
`@Finset.univ _ (Langlands.NYLL.PortInternal.M164.d001 k E Ω …)`.
This is the same instance choice as in the original.

The source instance is named `LocalClassFieldTheory.finiteSeparableAlgHomFintypeForNormProduct`.
Here it is named `Langlands.NYLL.PortInternal.M164.d001`, the name the port plan
reserves for local source commands
(`notes/reuse/nyll-public-port-plan.md`, section 3, and
`notes/reuse/nyll-public-port/m145-m168.md`, row M164.001).
The `_root_` prefix puts it in that namespace while it is declared inside the
statements' namespace, where the local attribute applies. A future proof of
either target can re-enable it with
`attribute [local instance] Langlands.NYLL.PortInternal.M164.d001`.
Any two `Fintype` instances on a type have equal products, since `Fintype` is a
subsingleton. The instance choice therefore affects only the syntactic form of
the targets, not their meaning.

## M164.002: embeddings in a tower over a power-basis generator

```lean
def prod_embeddings_algebraMap_powerBasisGen_eqStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    {L E : Type} [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Algebra.IsSeparable k E] [FiniteDimensional k E]
    (pb : PowerBasis k L) : Prop :=
  ∏ σ : E →ₐ[k] Ω, σ (algebraMap L E pb.gen) =
    ((@Finset.univ (L →ₐ[k] Ω) (PowerBasis.AlgHom.fintype pb)).prod
      (fun σ => σ pb.gen)) ^ Module.finrank L E
```

`Langlands.NYLL.LocalClassFieldTheory.prod_embeddings_algebraMap_powerBasisGen_eqStatement`
concerns a tower `k ⊆ L ⊆ E` with compatible algebra structures. Both
`L / k` and `E / k` are finite and separable, and `pb` is a `k`-power basis of
`L`. The proposition says that

  ∏_{σ : E → Ω over k} σ(gen) = ( ∏_{τ : L → Ω over k} τ(gen) )^[E : L],

where `gen = pb.gen` is viewed in `E` through `algebraMap L E`, and
`[E : L] = Module.finrank L E`. On the left, the embeddings of `E` are listed by
the local instance M164.001. On the right, the embeddings of `L` are listed
explicitly by `PowerBasis.AlgHom.fintype pb`, the instance written in the source
with `@Finset.univ`.

In mathematical terms: since `Ω` is separably closed and `E / L` is finite
separable, each `k`-embedding `τ` of `L` into `Ω` has exactly `[E : L]`
extensions to `E`. Each of these sends `gen` to `τ(gen)`.

The binders are exactly those of the source theorem, in source order, with the
same explicit/implicit/instance kinds. `k` and `Ω` are explicit, `L` and `E` are
implicit, and `pb` is the last explicit argument. The hypotheses
`[IsSepClosed Ω]`, `[IsScalarTower k L E]`, `[FiniteDimensional k L]` and
`[Algebra.IsSeparable k L]` do not occur in the proposition's body. They are kept
because they are hypotheses of the source theorem. `IsSepClosed Ω` is essential
for the statement to be true. For example, take `k = ℚ`, `L = ℚ(√2)`,
`E = ℚ(√2, i)`, `gen = √2` and the field `Ω = ℝ`, which is not separably closed.
Then `E` has no embedding into `ℝ`, so the left side is the empty product `1`.
The two embeddings of `L` give `√2 · (−√2) = −2`, so the right side is
`(−2)^2 = 4`.

## M164.003: the norm as a product of embeddings

```lean
def algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement
    (k Ω E : Type) [Field k] [Field Ω] [Field E]
    [Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (x : E) : Prop :=
  algebraMap k Ω (Algebra.norm k x) = ∏ σ : E →ₐ[k] Ω, σ x
```

`Langlands.NYLL.LocalClassFieldTheory.algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement`
says that, for a finite separable extension `E / k` and `x ∈ E`, the image in
`Ω` of the field norm `N_{E/k}(x) = Algebra.norm k x` is the product of `σ(x)`
over all `k`-embeddings `σ : E → Ω`. The product is indexed through the local
instance M164.001. The binders `k Ω E` are explicit, followed by the source's
instance arguments in source order and the explicit element `x`. `IsSepClosed Ω`
does not occur in the body, but it is needed for the statement to be true. For
example, for `k = ℚ`, `E = ℚ(i)`, `x = 1 + i` and `Ω = ℝ`, the norm is `2`, but
there are no embeddings, so the product is `1`.

## Source and exact adaptation

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean`,
SHA-256 `a8ed280bf8d7b6c67a804e2f364286aff6857b9e49222e3d21481dcf652fe9d0`
(verified). The complete 94-line file was read. The readable original is
[SeparableNormProduct.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean>).
The source collection is registered as `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library at base `e449cde988d4e97ab280b8d4d11262887ccc26e0` has no NYLL entry
in `notes/errata`. The port inventory records no patch10 change to this module.

| Source (line) | Adaptation |
| --- | --- |
| Header, lines 1–5 | Retained verbatim, followed by a modification note |
| Imports, lines 7–10 | Unchanged: `Mathlib.FieldTheory.PrimitiveElement`, `Mathlib.FieldTheory.IsSepClosed`, `Mathlib.RingTheory.Norm.Transitivity`, `Mathlib.RingTheory.AlgebraTower` |
| Module docstring, lines 12–18 | Rewritten to name the extracted targets and source lines |
| `noncomputable section`, `open scoped BigOperators`, lines 22–24 | Retained |
| `namespace LocalClassFieldTheory`, line 26 | `namespace Langlands.NYLL.LocalClassFieldTheory` |
| Local instance `finiteSeparableAlgHomFintypeForNormProduct`, lines 28–33 (M164.001) | Local instance `Langlands.NYLL.PortInternal.M164.d001`, same telescope and body |
| Theorem `prod_embeddings_algebraMap_powerBasisGen_eq`, signature lines 37–46 (M164.002) | `def … Statement … : Prop` with the same binders and the same equation |
| Its proof, lines 46–65 | Omitted |
| Theorem `algebraMap_norm_eq_prod_embeddings_of_isSepClosed`, signature lines 69–74 (M164.003) | `def … Statement … : Prop` with the same binders and the same equation |
| Its proof, lines 74–92 | Omitted |

The namespace, renaming, extraction and omissions are recorded in the Lean
header. Worker 177 wrote this extraction directly from the pinned original. No
draft or compatibility patch was reused.

## Reuse and related results

No existing Mathlib or Library declaration states either target at the source's
generality. The candidates inspected were:

- Mathlib `Algebra.prod_embeddings_eq_finrank_pow`
  (`Mathlib/RingTheory/Norm/Basic.lean`, line 192) has the same equation as
  M164.002, but assumes `[IsAlgClosed E]` for the ambient field. Its product over
  the upper embeddings uses Mathlib's global `minpoly.AlgHom.fintype`.
- Mathlib `Algebra.norm_eq_prod_embeddings`
  (`Mathlib/RingTheory/Norm/Transitivity.lean`, line 268) is M164.003 with
  `[IsAlgClosed E]` in place of `[IsSepClosed Ω]`.
- Library `Langlands.ClassField.Global.algebraMap_norm_eq_prod_algHom`
  (`Langlands/ClassField/Global/IdeleClassNormEmbeddingProduct.lean`) takes the
  product in a field `E` that contains `K` through a scalar tower and is normal
  over `F`, with a supplied `Fintype` instance.

Every algebraically closed field is separably closed, so the NYLL statements
generalize the Mathlib results. The Library theorem has a different setting.
These results are reuse candidates for a future proof, not replacements for the
targets.

Source route, recorded only as context for the proof tasks: the source proves
M164.002 by reindexing the embeddings of `E` through Mathlib's
`algHomEquivSigma` and counting the extensions of each embedding of `L` with
`AlgHom.natCard_of_splits` and `IsSepClosed.splits_codomain`. It proves M164.003
by reducing to `k⟮x⟯` with `Algebra.norm_eq_norm_adjoin`, then applying
`Algebra.norm_eq_prod_embeddings_gen` and M164.002 to the adjoined power basis.
In a private development check, both source proofs, with `d001` re-enabled
locally, closed these exact targets (M164.003 using M164.002 as a hypothesis).
That check is not a proof publication.

## Development validation

The module compiled in the Lean service, environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings. Both
declarations were inspected. Each inspection reports kind `definition`, no
universe level parameters and `statement_returns_prop: true`. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`. These development checks are not
independent acceptance.

## Attribution

The original copyright, license and author header is preserved. The existing
Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and full
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged. Their
SHA-256 hashes are `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals. This unit covers source units M164.001–M164.003
of the published NYLL declaration partition. It provides no host reciprocity,
class-formation, cup-product, transfer or Tate-cohomology result.
