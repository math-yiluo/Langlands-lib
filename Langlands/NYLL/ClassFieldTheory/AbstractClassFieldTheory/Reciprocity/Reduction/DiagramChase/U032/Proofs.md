# NYLL M077.032: surjectivity of the middle arrow from an exact diagram

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_surjective_of_exact_diagramStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_surjective_of_exact_diagram`.
The theorem's type is exactly that proposition applied to its source
parameters,

```lean
abstractReciprocity_surjective_of_exact_diagramStatement
  iQ pQ iB pB r₀ r r₁ hexact hpQ hleft hright hr₀ hr₁
```

with the six implicit types and their `AddGroup` instances supplied by
elaboration. Its sole direct import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.Statements`
([Markdown](../Statements.md)); that Lean/Markdown pair and its imports are
unchanged.

## Target and parameters

The theorem has, in this order: implicit `Q₀ Q Q₁ B₀ B B₁ : Type*` (six
independent universe parameters, as in the source); the six instances
`[AddGroup _]`, so none of the groups need be commutative; the additive
homomorphisms `iQ : Q₀ →+ Q`, `pQ : Q →+ Q₁`, `iB : B₀ →+ B`, `pB : B →+ B₁`,
`r₀ : Q₀ →+ B₀`, `r : Q →+ B`, `r₁ : Q₁ →+ B₁`; and the explicit hypotheses

- `hexact : Function.Exact iB pB` (the bottom row is exact at `B`, that is
  `pB y = 0 ↔ y ∈ Set.range iB` for every `y : B`);
- `hpQ : Function.Surjective pQ`;
- `hleft : ∀ q, r (iQ q) = iB (r₀ q)` and
  `hright : ∀ q, pB (r q) = r₁ (pQ q)` (the two squares commute);
- `hr₀ : Function.Surjective r₀` and `hr₁ : Function.Surjective r₁`.

Unfolding the published proposition gives `Function.Surjective r`. No
exactness of the top row and no injectivity hypothesis is assumed.

## Implemented proof

The proof first exposes the unfolded goal with
`show Function.Surjective r`, then follows the original proof unchanged.
Given `b : B`:

1. `hr₁ (pB b)` gives `q₁ : Q₁` with `r₁ q₁ = pB b`, and `hpQ q₁` gives
   `q : Q` with `pQ q = q₁`.
2. A `calc` chain shows `pB (b - r q) = 0`: by `map_sub`,
   `pB (b - r q) = pB b - pB (r q)`; `hright q` rewrites `pB (r q)` to
   `r₁ (pQ q)`, which is `r₁ q₁ = pB b` by the two choices; `sub_self`
   finishes.
3. Exactness `(hexact (b - r q)).mp` turns this into `b₀ : B₀` with
   `iB b₀ = b - r q`, and `hr₀ b₀` gives `q₀ : Q₀` with `r₀ q₀ = b₀`.
4. The preimage is `iQ q₀ + q`: by `map_add`, `hleft q₀`, the choice of `q₀`
   and of `b₀`, `r (iQ q₀ + q) = iB (r₀ q₀) + r q = (b - r q) + r q`, which
   is `b` by `sub_add_cancel`.

Only subtraction and addition in the possibly noncommutative group `B` are
used, in the order `(b - r q) + r q`, so no commutativity is needed. The
proof uses only Mathlib's `map_sub`, `map_add`, `sub_self`, `sub_add_cancel`
and the definitions of `Function.Exact` and `Function.Surjective`, all
available through the statement module's import of
`Mathlib.Algebra.Exact.Basic`. No auxiliary declaration, instance or `simp`
registration is introduced. A development check (`lean_check` in the
approved environment) compiled the module with no diagnostics; the theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean:666–702`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean#L666-L702):
the docstring at 666–669 (retained), the theorem with its telescope and
conclusion at 670–683, and the proof at 684–702. The partition's unit range
670–706 ends just before M077.033 at line 707; lines 704–706 are that next
theorem's docstring. The declaration sits in
namespace `ClassFormation` inside the source's `section Representation`, but
uses none of that section's variables. The whole-file SHA-256 of the
retained snapshot is
`42b99923f18b24748b529f410725f5a763554010151f57e0f8c0c5d943acf613`, as
recorded in the
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m077)
row `M077.032`, recomputed by Worker 60 on 13 November 2026.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_surjective_of_exact_diagram` (M077.032) | Published `abstractReciprocity_surjective_of_exact_diagramStatement` in DiagramChase.Statements |
| Proof `abstractReciprocity_surjective_of_exact_diagram` | This theorem of the same adapted name in DiagramChase.U032.Proofs |

Modifications by Worker 60, 13 November 2026: add the `Langlands.NYLL`
namespace prefix; replace the source imports by the sole published
statement import; state the theorem's type as the published proposition
applied to the source parameters; insert the initial `show` step; omit the
source `open`s, `noncomputable section`, universe, section variables and all
other source declarations. The binders, docstring and all proof steps are
otherwise unchanged. The original needed no change for the approved
environment.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 60's dated modification
record. Worker 60 extracted this proof directly from the pinned original
and the published statement by Worker 68. No project draft was reused and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively. No Mathlib code is copied.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance; publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
independent semantic review and Integrator publication.

This is the abstract diagram chase only. It supplies no reciprocity
homomorphism, class-formation, cup, transfer or Tate result. M077.033
(bijectivity) and M077.034 (commutator kernel) are separate proofs.
