# NYLL M077.033: bijectivity of the middle arrow from an exact diagram

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_bijective_of_exact_diagramStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_bijective_of_exact_diagram`.
The theorem's type is exactly that proposition applied to its source
parameters,

```lean
abstractReciprocity_bijective_of_exact_diagramStatement
  iQ pQ iB pB r₀ r r₁ hexactQ hexactB hpQ hiB hleft hright hr₀ hr₁
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

- `hexactQ : Function.Exact iQ pQ` and `hexactB : Function.Exact iB pB`
  (both rows are exact at the middle);
- `hpQ : Function.Surjective pQ` and `hiB : Function.Injective iB`;
- `hleft : ∀ q, r (iQ q) = iB (r₀ q)` and
  `hright : ∀ q, pB (r q) = r₁ (pQ q)` (the two squares commute);
- `hr₀ : Function.Bijective r₀` and `hr₁ : Function.Bijective r₁`.

Unfolding the published proposition gives `Function.Bijective r`, that is
`Function.Injective r ∧ Function.Surjective r`.

## Implemented proof

The module contains two declarations.

**Private local lemma `surjective_of_exact_diagram_aux`.** The source proof
calls the M077.032 theorem `abstractReciprocity_surjective_of_exact_diagram`,
whose proof is not yet in the Library (it is staged separately by the same
task). As the task permits, this module proves what it needs locally: the
`private theorem surjective_of_exact_diagram_aux` has exactly the source
M077.032 telescope and conclusion `Function.Surjective r` (original lines
670–683) and the original M077.032 proof (lines 684–702) verbatim. Given
`b : B`, it picks `q₁` with `r₁ q₁ = pB b` and `q` with `pQ q = q₁`, shows
`pB (b - r q) = 0` by `map_sub`, `hright q` and `sub_self`, obtains `b₀`
with `iB b₀ = b - r q` from exactness of the bottom row, picks `q₀` with
`r₀ q₀ = b₀`, and checks `r (iQ q₀ + q) = (b - r q) + r q = b` by `map_add`,
`hleft q₀` and `sub_add_cancel`. Being `private` under a name distinct from
the adapted M077.032 name, it publishes no second copy of that theorem and
is not part of this module's public interface.

**Main theorem.** After `show Function.Bijective r`, the proof follows the
original M077.033 proof (lines 723–746) with the single change that the
surjectivity component is supplied by
`surjective_of_exact_diagram_aux iQ pQ iB pB r₀ r r₁ hexactB hpQ hleft hright hr₀.2 hr₁.2`
instead of the source's call of the same arguments to the M077.032 theorem.
Injectivity is proved through Mathlib's `injective_iff_map_eq_zero`: for
`q : Q` with `r q = 0`,

1. `pB (r q) = 0` by `map_zero`, so `r₁ (pQ q) = 0` by `hright q`, and
   injectivity of `r₁` (`hr₁.1`, applied to `r₁ (pQ q) = r₁ 0` obtained by
   `simpa`) gives `pQ q = 0`;
2. exactness of the top row, `(hexactQ q).mp`, gives `q₀ : Q₀` with
   `iQ q₀ = q`;
3. `iB (r₀ q₀) = r (iQ q₀) = r q = 0` by `hleft q₀`, so injectivity of `iB`
   gives `r₀ q₀ = 0`, and injectivity of `r₀` (`hr₀.1`) gives `q₀ = 0`;
4. hence `q = iQ q₀ = iQ 0 = 0` by `map_zero`.

The proof uses only Mathlib's `map_sub`, `map_add`, `map_zero`, `sub_self`,
`sub_add_cancel`, `injective_iff_map_eq_zero`, the `simp` set and the
definitions of `Function.Exact`, `Function.Injective`,
`Function.Surjective` and `Function.Bijective`, all available through the
statement module's import of `Mathlib.Algebra.Exact.Basic`. No instance or
`simp` registration is introduced. A development check (`lean_check` in the
approved environment) compiled the module with no diagnostics; the theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean:704–746`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean#L704-L746):
the docstring at 704–706 (retained), the theorem with its telescope and
conclusion at 707–722, and the proof at 723–746. The partition's unit range
707–750 ends just before M077.034 at line 751; lines 748–750 are that next
theorem's docstring. The local lemma reproduces lines 670–702 (M077.032).
The declarations sit in namespace `ClassFormation` inside the source's
`section Representation`, but use none of that section's variables. The
whole-file SHA-256 of the retained snapshot is
`42b99923f18b24748b529f410725f5a763554010151f57e0f8c0c5d943acf613`, as
recorded in the
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m077)
row `M077.033`, recomputed by Worker 60 on 13 November 2026.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_bijective_of_exact_diagram` (M077.033) | Published `abstractReciprocity_bijective_of_exact_diagramStatement` in DiagramChase.Statements |
| Proof `abstractReciprocity_bijective_of_exact_diagram` | This theorem of the same adapted name in DiagramChase.U033.Proofs |
| `abstractReciprocity_surjective_of_exact_diagram` (M077.032), as used here | Private local copy `surjective_of_exact_diagram_aux` in this module |

Modifications by Worker 60, 13 November 2026: add the `Langlands.NYLL`
namespace prefix; replace the source imports by the sole published
statement import; state the theorem's type as the published proposition
applied to the source parameters; insert the initial `show` step; replace
the call to the unpublished M077.032 theorem by the private local lemma
described above; omit the source `open`s, `noncomputable section`, universe,
section variables and all other source declarations. The binders,
docstring and all other proof steps are unchanged. The original needed no
other change for the approved environment. Once the M077.032 proof is
published, a later revision may import it instead of the local lemma; this
does not change the theorem's type.

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
homomorphism, class-formation, cup, transfer or Tate result.
