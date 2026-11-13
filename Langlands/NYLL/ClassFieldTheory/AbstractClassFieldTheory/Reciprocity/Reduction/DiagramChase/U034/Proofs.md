# NYLL M077.034: additive homomorphisms into abelian groups kill commutators

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_commutator_mem_kernelStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_commutator_mem_kernel`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractReciprocity_commutator_mem_kernelStatement r q hq`, with
the implicit types and instances supplied by elaboration.

Its direct imports are the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.Statements`
([Markdown](../Statements.md)), whose Lean/Markdown pair and imports are
unchanged, and the Mathlib module `Mathlib.GroupTheory.Abelianization.Defs`.
The statement module imports only `Mathlib.Algebra.Exact.Basic` and
`Mathlib.GroupTheory.Commutator.Basic`, which do not provide
`Abelianization.commutator_subset_ker`; the added Mathlib import supplies
that lemma so the original proof can be kept verbatim. It does not affect the
statement.

## Target and parameters

The theorem has, in this order: implicit `Q : Type*` and `B : Type*` (two
independent universe parameters), the instances `[Group Q]` and
`[AddCommGroup B]`, and the explicit parameters `r : Additive Q →+ B`,
`q : Q` and `hq : q ∈ commutator Q`. Here `commutator Q` is Mathlib's
commutator subgroup `⁅⊤, ⊤⁆` of `Q`. Unfolding the published proposition
gives `r (Additive.ofMul q) = 0`: the additive homomorphism `r` vanishes at
the element of `Additive Q` corresponding to `q`. The group `Q` need not be
commutative or finite; only the target `B` is commutative.

## Implemented proof

After `show r (Additive.ofMul q) = 0`, the proof follows the original
unchanged:

1. It defines the multiplicative monoid homomorphism
   `rMul : Q →* Multiplicative B`,
   `x ↦ Multiplicative.ofAdd (r (Additive.ofMul x))`, whose `map_one'` and
   `map_mul'` fields are `r.map_zero` and `r.map_add` (definitionally the
   required equations, since multiplication in `Additive Q` and
   `Multiplicative B` is the addition of the other side).
2. Mathlib's `Abelianization.commutator_subset_ker`
   (`Mathlib/GroupTheory/Abelianization/Defs.lean`, line 72 in the approved
   environment) states `commutator G ≤ f.ker` for every homomorphism `f`
   from a group `G` into a group with commutative multiplication
   (`[IsMulCommutative A]`). It applies to `rMul`, because
   `Multiplicative B` is a commutative group for the additive commutative
   group `B`, and gives `q ∈ rMul.ker` from `hq`.
3. Membership in the kernel is changed to its definitional form
   `Multiplicative.ofAdd (r (Additive.ofMul q)) = 1`, and injectivity of the
   equivalence `Multiplicative.ofAdd` reduces the goal to
   `Multiplicative.ofAdd (r (Additive.ofMul q)) = Multiplicative.ofAdd 0`;
   `simpa using hker` closes it after simp normalizes
   `Multiplicative.ofAdd 0` to `1`.

No auxiliary top-level declaration, instance or `simp` registration is
introduced; `rMul` is a local `let`. A development check (`lean_check` in
the approved environment) compiled the module with no diagnostics; the
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean:748–763`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean#L748-L763):
the docstring at 748–750 (retained), the theorem with its telescope and
conclusion at 751–755, and the proof at 756–763. The partition's unit range
751–768 ends just before M077.035 at line 769; lines 765–768 are that next
theorem's docstring. The declaration sits in namespace `ClassFormation`
inside the source's `section Representation`, but uses none of that
section's variables. The whole-file SHA-256 of the retained snapshot is
`42b99923f18b24748b529f410725f5a763554010151f57e0f8c0c5d943acf613`, as
recorded in the
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m077)
row `M077.034`, recomputed by Worker 60 on 13 November 2026.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_commutator_mem_kernel` (M077.034) | Published `abstractReciprocity_commutator_mem_kernelStatement` in DiagramChase.Statements |
| Proof `abstractReciprocity_commutator_mem_kernel` | This theorem of the same adapted name in DiagramChase.U034.Proofs |

Modifications by Worker 60, 13 November 2026: add the `Langlands.NYLL`
namespace prefix; replace the source imports by the published statement
import and the focused Mathlib import
`Mathlib.GroupTheory.Abelianization.Defs`; state the theorem's type as the
published proposition applied to the source parameters; insert the initial
`show` step; omit the source `open`s, `noncomputable section`, universe,
section variables and all other source declarations. The binders, docstring
and all proof steps are otherwise unchanged. The original needed no change
for the approved environment. This proof does not use M077.032 or M077.033.

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

This is only the automatic inclusion of the commutator subgroup in the
kernel. The reverse inclusion for the actual maximal abelian intermediate
field (M077.035, `abstractReciprocity_abelianReduction_kernel`) and every
reciprocity, class-formation, cup, transfer or Tate result are separate.
