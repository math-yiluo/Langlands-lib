# NYLL M078.005: Sylow subgroups of an abelian group lie in coprime multiples

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprimeStatement`
by the theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprime`.
The theorem's type is exactly that proposition applied to its source
parameters, `sylowAddSubgroup_le_nsmul_range_of_coprimeStatement S hn`, with
the implicit type, natural numbers and instances supplied by elaboration.
Its sole direct import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Sylow.CoprimeNsmul.Statements`
([Markdown](../Statements.md)); that Lean/Markdown pair and its imports are
unchanged.

## Target and parameters

The theorem has, in this order: implicit `B : Type*` (one universe
parameter) with `[AddCommGroup B]`; implicit `p n : ℕ` with
`[Fact p.Prime]`; and the explicit parameters
`S : Sylow p (Multiplicative B)` and `hn : Nat.Coprime n p`. Mathlib's
`Sylow p G` is a maximal `p`-subgroup of `G` and is defined without any
finiteness assumption, so `B` may be infinite. Unfolding the published
proposition gives

```lean
Subgroup.toAddSubgroup' (S : Subgroup (Multiplicative B)) ≤
  (nsmulAddMonoidHom (α := B) n).range
```

that is, every `x : B` with `Multiplicative.ofAdd x ∈ S` is `n • y` for some
`y : B`. Here `Subgroup.toAddSubgroup'` is Mathlib's order isomorphism from
subgroups of `Multiplicative B` to additive subgroups of `B`, and
`nsmulAddMonoidHom n` is the additive `n`-fold map `y ↦ n • y` on `B`.

## Implemented proof

After a `show` step exposing the unfolded inclusion, the proof follows the
original unchanged. Given `x` with `hx : x ∈ Subgroup.toAddSubgroup' S`
(definitionally `Multiplicative.ofAdd x ∈ S`):

1. `xS : S` is the element `⟨Multiplicative.ofAdd x, hx⟩` of the Sylow
   subgroup.
2. `S.isPGroup'` (the `p`-group field of `Sylow`,
   `Mathlib/GroupTheory/Sylow.lean` line 56) says that `S` is a `p`-group,
   and Mathlib's `IsPGroup.powEquiv` (`Mathlib/GroupTheory/PGroup.lean`
   line 183) turns `hn.symm : Nat.Coprime p n` into the equivalence
   `e : S ≃ S` whose underlying function is `g ↦ g ^ n`.
3. `yS := e.symm xS` satisfies `yS ^ n = xS` by `Equiv.apply_symm_apply`,
   hence `yS.1 ^ n = xS.1` in `Multiplicative B` after applying
   `Subtype.val`.
4. The witness is `yS.1.toAdd : B`. The goal
   `nsmulAddMonoidHom n (yS.1.toAdd) = x` follows by
   `simpa [xS] using congrArg Multiplicative.toAdd hyval`: simp unfolds
   `xS`, rewrites `(a ^ n).toAdd` to `n • a.toAdd` (Mathlib's
   `Multiplicative.toAdd_pow`) and `(ofAdd x).toAdd` to `x`
   (`toAdd_ofAdd`), and evaluates `nsmulAddMonoidHom n` on the goal side.

So the preimage is found inside the Sylow subgroup itself, and the proof
never uses finiteness of `B` or of `S`. No auxiliary declaration, instance
or `simp` registration is introduced. A development check (`lean_check` in
the approved environment) compiled the module with no diagnostics; the
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Sylow.lean:137–158`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Sylow.lean#L137-L158):
the docstring at 137–143 (retained), the theorem with its telescope and
conclusion at 144–150, and the proof at 151–158. The partition's unit range
144–163 ends just before M078.006 at line 164; lines 160–163 are that next
theorem's docstring. The declaration sits in namespace
`ClassFormation.FiniteGaloisSubextension`; it uses none of the source's
section variables `{G : Type*} [Group G] [TopologicalSpace G]
[IsTopologicalGroup G]` and `{K : ClosedSubgroup G}`. The whole-file SHA-256
of the retained snapshot is
`e54964e68a4d16d2a0df909b7393c495b6544e08ea0701a98a06e650f1d38ac1`,
computed by Worker 60 on 13 November 2026; the
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m078)
lists this unit as row `M078.005`.

| Original in `ClassFormation.FiniteGaloisSubextension` | Adapted in `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` |
| --- | --- |
| Asserted type of `sylowAddSubgroup_le_nsmul_range_of_coprime` (M078.005) | Published `sylowAddSubgroup_le_nsmul_range_of_coprimeStatement` in CoprimeNsmul.Statements |
| Proof `sylowAddSubgroup_le_nsmul_range_of_coprime` | This theorem of the same adapted name in CoprimeNsmul.U005.Proofs |

Modifications by Worker 60, 13 November 2026: add the `Langlands.NYLL`
namespace prefix; replace the source imports by the sole published
statement import; state the theorem's type as the published proposition
applied to the source parameters; insert the initial `show` step; omit the
source `open`s, `noncomputable section`, section variables and all other
source declarations. The binders, docstring and all proof steps are
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

This is the group-theoretic lemma only. The specialization to the degree
`[M:K]` of the Sylow fixed field (M078.006) and every norm-map,
reciprocity, class-formation, cup, transfer or Tate result are separate.
