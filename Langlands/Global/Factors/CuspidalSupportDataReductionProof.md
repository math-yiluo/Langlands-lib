# Proof of the reduction of the cuspidal-support map

Authors: Worker 3657 (original shared proof draft) and Worker 573
(verification and submission).

Module `Langlands.Global.Factors.CuspidalSupportDataReductionProof` proves

```lean
theorem Langlands.Global.cuspidalSupportDataReduction :
    CuspidalSupportDataReductionStatement.{u}
```

The target is the published proposition
`Langlands.Global.CuspidalSupportDataReductionStatement` of module
`Langlands.Global.Factors.CuspidalSupportEveryPlaceStatement`. That module is
the sole import here. The target is the implication

```text
CuspidalSupportEveryPlaceStatement.{u} →
  CuspidalSupportUniquenessStatement.{u, u} → CuspidalSupportDataStatement.{u}
```

Both hypotheses are propositions taken as arguments. Neither is proved here,
and the theorem holds whether or not they are true. The proof uses no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.

## Statements involved

- `CuspidalSupportEveryPlaceStatement.{u}`: every irreducible automorphic
  operator subquotient `Q : IrreducibleOperatorSubquotient F r` over a number
  field `F : Type u` with `CompactSpace (AdeleQuotient F)` has cuspidal data
  `(k, m, hm, T, P, h)` of total rank `r + 1`. The presentations `P i` have
  factor universe `u`, and `IsInducedConstituent hm P h Q` holds.
- `CuspidalSupportUniquenessStatement.{u, u}` (module
  `Langlands.Global.Factors.CuspidalSupportStatement`): if `Q` is a finite
  induced constituent (`IsFiniteInducedConstituent`) of two families of
  cuspidal data, there is `e : Fin k ≃ Fin k'` matching the positive-rank
  cuspidal classes `⟨m i, (T i).isoClass⟩` and
  `⟨m' (e i), (T' (e i)).isoClass⟩`.
- `CuspidalSupportDataStatement.{u}`: every such `Q` has exactly one
  `D : IsobaricData F` with `Q.HasCuspidalSupport.{u, u} D`. Here
  `IsobaricData F` is `Multiset (PositiveRankCuspidalClass F)`.
  `HasCuspidalSupport D` says that `Q` is an induced constituent of cuspidal
  data whose classes satisfy
  `Finset.univ.val.map (fun i => ⟨m i, (T i).isoClass⟩) = D`.

## The proof

1. **Existence.** The first hypothesis, applied to `F`, `r` and `Q`, gives
   cuspidal data `(k, m, hm, T, P, h)` with `IsInducedConstituent hm P h Q`.
   These data witness `Q.HasCuspidalSupport D₀` for the multiset
   `D₀ := Finset.univ.val.map (fun i => ⟨m i, (T i).isoClass⟩)`, with the
   multiset equation by `rfl`.
2. **Uniqueness.** Let `D` be any cuspidal support of `Q`, with witness
   `(k', m', hm', T', P', h')`. The first conjuncts of the two
   `IsInducedConstituent` hypotheses are `IsFiniteInducedConstituent`
   statements. The second hypothesis, applied to the witness of `D` first and
   to `(k, m, hm, T, P, h)` second, gives `e : Fin k' ≃ Fin k` with
   `f' i = f (e i)` for all `i`. Here `f'` and `f` are the class maps of the
   two data. Then
   `D = univ.val.map f' = univ.val.map (f ∘ e) = (univ.val.map e).map f = univ.val.map f = D₀`.
   The steps are function extensionality, `Multiset.map_map`, and Mathlib's
   `Multiset.map_univ_val_equiv` (`Mathlib/Data/Fintype/Basic.lean`):
   `Finset.univ.val.map e = Finset.univ.val` for an equivalence `e`.

Only the finite-place conjuncts of `IsInducedConstituent` enter the
uniqueness step. The infinite-place conjuncts serve only to make the
existence witness a cuspidal support in the sense of `HasCuspidalSupport`.

## Provenance

This is the "Reduction" paragraph of §5 of the statement Markdown
(`Langlands/Global/Factors/CuspidalSupportEveryPlaceStatement.md`), with the
route of the contract of Task 7038 (`77a8a491-bc89-4cd8-ad39-99a4c66876f9`).
The mathematics is the sentence of Getz–Hahn after their Corollary 10.7.3,
which combines that corollary with Theorem 10.7.1 to obtain existence of
cuspidal inducing data and uniqueness up to permutation, in the sense of
Theorem 10.7.2. The source is J. R. Getz and H. Hahn (2024), *An
introduction to automorphic representations*, printed pp.286–287, PDF
pp.298–299 of the registered file
`getz-hahn-2024-automorphic-representations` (SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). The
source's existence and uniqueness are the two hypotheses here. The step from
"unique up to a permutation" to "a unique multiset" is the elementary
multiset computation above, and it is derived content.

The registered October 2026 errata
`getz-hahn-2024-errata-2026-10` (SHA256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
five PDF pages) contain no Chapter 10 correction.

The Lean proof is reused unchanged from Worker 3657's shared draft for
Task 7038, revision 1, content key
`23a8f79cf099551f1f5e19077e493fef8634897669cad63b1471cb21aaa3eac0`.
Worker 573 checked its agreement with the published target and the proof
description above.

## Scope

The theorem proves neither hypothesis. A proof of `CuspidalSupportDataStatement`
follows by applying `cuspidalSupportDataReduction` to proofs of
`CuspidalSupportEveryPlaceStatement.{u}` (Task 7041) and
`CuspidalSupportUniquenessStatement.{u, u}` (Task 6824). That application is
Task 7046 (`0572bce6-6824-4c50-bf51-f823c1f2f6cb`).

## Verification

Worker 573 checked the proof in the pinned environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. The entry module compiled with
zero errors and zero warnings; declaration inspection confirmed the theorem
has the single universe parameter `u` and uses only `propext`,
`Classical.choice` and `Quot.sound`. This development check does not supply
independent review or publication.
