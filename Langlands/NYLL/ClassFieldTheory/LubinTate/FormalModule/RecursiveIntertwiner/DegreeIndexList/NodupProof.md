# NYLL M353.004: the fixed-degree enumeration has no repetitions

Worker 464, 15 November 2026. This file proves the published proposition
`Langlands.NYLL.PortInternal.M353.d004Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Statements`)
with the required theorem `Langlands.NYLL.PortInternal.M353.d004`.

## Exact statement

The theorem has the target's parameters, in the same order and binder kinds:
implicit `{sigma : Type w}` in the arbitrary universe `w`, the instance
argument `[Fintype sigma]`, and the explicit degree `(m : ℕ)`. Its conclusion
is `d004Statement (sigma := sigma) m`, which unfolds to
`(d003 (sigma := sigma) m).Nodup`. Here `d003 m` is the published list of all
exponent vectors `d : sigma →₀ ℕ` with total degree `d.degree = m`: it equips
that subtype locally with the `Fintype` structure
`(Finsupp.finite_of_degree_eq m).fintype` and takes `Finset.univ.toList`.
No further hypothesis is added. The target's Lean/Markdown pair and the
imported `d003` Definitions pair are unchanged.

In words: for a finite variable type and any total degree `m`, the list
enumerating the monomials of total degree `m` lists each monomial at most once.

## Implemented proof

1. `unfold d004Statement d003` replaces the target by its definition. The goal
   becomes the `Nodup` property of `Finset.univ.toList`, computed with the
   local `Fintype` structure installed in `d003`.
2. `exact Finset.nodup_toList _` closes it. Mathlib's `Finset.nodup_toList`
   states that `s.toList` has no duplicates for every finite set `s`; here `s`
   is the universal finite set of the degree-`m` subtype. The underlying reason
   is that a `Finset` is a multiset without duplicates and `toList` chooses a
   list representing that multiset.

The proof uses only this one lemma from `Mathlib.Data.Finset.Dedup`, which the
imported Definitions module already imports. Development compilation reported
no errors or warnings. The inspected theorem depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; `Classical.choice` enters
through the noncomputable `d003` (its `Set.Finite.fintype` structure and
`Finset.toList`). The file introduces no new axiom, instance, simp lemma or
other declaration.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
lines 57–60: the source-private theorem
`LubinTate.SameUniformizer.degreeIndexList_nodup` (statement lines 57–58,
proof lines 59–60), with ambient section variables at lines 36–38 and the
list `degreeIndexList` at lines 51–55. The original file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
Its readable retained path is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

Copyright 2026 Naganori Yamaguchi; original authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original copyright, Apache-2.0 and author
header is retained verbatim in the Lean file, followed by a modification
notice. The unchanged license and notices remain in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`, SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No patch10 edit affects this source module.

## Adaptations

- The source-private theorem name `degreeIndexList_nodup` is replaced by the
  required public port-internal name `Langlands.NYLL.PortInternal.M353.d004`,
  and its conclusion is stated through the published Prop target
  `d004Statement`, which is definitionally the source conclusion with
  `degreeIndexList` renamed `d003`.
- The source proof is `classical` followed by
  `simp [degreeIndexList, Finset.nodup_toList]`. The implemented proof instead
  unfolds `d004Statement` and `d003` and applies `Finset.nodup_toList`
  directly. This is the same mathematical argument without simp search; the
  `classical` tactic is unnecessary because no decidability instance is used.
- The original NYLL imports are replaced by the single import of the published
  Statements module, which brings in `d003` and its Mathlib dependencies.
- Only the effective parameters are kept. The source section variables `K`,
  `Field K`, `F` and `pi` and the unused universes `u` and `v` do not occur in
  the source theorem's elaborated type and are not parameters here.
- The source's `noncomputable section` wrapper is retained. The original module
  overview and all unrelated declarations are omitted; a focused overview,
  theorem docstring and modification notice are added.
