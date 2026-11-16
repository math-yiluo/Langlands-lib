# The Frobenius tower map multiplies normalized degree by f

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_degree`, the proof phase of
M066.006 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m066).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement` applied to the
theorem's parameters:

```lean
theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') :
    finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement
      D E L L' hLK hL'K' hL'L q
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]`. The theorem then takes `D`, the instance `[IsTopologicalGroup G]`, `E`, `L L'`, `hLK`, `hL'K'`, `hL'L`, the two normality instance binders `hLnormal` and `hL'normal` and `q`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.FrobeniusTower.Statements`, the target is the proposition

```lean
(D.extensionNormalizedDegree E.base L hLK
    (D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L'
      hLK hL'K' E.below hL'L q)).toAdd =
  (E.residueDegree : ℕ) •
    (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd
```

Write `K = E.base` and `K' = E.field` for the finite-residue abstract extension `E` (M010.111), whose residue degree `f = E.residueDegree` (M010.116) is a positive natural number, and let `L | K` and `L' | K'` be Galois with `G_{L'} ≤ G_L`. `finiteReciprocityNaturalityFrobeniusTowerMap` (M066.003) is the map `G_{K'} ⧸ (G_{L'} ⊓ I_{K'}) →* G_K ⧸ (G_L ⊓ I_K)` induced by `G_{K'} ≤ G_K`, and `extensionNormalizedDegree` (M012.005) is the normalized degree to `Multiplicative ZHat`. The target says that for every `q` the normalized degree over `K` of the image of `q` is `f` times the normalized degree of `q` over `K'`, both read additively in `ZHat` (M008.008). No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.FrobeniusTower.Statements`, which defines the target and, through its imports, the normalized degree `DegreeData.normalizedDegree` (M011.006) and the positive residue degree `FiniteAbstractExtension.residueDegree` (M010.086);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs`, the published proof of M010.036 `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`: the cardinal relative residue degree times the residue-degree cardinal of the base is the residue-degree cardinal of the field;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs`, the published proof of M010.027 `FiniteResidueAbstractField.residueDegreeCardinal_eq_coe`: for a finite-residue field the residue-degree cardinal is the cast of its positive residue degree;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U008.Proofs`, the published proof of M011.008 `DegreeData.residueDegree_nsmul_normalizedDegree`: `f_K • d_K(k) = deg(k)` for `k ∈ G_K`;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs`, the published proof of M009.005 `zHatMulNat_injective`: multiplication by a positive natural number is injective on `ZHat`.

The module opens `CyclicCohomology`, for `extensionSubgroup`, as the source does.

## Implemented proof

The main proof is the source proof: `Quotient.inductionOn'` reduces to the coset of some `k' ∈ G_{K'}`, and the source `change` (which also unfolds the published proposition) identifies the goal with `(D.normalizedDegree E.base (Subgroup.inclusion E.below k')).toAdd = (E.residueDegree : ℕ) • (D.normalizedDegree E.field k').toAdd`. The source closes this with M011.019 `frobeniusRestrictionNaturality_normalizedDegree`, whose proof is not in the Library, nor are the proofs of the two results it uses, M011.017 and M010.103. The module reproduces their source proofs as three private theorems, each with the source binders and statement. `relativeResidueDegreeCardinal_eq_coe_aux` (M010.103): for a finite abstract extension, the cardinal relative residue degree is the cast of the positive residue degree; `change` exhibits both sides as the cardinal and the cast `Nat.card` of the same quotient, and Mathlib's `Nat.cast_card` closes the goal. `residueDegree_mul_absoluteResidueDegree_aux` (M011.017): `f_{K'|K} · f_K = f_{K'}` in `ℕ`; it takes the published M010.036, stated by `change` with its unfolded type, rewrites with the private M010.103, and with the published M010.027 for `K` and `K'` through the local equations `hbase` and `hfield`, and concludes by `exact_mod_cast`. `frobeniusRestrictionNaturality_normalizedDegree_aux` (M011.019): by the published M009.005 it suffices to compare both sides after multiplication by `f_K > 0`; the left side becomes `deg(l)` by the published M011.008 for `K` (local equation `hbase`), and `smul_smul`, `Nat.mul_comm`, the private M011.017 and M011.008 for `K'` (local equation `hfield`) turn the right side into `deg(l)` as well.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`, lines 142–165](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean#L142-L165):
the docstring at lines 142–143 and the theorem at lines 144–165. It lies in `namespace ClassFormation` (line 21), after `universe u` (line 19), with `open KummerTheory` (line 23), `open CyclicCohomology` (line 25), `open CategoryTheory` (line 27), its `noncomputable section` (line 32), `open scoped BigOperators` (line 34), `section GroupOnly` (line 36), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 38) and `namespace DegreeData` (line 78). The reproduced M011.017 and M011.019 are at [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`, lines 231–246](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean#L231-L246) and [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`, lines 258–276](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean#L258-L276) (SHA-256 `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`; `namespace ClassFormation`, `noncomputable section`, variables `{G : Type*} [Group G] [TopologicalSpace G]`, `namespace DegreeData`), and M010.103 is at [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, lines 878–891](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L878-L891) (SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`; `namespace DegreeData`, `namespace FiniteAbstractExtension` with the section variable `(E : FiniteAbstractExtension G)` at line 567). The source is:

```lean
/-- Frobenius residue-degree compatibility's normalized-degree square on the two infinite
Frobenius quotients. -/
theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') :
    (D.extensionNormalizedDegree E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L q)).toAdd =
      (E.residueDegree : ℕ) •
        (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd := by
  refine Quotient.inductionOn' q ?_
  intro k'
  change (D.normalizedDegree E.base (Subgroup.inclusion E.below k')).toAdd =
    (E.residueDegree : ℕ) • (D.normalizedDegree E.field k').toAdd
  exact D.frobeniusRestrictionNaturality_normalizedDegree E k'
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`;
its SHA-256 is `0107befcff3ba066d7663120d9aa823ae72911cef7d3e72c5eeb5cb95f73a533`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement D E L L' hLK hL'K' hL'L q` as its type; the source's `change` unfolds it;
- replace the source's final use of M011.019 (not proved in the Library) by the private theorem `frobeniusRestrictionNaturality_normalizedDegree_aux`, with a comment;
- reproduce the source theorems M011.019, M011.017 and M010.103 (not proved in the Library) as the private theorems `frobeniusRestrictionNaturality_normalizedDegree_aux`, `residueDegree_mul_absoluteResidueDegree_aux` and `relativeResidueDegreeCardinal_eq_coe_aux` in `namespace DegreeData`, with adapted docstrings, the source binders and statements (M010.103 with its section variable `E` as the first explicit binder and without its `@[simp]` attribute) and the source proofs, except that each use of a published theorem whose type is a Statement proposition goes through a local equation with the unfolded type: in M011.017 the hypothesis `h` from M010.036 is first restated by `change`, and the rewrites with M010.027 use `hbase` and `hfield`; in M011.019 the rewrites with M011.008 use `hbase` and `hfield`;
- omit `open KummerTheory`, `open CategoryTheory`, `open scoped BigOperators`, the `noncomputable section`, the section header and all other source declarations; keep `universe u`, `open CyclicCohomology`, the variable line and `namespace DegreeData`.

The theorem name, docstring, binders and the main proof steps are kept. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

The module was written by Worker 5264 and shared as revision 1 of the draft of
Task 7075 (`0454080b-e432-4027-b99d-a958401cb38d`). Worker 745 checked it
against the pinned original and the published statement module, recompiled it
over Library commit `72480b70c88adff84a438bd7029d64ee3977469c` on 16 November
2026 (no errors or warnings; axioms `propext`, `Classical.choice`,
`Quot.sound`) and staged it without changing the Lean file.

This module proves only M066.006. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
