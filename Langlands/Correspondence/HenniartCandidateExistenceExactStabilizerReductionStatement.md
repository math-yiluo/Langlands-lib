# Henniart's candidate existence from Proposition 4.8 under the exact Weil stabilizer condition

Module `Langlands.Correspondence.HenniartCandidateExistenceExactStabilizerReductionStatement`,
namespace `Langlands.Henniart`, universe parameters `uK uW uP uE uQ` as
published. It imports the published `HenniartCandidateExistenceReductionStatement`
and `HenniartCandidateExistenceTCReductionStatement`, and Task 7413's
published `HarrisProposition48ExactStabilizerStatement`, which defines
`Global.Harris.Proposition48ExactStabilizerStatement`; that proposition is not
restated here.

Two proposition definitions and two implications. Neither proposition is
proved here.

## The statements

### `CandidateExistenceExactStabilizerReductionStatement.{uK, uW, uP, uE, uQ}`

```
def CandidateExistenceExactStabilizerReductionStatement : Prop :=
  Global.Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
  ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
  ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0} →
  Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uW, uP} →
  Global.PoleComparison.HenniartCompositeMapStatement.{0, uK, uW, uP, uE} →
  CandidateExistenceStatement.{uK, uW, 0, uE, uQ}
```

Harris 1998, Proposition 4.8, in its exact-stabilizer form; Henniart 2000,
Théorème 2.4; the local relative class formation with its fundamental
classes; the certified local pole comparisons of Henniart's Lemme 2.8; and the
transport of Henniart's 3.8 to the composite map together imply that every
finite quotient `q` of the absolute Galois group of every `p`-adic field `K`
has a candidate, with automorphic lattice universe `0`.

**The single change.** The published declaration is
`CandidateExistenceReductionStatement`
(`Langlands/Correspondence/HenniartCandidateExistenceReductionStatement.lean`,
line 25). Its first hypothesis
`Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP}` becomes
`Global.Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP}`, at
the same universes. The other four hypotheses, their order and universes, and
the conclusion `CandidateExistenceStatement.{uK, uW, 0, uE, uQ}` are
unchanged.

### `CandidateExistenceExactStabilizerTCReductionStatement.{uK, uW, uP, uE, uQ}`

```
def CandidateExistenceExactStabilizerTCReductionStatement : Prop :=
  Global.Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
  ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP} →
  ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0} →
  Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uW, uP} →
  Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uK, uW, uP, uE} →
  CandidateExistenceStatement.{uK, uW, 0, uE, uQ}
```

The same, with the second, fourth and fifth hypotheses in their totally
complex forms, as published.

**The single change.** The published declaration is
`CandidateExistenceTCReductionStatement`
(`Langlands/Correspondence/HenniartCandidateExistenceTCReductionStatement.lean`,
line 25). Its first hypothesis
`Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP}` becomes
`Global.Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP}`, at
the same universes. Its totally complex hypotheses 2, 4 and 5, its hypothesis
3 and its conclusion are unchanged. Harris's proposition, whose fields are CM,
has no totally complex form, as in the published statement.

A private audit (not submitted) compared the elaborated values. In each
published value the constant `Global.Harris.Proposition48Statement` occurs
once; replacing it by `Global.Harris.Proposition48ExactStabilizerStatement`
(same universe arity) gives the new value exactly, with the same type,
universe parameters and reducibility.

## Relation to the published statements

Every exact-stabilizer datum is a datum (the published theorem
`Global.Harris.IsProposition48ExactStabilizerDatum.isProposition48Datum`,
through `Langlands.Global.generalPositionOfExactStabilizer`). So the
published `Proposition48Statement` implies
`Proposition48ExactStabilizerStatement`: this is the published theorem
`Global.Harris.proposition48ExactStabilizerStatement_of_proposition48Statement`
(`HarrisProposition48ExactStabilizerStatement.lean`, line 54). The statements
here have this weaker first hypothesis, so each one implies its published
counterpart. The module proves both implications:

```
theorem candidateExistenceReductionStatement_of_exactStabilizer
    (h : CandidateExistenceExactStabilizerReductionStatement.{uK, uW, uP, uE, uQ}) :
    CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}

theorem candidateExistenceTCReductionStatement_of_exactStabilizer
    (h : CandidateExistenceExactStabilizerTCReductionStatement.{uK, uW, uP, uE, uQ}) :
    CandidateExistenceTCReductionStatement.{uK, uW, uP, uE, uQ}
```

Each one composes `h` with
`proposition48ExactStabilizerStatement_of_proposition48Statement` on the first
hypothesis. Both use only the standard axioms. Neither converse is claimed.

## Why the statements are true (the expected proof)

This is a reading of the Library at commit `97bd11ee`; the proofs are not given
here.

- The published proof `candidateExistenceReduction`
  (`Langlands/Correspondence/HenniartCandidateExistenceReductionProof.lean`,
  line 28) uses Harris's proposition only by passing it to
  `henniartGlobalization_of_inputs` (line 38), with the four proved local
  inputs.
- `henniartGlobalization_of_inputs` (`HenniartGlobalizationReduction.lean`,
  line 122) applies Harris's proposition once, in
  `exists_weilImage_realizeExact_continuousInduce`
  (`HenniartGeneratorRealization.lean`, lines 141–143), to the datum given by
  the character realization. With the exact-stabilizer realization
  (`HarrisDatumCharacterRealizationExactStabilizerStatement`) and the
  exact-stabilizer reduction
  (`HenniartGlobalizationExactStabilizerReductionStatement`, both stated in
  the sibling modules of this task), the restated proposition gives the same
  conclusion, so the same proof gives
  `CandidateExistenceExactStabilizerReductionStatement`.
- The proof of the published TC form is open (Task 7363,
  `a10de1f7-62b5-4acd-852f-4b0fcc13833e`). Its expected proof goes through TC
  copies of the same lemmas, and the same change applies to it.

Mathematically, Henniart needs Harris's proposition only for the characters
of his §3.4, whose component at `0'` satisfies condition 3). That condition
implies Harris's (4.12), so the exact-stabilizer form of Proposition 4.8 is
enough.

## What is not claimed

Neither `CandidateExistenceExactStabilizerReductionStatement` nor
`CandidateExistenceExactStabilizerTCReductionStatement` is proved here. Their
proofs belong to separate `lean.proof@1` tasks of the parent (Task 7343). Only
the two implications to the published statements are proved. The published
`CandidateExistenceReductionStatement` (proved as `candidateExistenceReduction`),
`CandidateExistenceTCReductionStatement` (Task 7363) and their tasks are
unchanged.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455, source
  `henniart-2000-simple-proof` (PDF page = printed page − 438).
  - §3.4, condition 3), printed p.449 (PDF p.11): "Le caractère `X_{0'}` est
    `L_{0'}/F_{0'}` régulier, au sens où le stabilisateur dans
    `Gal(L̃_{0'}/F_{0'})` de la restriction à `U_{L̃_{0'}}` de
    `X_{0'} ∘ N_{L̃_{0'}/L_{0'}}` est `Gal(L̃_{0'}/L_{0'})`". The stabilizer
    of the full character `X_{0'} ∘ N` contains `Gal(L̃_{0'}/L_{0'})` and is
    contained in the stabilizer of its restriction to units, so this condition
    implies the exact-stabilizer condition (4.12).
  - §3.6, Lemme 3, printed p.451 (PDF p.13): the characters of 3.4 exist with
    prescribed restriction to `U_0`. Its proof chooses the component at `0'`
    satisfying condition 3) of 3.4, "c'est possible d'après la preuve du
    Lemme 4.7 de [Ha 2]".
  - Théorème 3.1 with 3.7–3.8, printed pp.448–451: the candidate built from
    the global construction.
- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, source
  `harris-1998-local-langlands` (PDF page = printed page − 176).
  Proposition 4.8, printed p.201 (PDF p.25). Condition (4.12), in the proof of
  Lemma 4.7, printed pp.204–206 (statement of (4.12) on p.204, PDF p.28): with
  `G = Γ_F`, `H = Γ_{F'}` and `χ̃(*) = χ(*) ∘ N_{F̃/F'}`,
  `H = {g ∈ G | g χ̃(*) = χ̃(*)}`.
- Design: operator plan note `operator-external-inputs-plan-2026-11-16`,
  Section 4.8, Remark 4.2 (TeX lines 859–894) and the paragraph "The remark
  and the Library's statements" (TeX lines 897–912). The plan note is
  unreviewed design guidance, not a source of the statement.
