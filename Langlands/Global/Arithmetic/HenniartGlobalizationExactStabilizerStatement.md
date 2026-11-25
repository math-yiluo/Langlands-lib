# Henniart's relative globalization from Proposition 4.8 under the exact Weil stabilizer condition

Module `Langlands.Global.Arithmetic.HenniartGlobalizationExactStabilizerStatement`,
namespace `Langlands.Global`. It imports the published
`HenniartGlobalizationStatement`, `HenniartGlobalizationReduction` (only for
the published `HenniartGlobalizationReductionStatement`, which the second
implication below needs) and the published
`HarrisProposition48ExactStabilizerStatement`, which defines
`Harris.Proposition48ExactStabilizerStatement`; that proposition is not
restated here.

Two proposition definitions and two implications. Neither proposition is
proved here.

## The statements

### `HenniartGlobalizationExactStabilizerStatement.{uK, uQ, uW, uP}`

```
def HenniartGlobalizationExactStabilizerStatement : Prop :=
  Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
    RelativeGaloisGlobalization.{uK, uQ, uW, uP}
```

Harris 1998, Proposition 4.8, in its exact-stabilizer form implies the
relative form of Henniart 2000, Théorème 3.1. The conclusion is the published
`RelativeGaloisGlobalization` (`HenniartGlobalizationStatement.lean`, line
66), used unchanged. Informally, for every arithmetic fundamental-class family
`c`, every `p`-adic field `K` and every homomorphism `q` from the absolute
Galois group of `K` to a finite group, there are a finite Galois extension
`E/F` of number fields, a finite place `v` of `F` above `p` and an
isomorphism `K ≅ F_v` such that every unitary virtual class of `W_K` whose
irreducible constituents factor through `q` is, after transport along this
isomorphism, the restriction of an element of the Weil image
`weilImage F E c v`.

**The single change.** The published declaration is
`HenniartGlobalizationStatement` (`HenniartGlobalizationStatement.lean`, line
85):

```
Harris.Proposition48Statement.{uK, 0, 0, 0, uP} →
  RelativeGaloisGlobalization.{uK, uQ, uW, uP}
```

The hypothesis `Harris.Proposition48Statement.{uK, 0, 0, 0, uP}` becomes
`Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP}`, at the same
universes. The universe parameters `uK uQ uW uP` and the conclusion are
unchanged.

### `HenniartGlobalizationExactStabilizerReductionStatement.{uK, uQ, uW, uP}`

```
def HenniartGlobalizationExactStabilizerReductionStatement : Prop :=
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
    LocalInducedRestrictionStatement.{uW, 0} →
      AssociatedCentralCharacterStatement.{0, uW, uP} →
        AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
          LocalTransferReciprocityStatement.{0} →
            HenniartGlobalizationExactStabilizerStatement.{uK, uQ, uW, uP}
```

The existence of normalized local reciprocity families, Tate's local
restriction formula for induced reciprocity representations, the central
character comparison, the associated supercuspidal induction and local
transfer reciprocity imply the statement above.

**The single change.** The published declaration is
`HenniartGlobalizationReductionStatement`
(`HenniartGlobalizationReduction.lean`, line 208). It has the same five
hypotheses, in the same order and at the same universes. Its conclusion
`HenniartGlobalizationStatement.{uK, uQ, uW, uP}` becomes
`HenniartGlobalizationExactStabilizerStatement.{uK, uQ, uW, uP}`.

An audit outside the Library compared the elaborated values. For the first
statement, the constant `Harris.Proposition48Statement` occurs once in the
published value; replacing it by `Harris.Proposition48ExactStabilizerStatement`
(same universe arity) gives the new value exactly. For the second, the same
holds with `HenniartGlobalizationStatement` replaced by
`HenniartGlobalizationExactStabilizerStatement`. In both cases the type,
universe parameters and reducibility are the same.

## Relation to the published statements

Every exact-stabilizer datum is a datum (the published theorem
`Harris.IsProposition48ExactStabilizerDatum.isProposition48Datum`, through
`Langlands.Global.generalPositionOfExactStabilizer`). So the published
`Proposition48Statement` implies `Proposition48ExactStabilizerStatement`: this
is the published theorem
`Harris.proposition48ExactStabilizerStatement_of_proposition48Statement`
(`HarrisProposition48ExactStabilizerStatement.lean`, line 54). The statements
here have this weaker hypothesis, so each one implies its published
counterpart. The module proves both implications:

```
theorem henniartGlobalizationStatement_of_exactStabilizer
    (h : HenniartGlobalizationExactStabilizerStatement.{uK, uQ, uW, uP}) :
    HenniartGlobalizationStatement.{uK, uQ, uW, uP}

theorem henniartGlobalizationReductionStatement_of_exactStabilizer
    (h : HenniartGlobalizationExactStabilizerReductionStatement.{uK, uQ, uW, uP}) :
    HenniartGlobalizationReductionStatement.{uK, uQ, uW, uP}
```

The first composes `h` with
`proposition48ExactStabilizerStatement_of_proposition48Statement`. The second
applies `h` to the five local hypotheses and then uses the first. Both use only
the standard axioms. Neither converse is claimed.

## Why the statements are true

This is a reading of the Library at commit `97bd11ee`; the proofs are not given
here.

- The published reduction is proved: `henniartGlobalization_reduction`
  (`HenniartGlobalizationReduction.lean`, line 217) is
  `henniartGlobalization_of_inputs` (line 122). Harris's proposition is only
  passed down there, and applied once: in
  `exists_weilImage_realizeExact_continuousInduce`
  (`HenniartGeneratorRealization.lean`, hypothesis at line 70). There it is
  applied (line 142) to the datum returned by `harrisDatumCharacterRealization`
  (line 141), and the datum's conjuncts are then read by position (line 143):
  the three it uses are regularity, conjugate inverse and the component at
  `P`, not the general-position conjunct.
- The exact-stabilizer realization
  `HarrisDatumCharacterRealizationExactStabilizerStatement` (module
  `HenniartHarrisDatumExactStabilizerStatement`) gives an exact-stabilizer
  datum for the same characters. The restated proposition applies to it and
  gives the same conclusion. The exact-stabilizer datum has the same conjuncts
  in the same positions, so the rest of the proof is unchanged.
- So, with the exact-stabilizer realization (proved as
  `harrisDatumCharacterRealizationExactStabilizer`, module
  `HenniartHarrisDatumExactStabilizerProof`), the same proof with
  `Proposition48ExactStabilizerStatement` gives the exact-stabilizer
  reduction; it is proved as `henniartGlobalizationExactStabilizerReduction`
  (module `HenniartGlobalizationExactStabilizerProof`). The four local inputs `CommonClosureReciprocityExistence`,
  `LocalInducedRestrictionStatement`, `AssociatedCentralCharacterStatement`
  and `LocalTransferReciprocityStatement` are proved in the Library, so the
  reduction and a proof of `AssociatedSupercuspidalInductionStatement` would
  give `HenniartGlobalizationExactStabilizerStatement`.

Mathematically, Henniart needs Harris's proposition only for the characters
of his §3.4. Their component at `0'` satisfies condition 3), a condition on
the restriction to units. It implies Harris's (4.12), so the exact-stabilizer
form of Proposition 4.8 is enough.

## What is not claimed

Neither `HenniartGlobalizationExactStabilizerStatement` nor
`HenniartGlobalizationExactStabilizerReductionStatement` is proved here; the
second is proved as `henniartGlobalizationExactStabilizerReduction` (module
`HenniartGlobalizationExactStabilizerProof`). Only the two implications to the
published statements are proved here. The
published `HenniartGlobalizationStatement`,
`HenniartGlobalizationReductionStatement` and their proofs are unchanged.
No totally complex form of the globalization is stated; the published
globalization has none.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455, source
  `henniart-2000-simple-proof` (PDF page = printed page − 438).
  - Théorème 3.1 and §§3.3–3.7, printed pp.448–451: the global construction.
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
- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, source
  `harris-1998-local-langlands` (PDF page = printed page − 176).
  Proposition 4.8, printed p.201 (PDF p.25). Condition (4.12), in the proof of
  Lemma 4.7, printed pp.204–206 (statement of (4.12) on p.204, PDF p.28): with
  `G = Γ_F`, `H = Γ_{F'}` and `χ̃(*) = χ(*) ∘ N_{F̃/F'}`,
  `H = {g ∈ G | g χ̃(*) = χ̃(*)}`.
- Design: plan note `operator-external-inputs-plan-2026-11-16`,
  Section 4.8, Remark 4.2 (TeX lines 859–894) and the paragraph "The remark
  and the Library's statements" (TeX lines 897–912). The plan note is
  design guidance, not a source of the statement.
