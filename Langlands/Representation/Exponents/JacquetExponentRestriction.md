# Restriction of normalized Jacquet exponents

Workers 1670 and 1666. The source is David Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026, VII.1.1, printed pages 220–221 / PDF pages
226–227, lemma (ii) and its proof. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The generic supporting lemmas below are internal derivations for the published
actual coinvariant and characteristic-space constructions.

`JacquetExponentRestrictionStatement` is clause (ii) of the exponent lemma:
for every admissible smooth representation `π` and normalized Jacquet exponent
`χ`, the pullback `χ.comp e` is a whole-group exponent of `π`.
`normalizedJacquetExponent_restrict` proves it whenever the supplied point
homomorphism `e : A_G(F) →* A(F)` agrees with the two inclusions into the
ambient rational-point group. The split components, represented parabolic,
Levi, radical and multiplication isomorphism are all specified data.

The implemented proof has the following steps.

1. `closedInverseHalfCharacter_eq_one_of_mem_center` uses the published
   triviality of the actual closed Haar modulus at an ambient central point.
   It follows that the inverse half character is one. Consequently
   `normalizedJacquetFunctor_obj_apply_of_mem_center` identifies the
   normalized quotient action there with the original action followed by the
   actual coinvariant projection.
2. `normalizedJacquetCentralQuotient` makes that projection a linear
   intertwiner between the restrictions of the original and normalized
   Jacquet representations along any compatible central maps. It is
   surjective because `Jacquet.Localization.mk` is a quotient map, as recorded
   by `normalizedJacquetCentralQuotient_surjective`.
3. `normalizedJacquetExponent_restrict_isGeneralizedEigencharacter` restricts
   the generalized-character equations along `e`. The same nonzero vector
   and the same natural-number power work for every point in the smaller
   domain. No continuity assumption on `e` is used.
4. In the actual represented-parabolic comparison, the restricted Levi action
   is `κ = (splitComponentPointsMap (l ≫ p) a).comp e`. Compatibility identifies
   its ambient values with `rationalPoints.map aG`. The source representation
   is admissible, so the published full-center finite-span result, followed
   by `generalizedWeightSpace_iSup_eq_top`, gives spanning by its `A_G`
   characteristic spaces. The actual Jacquet object is smooth, and its
   literal Levi image is closed and locally compact. These facts convert
   the restricted generalized character to a nonzero target weight space.
5. `generalizedWeightSpace_ne_bot_of_surjective` reflects this nonzero target
   weight through the canonical quotient intertwiner. Only the original
   representation needs to have spanning weight spaces. Finally the
   canonical split-component point topology makes `rationalPoints.map aG`
   continuous. The published `isGeneralizedWeight_iff` supplies the open
   kernel of `χ.comp e`, giving the actual `IsGroupExponent` conclusion.

The field universe and representation-carrier universe are independent.
The theorem assumes a Hausdorff topological field, affine ambient group,
locally compact nonarchimedean ambient rational-point group and the displayed
parabolic and split-component hypotheses. These hold among the hypotheses
of `ArbitraryParabolicExponentStatement`; neither local-field structure nor
connected reductivity is additionally needed in this argument. The theorem
requires no admissibility or finite generation of the Jacquet representation,
no Iwahori contraction, irreducibility, continuity of `e`, or existence of `e`.

Worker 1670 implemented the central quotient and actual Jacquet comparison.
Worker 1666 authored the bundled `SplitComponentDecomposition` and
`SplitComponentComparison` pairs, including the source-spanning and surjective
weight-reflection lemmas used here. Those pairs are unchanged copies of the
separately submitted supporting units.

This is a supporting statement and its derivation within the parent proof
task. It proves the Jacquet exponent-comparison clause only. The full
`ArbitraryParabolicExponentStatement` still requires its unconditional
Jacquet decomposition and finite-exponent assertions. The separate Casselman
criterion and later VII.2 assertions are outside this unit.
