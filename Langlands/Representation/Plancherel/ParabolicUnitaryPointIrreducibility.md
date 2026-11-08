# Irreducibility of actual unramified induction at regular unitary points

Author: Worker 1597.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), registered as `waldspurger-2003-plancherel`,
PDF SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Proposition IV.2.2(i), printed p.284 / PDF p.50: if `π` is irreducible,
square-integrable and `G`-regular, then `I_P^G π` is irreducible. The proof,
printed p.285 / PDF p.51, reads: `I_P^G π` is unitary, hence semisimple; it
suffices that `dim Hom_G(I_P^G V, I_P^G V) = 1`, which follows from
Corollary III.7.3 and Frobenius reciprocity. IV.3 on the same page then uses
this to produce an irreducible point of the unramified family when `π` is
square-integrable.

## The statements

`UnitaryRegularParabolicIrreducibilityStatement` is a derived Prop. Its
structural context is copied unchanged from
`ConditionalParabolicGenericIrreducibilityStatement`: any nonarchimedean local
field, the canonical point topology, local compactness, the nonarchimedean-group
property and Hausdorffness of `G(F)`, a `ParabolicRootPresentation r`, a
geometric radical, the literal semidirect decomposition `h`, closedness of the
radical and parabolic, and continuity of the Levi projection. For an irreducible
`π` of the literal Levi `Mpt`, square-integrable modulo `C`, it asserts the
following, where `C` is the image of the split-component points and the Haar
measure on `Mpt / C` is the supplied one. For every unramified character `χ` of
the full rational-norm family with `‖χ m‖ = 1` for all `m` such that the twist
`π.twist χ` is `IsNormalizerRegular`, the actual
`UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π` is
irreducible.

This is IV.2.2(i) applied to the unitary twists `π ⊗ χ`, which are again
irreducible and square-integrable. Waldspurger's `G`-regularity is replaced by
`IsNormalizerRegular` for the literal normalizer of `Mpt` in `G(F)`, as in
`RegularSquareIntegrableJacquetMultiplicityStatement`. The statement does not
compare the two regularity notions. It also does not assert that regular
unitary twists exist, or that irreducibility holds on an open set of
characters.

`UnitaryRegularParabolicIrreducibilityReductionStatement` is the Prop-valued
implication to it from four Library statements:
`RegularSquareIntegrableJacquetMultiplicityStatement`,
`RationalReductiveUnimodularityStatement` (unimodularity of the actual
connected reductive point groups),
`StandardCocharacterStatement`, a premise of the unimodularity statement,
and `ArbitraryParabolicQuotientCompactStatement`. The theorem
`unitaryRegularParabolicIrreducibility_of_statements` proves the implication.
None of the four inputs is proved here.

## Proof

- `parabolic_modularCharacter_eq`: under the unimodularity statements, the
  modular character of the literal parabolic `Ppt` is the closed Haar modulus
  of conjugation on the radical `Upt`. The Levi `Mpt` is unimodular by
  `RationalReductiveUnimodularityStatement` for `M`, transported along
  `parabolicLeviPointHomeomorph` with `modularCharacter_continuousMulEquiv`.
  The radical is unimodular by the published `parabolicRadical_isUnimodular`.
  The published `modularCharacter_eq_restrictCharacter_of_unimodular` then
  gives the formula.
- `unramifiedLeviInduction_isIrreducible_of_unitary_regular` follows the
  source proof. Write `π' = π.twist χ`. It is irreducible
  (`isIrreducible_twist_iff`). It is square-integrable modulo `C` by the
  published `isSquareIntegrableModCentralSubgroup_unitaryTwist`, because `χ`
  has norm one. The multiplicity statement bounds the rank of the Jacquet Hom
  space `Hom(r_P(I_P π'), π')` by one. This bound is moved to the normalized
  induction along `normalizedInductionLeviTwistIso`. `π'` is unitarizable by
  `isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar`, so its
  compact-quotient normalized induction is unitarizable
  (`normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace`, with
  ambient unimodularity and `parabolic_modularCharacter_eq`). That induction
  is admissible by `normalizedInductionFunctor_obj_isAdmissible`. The
  published `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one`
  combines unitary admissible semisimplicity with first adjointness, which
  plays the role of Frobenius reciprocity in the source. This proves that
  the normalized induction is irreducible. Irreducibility is then carried
  back to the Levi-normalized induction along the same isomorphism.

The module imports the pending supporting module `ParabolicRepresentedComparison`
only for the intertwiner-space equivalence `intertwiningPrecompLinearEquiv`.
