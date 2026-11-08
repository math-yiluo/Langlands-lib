# A reduction of actual generic irreducibility of unramified parabolic induction

Author: Worker 1597.

This module reduces the published Prop target
`ConditionalParabolicGenericIrreducibilityStatement` to Prop statements in the
Library. It does not prove that target: every statement it assumes is unproved
in the Library.

## Source

The target is the open-locus consequence at the start of Waldspurger 2003,
IV.3 (printed p.285 / PDF p.51, `waldspurger-2003-plancherel`). Let `π` be
irreducible and square-integrable. By Proposition IV.2.2 there is an
irreducible point of its unramified orbit, and the set of such points is a
nonempty Zariski open subset. The openness step is Renard 2026, VI.8.4
(`renard-2026-representations-groupes-reductifs-padiques`), formalized in the
Library as `Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement`. That
statement concerns represented induction and principal Zariski open sets of
the unramified characters of `M(F)`.

## Statements

- `ParabolicGenericIrreducibilityReductionStatement` is the Prop-valued
  implication from `UnitaryRegularParabolicIrreducibilityStatement`
  (irreducibility at regular unitary points, the Waldspurger IV.2.2(i) form of
  `ParabolicUnitaryPointIrreducibility`) and `InducedIrreducibilityOpenStatement`
  to `ConditionalParabolicGenericIrreducibilityStatement`, at universes `u` and
  `uV`. `conditionalParabolicGenericIrreducibility_of_statements` proves it.
- `ParabolicGenericIrreducibilityStructuralReductionStatement` is the
  Prop-valued implication to the same target from eight Library statements:
  `RepresentedGeometricLemmaStatement`,
  `TemperedSquareIntegrableUnitaryPartStatement`,
  `ArbitraryParabolicQuotientCompactStatement`,
  `SquareIntegrableNormalizedTemperedStatement`,
  `ArbitraryParabolicJacquetAdmissibilityStatement`,
  `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement`
  and `InducedIrreducibilityOpenStatement`.
  `conditionalParabolicGenericIrreducibility_of_structuralStatements` proves
  it. The proof composes `regularSquareIntegrableJacquetMultiplicity_of_statements`,
  `unitaryRegularParabolicIrreducibility_of_statements` and the preceding
  theorem.

## Proof of the core step

`exists_open_irreducible_of_statements` works in the target's own structural
context. Let `π` be an irreducible representation of the literal Levi that is
square-integrable modulo the split-component image `C`.

1. Square-integrability supplies a unitary central character, so
   `π.HasCentralCharacter` holds. Irreducibility makes `π` nontrivial.
2. `exists_unitary_twist_isNormalizerRegular` gives a norm-one unramified `χ₀`
   with `π.twist χ₀` regular for the literal normalizer.
3. `UnitaryRegularParabolicIrreducibilityStatement` makes
   `UnramifiedLeviInduction h hU ν χ₀ π` irreducible, where `ν` is the full
   rational-norm family.
4. Worker 1598's `representedInductionLeviEquiv` identifies this induction with
   the represented `leviInductionFunctor` of the intrinsic twist of
   `intrinsicLeviRep π` by `Φ⁻¹ χ₀`, where
   `Φ = parabolicLeviUnramifiedCharactersHomeomorph`. The radical is the
   supplied geometric radical, with the multiplication isomorphism
   `parabolicRadical_isIso_subgroupMultiplication`.
   `intrinsicLeviRep_isIrreducible_iff` transfers irreducibility of `π`.
5. `InducedIrreducibilityOpenStatement` gives a polynomial `f` whose principal
   open set contains `Φ⁻¹ χ₀`. Represented induction is irreducible on all of
   it.
6. `D = Φ⁻¹ ⁻¹' D(f)` is open by `isOpen_rationalUnramifiedPrincipalOpen` and
   continuity of `Φ⁻¹`. It contains `χ₀`. On `D` the literal induction is
   irreducible, by the equivalence of step 4.

## Dependencies

Besides published Library modules, the module imports the supporting modules
`ParabolicUnitaryPointIrreducibility`, `ParabolicRegularUnitaryTwist` and
`RegularSquareIntegrableJacquetMultiplicityReduction`, with their
dependencies, submitted for the same task. It also imports Worker 1598's
`RepresentedInductionComparison`.
