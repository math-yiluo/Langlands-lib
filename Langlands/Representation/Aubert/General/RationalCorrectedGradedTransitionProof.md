# The actual surviving graded transitions of the corrected Aubert complex

Module: `Langlands.Representation.Aubert.General.RationalCorrectedGradedTransitionProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

This module proves the exact published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCorrectedGradedTransitionStatement.{u, v}`
(module `Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets`).
The final theorem is

```lean
theorem rationalCorrectedGradedTransitionStatement :
    RationalCorrectedGradedTransitionStatement.{u, v}
```

It has independent universes `u` and `v` and takes no arguments. Every binder,
premise and quantifier of the target is kept. In particular, the group is
`RationalPoint k G.X` with `pointTopology` for every connected reductive `G`
over every nonarchimedean local field `k`. Positive characteristic, nonsplit
and non-quasisplit groups, empty simple-root sets and relative rank zero are
all covered. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound` (development check `5f388b29-f589-4278-aa05-d8db20951398`).

## Route

The published reduction `rationalCorrectedGradedTransitionStatement_of_inputs`
(RationalCorrectedGradedReduction) proves the target at every universe `v` from
`RationalCorrectedGradedTransitionInputs.{u}`. That reduction contains the
construction of the maps `β_s` and the proofs of their equivariance,
surjectivity, kernel and compatibility with the actual Jacquet transitions.
The inputs proposition has the target's binders and three conjuncts:

* compactness of every quotient `P_J \ G`;
* the fixed-order support hypotheses
  (`RationalCorrectedSurvivingSupportStatement`);
* for each grade, lift `m` and index `K` satisfying the comparison `hK`: the
  radical-intersection identities `(S1)`, `(S2)` and the squared modulus
  identity `(D07)`.

This module proves the inputs proposition in two steps.

### Assembly theorem

`rationalCorrectedGradedTransitionInputs_of_points_of_squaredModulus` takes

* `hPoints : StandardParabolicPointsStatement.{u}` and
* `hmod : RationalCorrectedOrbitSquaredModulusStatement.{u}`,

and proves `RationalCorrectedGradedTransitionInputs.{u}`. It introduces the
binders in the order of the inputs proposition and supplies the three
conjuncts.

1. Compactness of `P_J \ G` is
   `compactSpace_leftQuotient_parabolic i ν BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν J`.
   The published theorem `Langlands.BruhatTits.dynamicParabolicQuotientCompact`
   (BruhatTits.Parabolic.QuotientCompactProof) proves
   `DynamicParabolicQuotientCompactStatement`.
2. The support conjunct is the published
   `rationalCorrectedSurvivingSupportStatement_of_prerequisites`
   (RationalCorrectedSupportAssembly), applied to the pair
   `⟨hPoints, BruhatTits.dynamicParabolicQuotientCompact⟩` and then to the same
   binders.
3. `(S1)` and `(S2)` come from the published theorem
   `rationalCorrectedOrbitRadicalIntersectionStatement`
   (RationalCorrectedOrbitRadicalProof). `(D07)` is `hmod` applied to the same
   arguments.

All binders are passed unchanged. The local instance
`DecidableEq (Weyl i) := Classical.decEq _` is the one the target fixes.

### Discharging the two inputs

The final theorem applies `rationalCorrectedGradedTransitionStatement_of_inputs`
to the assembly theorem, which it applies to two published theorems:

* `Langlands.GroupScheme.standardParabolicPointsStatement_proof :
  StandardParabolicPointsStatement.{u}` (GroupScheme.Rational.StandardParabolicPointsProof).
  It is proved from `rationalBruhat` and `rootRankOneFactorization`.
* `Langlands.Aubert.General.RationalPointFamily.rationalCorrectedOrbitSquaredModulus :
  RationalCorrectedOrbitSquaredModulusStatement.{u}`
  (Representation.Aubert.General.RationalCorrectedOrbitModulusProof). It
  discharges the injectivity of `characterRestrict r.torusHom` that the
  conditional balance theorem
  `squared_modulus_of_characterRestrict_injective` requires.

No premise is added to the target. In particular, no finite-length,
admissibility, finite-generation, endpoint, compactness, Coxeter, compact-limit,
support, exactness or irreducibility premise is added: compactness and support
are proved by the published theorems above.

## Declaration-level dependencies

Used directly:

* `rationalCorrectedGradedTransitionStatement_of_inputs`,
  `RationalCorrectedGradedTransitionInputs` (RationalCorrectedGradedReduction);
* `compactSpace_leftQuotient_parabolic` and
  `Langlands.BruhatTits.dynamicParabolicQuotientCompact`;
* `rationalCorrectedSurvivingSupportStatement_of_prerequisites`
  (RationalCorrectedSupportAssembly);
* `rationalCorrectedOrbitRadicalIntersectionStatement`
  (RationalCorrectedOrbitRadicalProof);
* `Langlands.GroupScheme.standardParabolicPointsStatement_proof`;
* `rationalCorrectedOrbitSquaredModulus`;
* `simpleRelativeRootFintype` and `pointTopology`, which give the instances
  the target fixes.

## Transitive dependency ledger

The ledger comes from a recursive scan of the final theorem's type and value
(`ConstantInfo.getUsedConstantsAsSet`, development check
`1923dbfc-5ddd-4f1d-9b35-d84fd2d0f486`). The scan reached 135,511 constants,
whose project constants come from 2,460 modules. Of these, 118 modules are
under `Langlands.Representation`.

* **Langlands classification.** None. No module under
  `Langlands.Representation.Classification` is reached. The only project
  constants whose names contain "classification" are group-scheme facts:
  `GroupScheme.RelativeRoot.commutativeVectorClassification` (with its
  statement `CommutativeVectorClassificationStatement`),
  `centralStableVectorSubgroupOfClassification`,
  `centralStableVectorSubgroup_of_classification` and
  `nonempty_centralStableVectorSubgroupData_of_classification`. They classify
  commutative vector subgroups and belong to the group-scheme structure
  theory, not to representation theory.
* **Character independence.** Linear independence of Harish-Chandra
  characters of representations is not used. The independence results reached
  are algebraic. `GroupScheme.CharacterUnits.linearIndependent_unit` is
  linear independence of the character units in a group scheme's coordinate
  algebra. `HomogeneousVectorCoordinates.independent_weightSpaces` is
  independence of weight spaces. The rest are linear independence of simple
  relative roots (`HasRelativeRootSystem.linearIndependent_simpleRelativeRoots`)
  and of character-lattice elements, Galois descent of functions
  (`Descent.galoisFunctions_linearIndependent`), and algebraic independence
  of Laurent Frobenius coordinates
  (`PrimitivePolynomial.algebraicIndependent_of_frobIndep_encoding`).
* **Geometric lemma.** None. No constant named after the geometric lemma is
  reached, and neither is any geometric-lemma `K0` expansion module. From
  `GeometricK0Target` only the subgroup definition `geometricSourceIntersection`
  and its auxiliary `_proof_1` are reached. They come through the
  radical-intersection proof and contain no `K0` expansion.
* **Adjointness.** No adjunction between induction and Jacquet modules
  (Frobenius reciprocity, first or second adjointness) is reached. The project
  constants named after adjunctions are `Corepresented.adjunctionPointsEquiv`,
  `GeneralLinear.adjunction_homEquiv_symm_apply` and the coinvariant
  adjunction of faithfully flat coalgebra descent. These are scheme-level
  universal properties. Other names containing "adjoint" refer to the adjoint
  representation of a group scheme on its Lie algebra or to Mathlib category
  theory.

## Provenance

This is an internal assembly of published Library theorems. The mathematics
of the graded transitions follows Aubert's erratum (printed pp. 4689–4690) with
the Ban–Jantzen double-coset correction (Section 4, printed p. 162). The
citations are in the Markdown of `RationalCorrectedFiltrationTargets` and
`CorrectedFiltrationStatements`. Aubert's Proposition 3.2 is not used.
