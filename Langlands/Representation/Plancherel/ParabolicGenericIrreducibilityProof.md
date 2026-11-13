# Generic irreducibility of actual unramified parabolic induction: proof

Author: Worker 52. Module
`Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityProof`,
namespace `Langlands.Plancherel`. Entry module of the proof for Task 5066. The
argument is Worker 1597's reduction `ParabolicGenericIrreducibilityReduction`,
with both of its hypotheses discharged.

## What is proved

`conditionalParabolicGenericIrreducibility :
ConditionalParabolicGenericIrreducibilityStatement.{u, uV}` proves the
published proposition of module
`Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityStatement`
exactly, at independent universes `u` (field) and `uV` (carrier). The statement
fixes the following data:

- a nonarchimedean local field `F` and a connected reductive `G`, with `G(F)`
  locally compact, nonarchimedean and Hausdorff;
- a parabolic root presentation `r` of `p : P ⟶ G`, `l : M ⟶ P`,
  `a : A.toGrp ⟶ M`, and a geometric unipotent radical `n`;
- a semidirect decomposition `h` of the literal point groups, with closed
  unipotent and parabolic point groups and a continuous projection;
- a Haar measure on `M(F)/C`, where `C` is the split-component image;
- an irreducible smooth `π` of the literal Levi, square integrable modulo `C`.

It asserts a nonempty open set `D` of unramified characters of `M` such that
`UnramifiedLeviInduction h hU ν χ π` is irreducible for every `χ ∈ D`. This is
the open-locus consequence at the start of Waldspurger 2003, IV.3, printed
p. 285 / PDF p. 51 (`waldspurger-2003-plancherel`). The statement's own Markdown
documents it. This proof adds no hypothesis.

## Implemented proof

`exists_open_irreducible_unconditional` repeats the proof of the Library
theorem `exists_open_irreducible_of_statements`, with its two hypotheses
replaced as follows.

- **Irreducibility at regular unitary points.** In the reduction this is the
  parameter `hunit : UnitaryRegularParabolicIrreducibilityStatement`. Here it
  is the term
  `unitaryRegularParabolicIrreducibility_of_statements
  regularSquareIntegrableJacquetMultiplicity rationalReductiveUnimodularity
  standardCocharacter arbitraryParabolicQuotientCompact`.
  The first argument is proved in the supporting module
  `RegularSquareIntegrableJacquetMultiplicityProof`. The other three are
  published theorems. This is the composition that the Library's
  `conditionalParabolicGenericIrreducibility_of_structuralStatements` performs,
  except that the multiplicity input no longer needs the VII.2.4 criterion.
- **Renard VI.8.4 openness.** In the reduction this is the parameter
  `hopen : InducedIrreducibilityOpenStatement`, used once for the
  representation `intrinsicLeviRep pres π`. Here that use is
  `Renard.AlgebraicFamily.admissibleInducedIrreducibilityOpen` from the
  supporting module `AdmissibleInducedIrreducibilityOpen`. It has the same
  conclusion for irreducible admissible inducing representations. Its extra
  argument, admissibility of `intrinsicLeviRep pres π`, comes from the
  admissibility component `hsq.1` of square integrability modulo `C`. The
  published `isAdmissible_comp_continuousMulEquiv` transports it along the
  homeomorphic isomorphism `parabolicLeviPointHomeomorph pres`.

The remaining steps are unchanged from the reduction:

1. Square integrability supplies a unitary central character, and irreducibility
   makes `π` nontrivial.
2. `exists_unitary_twist_isNormalizerRegular` gives a unitary `χ₀` at which
   `π ⊗ χ₀` is normalizer-regular, and the induction is irreducible at `χ₀`.
3. `representedInductionLeviEquiv` identifies the literal induction with the
   represented induction of the intrinsic twist at `Φ⁻¹ χ₀`, where
   `Φ = parabolicLeviUnramifiedCharactersHomeomorph pres`.
4. The openness theorem gives a polynomial `f`. The set
   `D = Φ⁻¹ ⁻¹' D(f)` is open by `isOpen_rationalUnramifiedPrincipalOpen` and
   continuity of `Φ⁻¹`. It contains `χ₀`, and the literal induction is
   irreducible on it.

`conditionalParabolicGenericIrreducibility` introduces the binders of the
statement in the order used by
`conditionalParabolicGenericIrreducibility_of_statements`, installs
`hG.isAffineHom` and applies the theorem above.

## Supporting modules

The candidate also ships these modules, each with its own Markdown:

- `Langlands/Representation/Families/SubrepDetectionPrincipalOpen.lean`:
  irreducibility neighborhoods from detection of subrepresentations by fixed
  vectors.
- `Langlands/Representation/Families/AdmissibleInducedIrreducibilityOpen.lean`:
  Renard VI.8.4 for irreducible admissible inducing representations.
- `Langlands/Representation/Exponents/SelfUnitaryPieceMultiplicityUnconditional.lean`:
  the forward direction of Renard VII.2.4 from Casselman necessity, and the
  self-intersection bounds without the criterion.
- `Langlands/Representation/Plancherel/RegularSquareIntegrableJacquetMultiplicityProof.lean`:
  the multiplicity statement.

No Library file is edited.

## Checks

A `lean_check` of the five modules in the environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` gives zero errors and zero warnings.
`conditionalParabolicGenericIrreducibility` depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
