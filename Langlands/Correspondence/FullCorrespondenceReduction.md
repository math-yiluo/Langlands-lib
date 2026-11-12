# The full correspondence from a supercuspidal correspondence

Authors: Worker 1677 (shared draft revision 1, previous instance) and Worker 4809.

This module states and proves one intermediate result for task
`1ccfc228-cd00-4744-b7c2-42b1affdcf69`, the full local Langlands correspondence
for `GL_n`. It does not prove that task's unconditional target
`FullCorrespondenceStatement`. The supercuspidal correspondence remains a
hypothesis. It is the target of Task 4803
(`871c9ea7-1e86-44f8-bba0-6aa26b3ef474`). Every other ingredient is a published
Library proof, cited below by Lean name.

## Statement

`FullCorrespondenceFromSupercuspidalExistenceStatement.{uF, uP, uA}` says: for
every prime `p` and every `F : PadicField.{uF} p`, if
`SupercuspidalCorrespondenceExistence.{uF, uP, uA} F` holds, then
`FullCorrespondenceExistsUnique.{uF, uP, uA} F` holds. In words, if `F` has a
supercuspidal correspondence (some `SupercuspidalMap` satisfying
`IsSupercuspidalCorrespondence`), then `F` has exactly one full correspondence
(a `FullMap` satisfying `IsFullCorrespondence`, unique as a map on isomorphism
classes in every rank). The three universes `uF`, `uP` and `uA` of the field,
parameter carriers and representation carriers stay independent. The statement
is per field: the hypothesis is used only over the same field `F`.

### Provenance

The statement is derived. It combines two results of Henniart, *Une
caractérisation de la correspondance de Langlands locale pour GL(n)*, Bull.
Soc. Math. France 130 (2002), 587–602:

- Théorème 1.5 (printed p. 590, PDF p. 4). The supercuspidal bijections
  `π⁰_n` extend, through the Langlands and Zelevinsky classifications, to
  bijections `π_n` of `G(n)` onto `A(n)`. These agree with `π⁰_n` on
  irreducible classes, are compatible with contragredients there, and preserve
  all pair L- and epsilon-factors.
- Corollaire 1.8 (printed p. 592, PDF p. 6). A family of maps `τ_n` with
  `τ_1 = π⁰_1` and the pair L- and epsilon-factor identities equals `π_n`.

Henniart starts from the supercuspidal correspondence of Théorème 1.3 (printed
p. 589, PDF p. 3). Here only the existence of a supercuspidal correspondence is
assumed. The Library predicates `IsSupercuspidalCorrespondence` and
`IsFullCorrespondence` impose rank-one, determinant, twist, dual and pair-factor
conditions for one geometrically normalized reciprocity candidate. Their own
Markdown documents explain how these conditions relate to the source.

## Implemented proof

The proof composes published theorems. It does not follow Henniart's text.

`fullFactorCompatibilityAt_of_fullFactorCompatibility` specializes
`FullFactorCompatibility F e c` to `FullFactorCompatibilityAt F e ψ c`.
It evaluates the universal L-factor condition at `ψ`, opens the existential
epsilon system, and evaluates that system's universal epsilon condition at
the same character. The proof keeps the reciprocity family, epsilon assignment,
system certificate and base-reciprocity witness. It does not change the inner
factor predicates, which require self-dual measures to exist and quantify over
every such measure.

`fullCharacterization_of_extends_of_lCharacterization` proves
`FullCharacterizationStatement F` from `FullCharacterizationExtendsStatement F`
and `AssemblyLCharacterizationStatement F`. The extension statement shows that
the competitor extends the supercuspidal map. The L-part of
`FullFactorCompatibilityAt` supplies every pair test that the
L-characterization of assembly requires.

`fullCorrespondenceExistsUnique_of_henniartPrerequisites` assumes
supercuspidal existence, `ConditionalAssemblyStatement F` and
`FullCharacterizationStatement F`. It chooses a supercuspidal correspondence
`c0` and an assembly `c` of `c0`. The second conjunct of conditional assembly
shows that `c` is a full correspondence.

For uniqueness, let `τ` be any full correspondence. Its predicate gives its own
geometric reciprocity candidate `e`, rank-one compatibility and the full
pair-factor condition. The imported theorem
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists` provides a
`NontrivialAdditiveCharacter F`. The proof specializes the factor condition to
this character and applies `FullCharacterizationStatement` to `c0` and `τ`. Its
uniqueness conjunct gives `c = τ`.

`fullCorrespondenceExistsUnique_of_supercuspidalExistence` discharges the last
two hypotheses with published proofs, stated inside the proof as local `have`s.

- `ConditionalAssemblyStatement F` comes from
  `conditionalAssembly_of_fivePrerequisites` applied to the published
  `assemblyWellDefined`, `assemblyBijective`, `assemblyOperation`,
  `assemblyLInheritance` and `assemblyEpsilonInheritance`.
- `AssemblyLCharacterizationStatement F` comes from
  `assemblyLCharacterization_of_ingredients`. Its five ingredients are
  `assemblyWellDefined`, `assemblyBijective`, `assemblyLInheritance`,
  `RankinSelberg.squareIntegrablePoleOrderCharacterization`, and
  `assemblySquareIntegrablePreimage_of_headClassification` applied to
  `Classification.multisegmentHeadClassification` at the canonical topology.
- `FullCharacterizationExtendsStatement F` comes from
  `fullCharacterizationExtends_of_inputs` applied to the published
  `RankinSelberg.supercuspidalLocalConverse`,
  `RankinSelberg.supercuspidalLFactorCharacterization` and
  `LocalFactor.NonabelianSystem.unique`.

The theorem then combines extension and L-characterization into the full
characterization, as above.

`fullCorrespondenceFromSupercuspidalExistence` proves
`FullCorrespondenceFromSupercuspidalExistenceStatement` by applying the
previous theorem at each prime and field.

`fullCorrespondenceStatement_of_supercuspidalCorrespondence` derives
`FullCorrespondenceStatement` from `SupercuspidalCorrespondenceStatement`. It
uses only the existence part of the hypothesis. Uniqueness of the full
correspondence comes from the full characterization, not from supercuspidal
uniqueness. Once `SupercuspidalCorrespondenceStatement` is proved, this
theorem gives the task's target.

## Checks

Against Library commit `2c8da0356d4c25c4ee22a9d7c15cae7a7f55cf26`, the module
compiles with no errors or warnings. The proofs use only `propext`,
`Classical.choice` and `Quot.sound`. Compilation shows only that the
composition is correct. It does not show that the correspondence holds
unconditionally.
