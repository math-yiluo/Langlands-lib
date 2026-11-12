# Split parts of maximal tori in minimal rational parabolics: proof

Author: Worker 3905.

This module proves the unchanged published proposition
`Langlands.GroupScheme.MinimalParabolicTorusSplitPartStatement.{u}` from
`Langlands.GroupScheme.Rational.MinimalParabolicTorusSplitPartStatement`.
The final theorem `minimalParabolicTorusSplitPart` has exactly this
proposition as its type, at an arbitrary universe `u`. It adds no
hypothesis on the field, no rational-point density assumption and no
proposition-valued premise. Every structural input is a published
unconditional theorem of the Library.

## Route

The Library already contains the conditional reduction
`minimalParabolicTorusSplitPartStatement_of_radical_torus_levi`
(module `Rational.MinimalParabolicTorusSplitPartReduction`). It derives the
target from two geometric statements,
`ParabolicRadicalTorusLeviStatement` and
`MinimalParabolicLeviCentralizerStatement`. This module proves both of
them from `ParabolicDynamicStatement`, then supplies the published proof
`parabolicDynamic` of that statement.

### The Levi centralizer statement

`minimalParabolicLeviCentralizer_of_parabolicDynamic` proves
`MinimalParabolicLeviCentralizerStatement` from `ParabolicDynamicStatement`.
Let `j : P → G` be a minimal rational parabolic, `l : L → P` a rational
Levi and `r : R → P` a geometric solvable radical.

1. The forward direction of `ParabolicDynamicStatement`, applied to the
   closed parabolic `j`, gives a cocharacter `χ` over the ground field with
   `range j = Dynamic.parabolic χ`. Because `j` is a closed immersion,
   `j` represents `Dynamic.parabolic χ`.
2. `splitComponentStatement` (module `Rational.SplitComponentProof`) gives
   a split component `a : A → L` of the connected reductive group `L`.
3. `IsRationalLeviSubgroup.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic`
   (module `Rational.MinimalParabolicCompatibleRefinement`) shows that
   `a ≫ l ≫ j` is an ambient maximal split torus of `G`. This step uses
   the minimality of `j`.
4. `IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
   (module `Rational.OriginalLeviCocharacter`) gives
   `torusCentralizer (a ≫ l ≫ j) = range (l ≫ j)` on every test scheme.
5. `IsRationalLeviSubgroup.centralTorusRadicalFactor` (module
   `Rational.CentralLeviTorusRadical`) factors the closed central torus
   `a ≫ l` through the solvable radical underlying `r`, as an actual
   morphism `aR : A → R`. The lemma
   `centralTorusRadicalFactor_comp` gives `aR ≫ r = a ≫ l`.

Thus `aR ≫ r ≫ j = a ≫ l ≫ j`, and `B = A` with `bR = aR` witnesses the
statement.

### The adapted rational Levi statement

`parabolicRadicalTorusLevi_of_parabolicDynamic` proves
`ParabolicRadicalTorusLeviStatement` from `ParabolicDynamicStatement`.
It applies the published six-input assembly
`parabolicRadicalTorusLevi_of_structural_inputs` (module
`Rational.ParabolicRadicalTorusLeviReduction`) to the following inputs.

- `ParabolicGeometricSolvableRadicalExistsStatement`, obtained from
  `parabolicGeometricSolvableRadicalExists_of_structure` (module
  `Rational.ParabolicGeometricSolvableRadicalReduction`). Its three inputs
  are the given `ParabolicDynamicStatement`, `dynamicCentralizerReductive`
  (module `Dynamic.CentralizerReductiveProof`) and the following inline
  proof of `ReductiveGeometricSolvableRadicalExistsStatement`:
  `reductiveGeometricSolvableRadicalExists_of_structure` (module
  `Rational.ReductiveGeometricSolvableRadicalReduction`) applied to
  `solvableRadicalExistence` (`Rational.SolvableRadicalExistenceProof`),
  `algClosedReductiveNormalSolvableTorus`
  (`Rational.AlgClosedNormalSolvableTorusProof`) and
  `reductiveLargestCentralSubtorusBaseChange`
  (`Rational.LargestCentralSubtorusBaseChangeProof`).
- `maximalRankRadicalTorusIntersection`
  (`Absolute.MaximalRankRadicalTorusIntersectionProof`).
- `maximalTorusBaseChange` (`Torus.MaximalBaseChangeProof`).
- `borelContainingSubgroupConnectedStatement`
  (`Absolute.BorelContainingSubgroupConnected`).
- `ParabolicRadicalTorusCentralizerLeviStatement`, obtained from
  `parabolicRadicalTorusCentralizerLevi_of_dynamic` (module
  `Rational.ParabolicRadicalTorusInitialLevi`). Its inputs are the given
  `ParabolicDynamicStatement`, `dynamicCentralizerReductive` and
  `solvableMaximalTorusConjugacy`
  (`Rational.SolvableMaximalTorusConjugacyProof`).
- `maximalTorusCentralizer` (`Absolute.MaximalTorusCentralizerProof`).

### Assembly

`minimalParabolicTorusSplitPart_of_parabolicDynamic` combines the two
previous theorems through
`minimalParabolicTorusSplitPartStatement_of_radical_torus_levi`. The final
theorem `minimalParabolicTorusSplitPart` applies it to `parabolicDynamic`
(module `Absolute.ParabolicDynamicProof`), the published proof of
`ParabolicDynamicStatement`.

## Relation to the source

The statement Markdown cites Borel–Tits, *Groupes réductifs* (1965),
2.15(d), 4.2–4.3, 4.15(b), 4.16 and the split-part step of the proof of
4.18. The implemented proof does not follow the printed route through a
general rational Levi conjugacy theorem. It uses the dynamic presentation
`P = P_G(χ)` of the minimal parabolic. That presentation places a
cocharacter of the split component of any rational Levi so that it presents
`P` and has that Levi as centralizer, and minimality of `P` then makes the
split component ambient maximal. The conclusion of 4.18 is not used, and
neither is the split-group hypothesis of 4.6.

The intermediate theorem `minimalParabolicLeviCentralizer_of_parabolicDynamic`
is a conditional statement. Applied to `parabolicDynamic`, it gives
`MinimalParabolicLeviCentralizerStatement`, which is the target of the
separate proof task `065952dc-e6a6-4909-82c3-b7b626953155`. This module does
not state that unconditional theorem under a separate name.
