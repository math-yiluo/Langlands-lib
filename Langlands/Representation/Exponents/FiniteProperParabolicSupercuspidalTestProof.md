# A finite proper-parabolic supercuspidality test: proof

Worker 5115, under Task 5115 (`ea93fe45-ec73-41a7-aca0-ff6d5a72aa23`, the proof
task for Renard VI.7.5). Module
`Langlands.Representation.Exponents.FiniteProperParabolicSupercuspidalTestProof`.

## Statement proved

`finiteProperParabolicSupercuspidalTest :
FiniteProperParabolicSupercuspidalTestStatement.{u, v}` proves the published
proposition `Langlands.Aubert.General.RepresentedParabolic.FiniteProperParabolicSupercuspidalTestStatement`
of `Langlands/Representation/Exponents/SmoothRepNoetherianReduction.lean`, at
arbitrary field universe `u` and carrier universe `v`, with no added hypothesis.

The statement says: for every nonarchimedean local field `k` (with its valuation,
Hausdorff topology and local-field instances) and every connected reductive group
scheme `G` over `k`, with the canonical point topology on `G(k)` and every local
compactness and nonarchimedean-group instance, there are a natural number `n` and
`n` actual rational parabolic data `D i : ParabolicDatum G`, each with
`¬ IsIso (D i).p`, such that every smooth complex representation `A` of `G(k)`
(carrier universe `v`) whose normalized Jacquet modules along all `D i` are
`Subsingleton` is `IsSupercuspidal`, i.e. its normalized Jacquet module vanishes
along every proper actual rational parabolic datum. This is a finite form of
Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026), VI.2.1,
Remark 1, printed p.137 / PDF p.143; see the paired Markdown of
`SmoothRepNoetherianReduction` and `FiniteProperParabolicSupercuspidalTestReduction`
for the comparison with the source.

## Implemented proof

The proof is a single application of the published conditional reduction
`finiteProperParabolicSupercuspidalTest_of_structure` (Worker 1582, module
`Exponents/FiniteProperParabolicSupercuspidalTestReduction`), whose three
hypotheses are now discharged by published theorems:

- `ParabolicDynamicStatement.{u}` by `Langlands.GroupScheme.parabolicDynamic`
  (module `GroupScheme/Absolute/ParabolicDynamicProof`): over a field, a closed
  subgroup of a connected reductive group is parabolic exactly when it is a dynamic
  parabolic `P(χ)` (Milne, Theorem 25.1);
- `SmoothMaximalSplitTorusConjugacyStatement.{u}` by
  `Langlands.GroupScheme.smoothMaximalSplitTorusConjugacy` (module
  `GroupScheme/Rational/SmoothMaximalSplitTorusConjugacyProof`): maximal split tori
  of a smooth connected affine group are conjugate by a rational point;
- `RelativeRootSystemStatement.{u}` by `Langlands.GroupScheme.relativeRootSystem`
  (module `GroupScheme/Rational/RelativeRootSystemProof`): the relative roots of a
  maximal split torus of a connected reductive group form a root system.

The reduction itself chooses a maximal split torus with a generic cocharacter,
standardizes every proper actual parabolic datum to a proper face of the finite set
of simple relative roots, and picks one actual datum for each attained face; the
Jacquet module along an arbitrary proper datum is identified with the one along the
chosen datum of its face by a translation of coinvariants. The family is not
required to consist of standard parabolics.

A development `lean_check` of the module reported no errors or warnings and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Role in Task 5115

`FiniteProperParabolicSupercuspidalTestStatement` is an explicit premise (at carrier
universe `max u v`) of both published reductions of the VI.7.5 targets,
`smoothRepNoetherianCategory_of_blockInputs` (module
`Exponents/SupercuspidalFiniteTypeNoetherianReduction`) and
`leviInductionFiniteType_of_inputs` (module
`Exponents/LeviInductionFiniteTypeReduction`). This theorem removes that premise.
It does not prove either VI.7.5 target: their remaining premises (VI.1.3, the
represented cuspidal/remainder splitting, the VI.3/VI.4 block inputs and, for the
Theorem, the represented geometric lemma) are still unproved and owned by other
proof tasks.
