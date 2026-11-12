# A rational Levi adapted to a maximal torus in a parabolic: proof

Author: Worker 4060.

`Langlands.GroupScheme.parabolicRadicalTorusLevi` proves exactly the
published `Langlands.GroupScheme.ParabolicRadicalTorusLeviStatement.{u}`.
For every field `k : Type u`, connected reductive `G`, actual rational
parabolic `j : P → G` and actual rational maximal torus `t : T → G`
with a specified `f : T → P` such that `f ≫ j = t`, it supplies the
statement's witnesses. These are a represented geometric solvable radical
`r : R → P`, a commutative `S` with a closed `sT : S → T` and a maximal
torus `sR : S → R` satisfying `sT ≫ f = sR ≫ r`, and the all-test equality
`range (sT ≫ f) = range f ⊓ range r`. They also include an actual rational
Levi `l : L → P` such that `l ≫ j` represents `torusCentralizer (sT ≫ t)`,
with `sL : S → L`, `sL ≫ l = sT ≫ f`, and `sL` a largest closed central
subtorus of `L`.

## Implemented proof

The theorem is a single term. It applies the published assembly
`parabolicRadicalTorusLevi_of_structural_inputs` (module
`Rational.ParabolicRadicalTorusLeviReduction`) and discharges all six of its
structural premises with published unconditional proofs.

1. *Parabolic geometric solvable radicals.*
   `parabolicGeometricSolvableRadicalExists_of_structure` is applied to
   `parabolicDynamic` (Milne 25.1 in the Library's formulation) and
   `dynamicCentralizerReductive`. Its third premise is proved by
   `reductiveGeometricSolvableRadicalExists_of_structure`, applied to
   `solvableRadicalExistence`, `algClosedReductiveNormalSolvableTorus` and
   `reductiveLargestCentralSubtorusBaseChange`. That reduction shows that
   the ground-field solvable radical of a connected reductive group is a
   geometric solvable radical. The parabolic reduction writes `P = P_G(χ)`
   with the rational Levi `Z_G(χ)`, and takes the inverse image of the
   geometric solvable radical of `Z_G(χ)` under the Levi retraction.
2. *Maximal-rank radical intersection.*
   `maximalRankRadicalTorusIntersection`.
3. *Maximal tori under field extension.* `maximalTorusBaseChange`.
4. *Connectedness of subgroups containing a Borel.*
   `borelContainingSubgroupConnectedStatement`.
5. *Centralizer Levis of radical maximal tori.*
   `parabolicRadicalTorusCentralizerLevi_of_dynamic` is applied to
   `parabolicDynamic`, `dynamicCentralizerReductive` and
   `solvableMaximalTorusConjugacy`. It obtains one maximal torus of the
   supplied radical from the dynamic Levi, with ambient centralizer the
   image of an actual rational Levi. Rational conjugacy of maximal tori in
   the smooth connected affine solvable radical then moves this to every
   supplied maximal torus of the radical.
6. *Self-centralization of maximal tori.* `maximalTorusCentralizer`.

Inside the assembly, item 1 gives `r`. The published
`IsParabolicSubgroup.exists_radicalTorusIntersection_of_structural_inputs`
uses items 2–4 to construct `S`, `sT` and `sR` with the composite equation
and the all-test intersection equality. Item 5 gives the rational Levi
for `sR`; the composite equation rewrites its ambient torus map to
`sT ≫ t`. Finally `IsRationalLeviSubgroup.radicalIntersectionCenter`,
with item 6 for the original maximal torus `t`, gives `sL`, its
factorization and greatestness among all closed central tori of `L`.

## Scope

The theorem's type is exactly the published proposition at arbitrary
universe `u`, with no added hypothesis. No splitness or perfectness of
the field, density of rational points, or Levi or radical existence
premise is assumed. The radical, centralizer and intersection claims keep
their quantification over every test scheme. The rational Levi retains its
actual multiplication isomorphism with a geometric unipotent radical. The
development check in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
reported only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This proof is an internal composition of the named published Library
results; the route follows the composite recorded in the public note
`notes/group-schemes/composable-targets-2026-11-08.md`. The original
mathematics is Borel and Tits, *Groupes réductifs* (1965), 3.14, 4.2–4.3
and the constructions in the proofs of 4.15(b) and 4.18, as documented in
the unchanged statement pair `ParabolicRadicalTorusLeviStatement`. The
Lean route need not follow those proofs, and no new external assertion is
introduced here.
