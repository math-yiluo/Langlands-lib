# Geometric solvable radicals of parabolics from the structure theory

Author: Worker 1131.

This module reduces the published target
`ParabolicGeometricSolvableRadicalExistsStatement.{u}` (module
`Rational.ParabolicGeometricSolvableRadicalExistsStatement`) to three
published structure statements and proves the reduction. It does not prove
any of the three statements, so it does not discharge the target.

## The reduction statement

`ParabolicGeometricSolvableRadicalFromStructureStatement.{u}` is the
Prop-valued implication

```
ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
  ReductiveGeometricSolvableRadicalExistsStatement.{u} →
    ParabolicGeometricSolvableRadicalExistsStatement.{u}
```

All four propositions are published, and each is used unchanged:

- `ParabolicDynamicStatement` (module `Absolute.BorelStatement`): over every
  field, a closed subgroup of a connected reductive group is parabolic if and
  only if its range is the dynamic parabolic `P_G(χ)` of a cocharacter
  defined over the field;
- `DynamicCentralizerReductiveStatement` (module
  `Dynamic.CentralizerReductiveStatement`): every closed representative of
  the dynamic centralizer of a cocharacter of a connected reductive group is
  connected reductive;
- `ReductiveGeometricSolvableRadicalExistsStatement` (module
  `Rational.ReductiveGeometricSolvableRadicalExistsStatement`): every
  connected reductive group over a field has a geometric solvable radical;
- the conclusion is the target itself: every parabolic `j : P → G` of a
  connected reductive group over a field has some `r : R → P` with
  `IsGeometricSolvableRadical r`.

The universe parameter is shared by all four statements. Fields, groups and
parabolics are arbitrary. No perfectness, splitness or characteristic
restriction is added.

## The proof

`parabolicGeometricSolvableRadicalExists_of_structure` proves the
implication. Given the three hypotheses and a parabolic `j : P → G` of a
connected reductive `G` over `k`:

1. `IsParabolicSubgroup.exists_isRationalLeviSubgroup` from
   `Rational.LeviPreimageSolvableRadical` uses the first two hypotheses to
   give a rational Levi subgroup `l : L → P`. This is the dynamic centralizer
   `Z_G(χ)` of a cocharacter with `P = P_G(χ)`.
2. The Levi subgroup is connected reductive, so the third hypothesis gives
   a geometric solvable radical `c : C → L`.
3. `IsRationalLeviSubgroup.exists_isGeometricSolvableRadical` from the same
   module shows that the inverse image of `C` under the Levi retraction
   `P → L` is a geometric solvable radical of `P`.

## Provenance

This is a derived internal reduction. Its route follows the proof of
Borel–Tits, *Groupes réductifs*, Corollary 3.14, cited in the target's
Markdown, which builds the radical of a parabolic from a rational Levi
subgroup and the unipotent radical. The implementation forms the inverse
image of the Levi radical instead of a product with a central torus. The
external content of the three hypotheses is documented in their own
statement Markdown. This module adds no new citation and no new external
structural assertion. The hypotheses are explicit premises of the stated
implication; they are not proved here.
