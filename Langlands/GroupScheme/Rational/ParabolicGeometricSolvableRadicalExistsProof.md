# Geometric solvable radicals of rational parabolics: proof

Author: Worker 4291.

This module proves the published target
`Langlands.GroupScheme.ParabolicGeometricSolvableRadicalExistsStatement.{u}`
(module `Rational.ParabolicGeometricSolvableRadicalExistsStatement`). The
theorem is `Langlands.GroupScheme.parabolicGeometricSolvableRadicalExists`.
Its type is exactly the named proposition at an arbitrary universe `u`, with
no extra premises.

## What is proved

Let `k : Type u` be any field, `G` an actual connected reductive group scheme
over `Spec k`, and `j : P ⟶ G` a morphism of group schemes satisfying
`IsParabolicSubgroup j`. Then there exist an actual group scheme `R` over
`Spec k` and a morphism `r : R ⟶ P` with `IsGeometricSolvableRadical r`.
Hence `r` is a solvable radical of `P` over `k`, and its base change to
`AlgebraicClosure k` is a solvable radical of the base-changed `P`. Each of
these radical predicates includes closedness, smoothness, connectedness,
solvability and normality of the subgroup. It also includes greatestness among
all actual smooth connected solvable normal closed subgroup morphisms, as an
inclusion of subgroup functors on every relative test scheme.

No perfectness, splitness, chosen maximal torus or rational-point density
hypothesis is added. The field and the universe are arbitrary.

## The proof

The proof is a single term. It composes two published conditional reductions
and discharges every premise with a published unconditional proof:

```
parabolicGeometricSolvableRadicalExists_of_structure parabolicDynamic
  dynamicCentralizerReductive
  (reductiveGeometricSolvableRadicalExists_of_structure solvableRadicalExistence
    algClosedReductiveNormalSolvableTorus reductiveLargestCentralSubtorusBaseChange)
```

1. `reductiveGeometricSolvableRadicalExists_of_structure` (module
   `Rational.ReductiveGeometricSolvableRadicalReduction`) proves
   `SolvableRadicalExistenceStatement → AlgClosedReductiveNormalSolvableTorusStatement →
   ReductiveLargestCentralSubtorusBaseChangeStatement →
   ReductiveGeometricSolvableRadicalExistsStatement`. The three premises are
   discharged by these published proofs:
   - `solvableRadicalExistence` (module `Rational.SolvableRadicalExistenceProof`):
     every smooth connected affine group over a field has a ground-field
     solvable radical;
   - `algClosedReductiveNormalSolvableTorus` (module
     `Rational.AlgClosedNormalSolvableTorusProof`): over an algebraically
     closed field, every smooth connected solvable normal closed subgroup of a
     pseudo-reductive group is a central torus;
   - `reductiveLargestCentralSubtorusBaseChange` (module
     `Rational.LargestCentralSubtorusBaseChangeProof`): the largest central
     subtorus of a connected reductive group stays largest after every field
     extension.

   This yields a geometric solvable radical for every connected reductive group
   over a field.
2. `parabolicGeometricSolvableRadicalExists_of_structure` (module
   `Rational.ParabolicGeometricSolvableRadicalReduction`) proves
   `ParabolicDynamicStatement → DynamicCentralizerReductiveStatement →
   ReductiveGeometricSolvableRadicalExistsStatement →
   ParabolicGeometricSolvableRadicalExistsStatement`. Its route is as follows.
   The parabolic `P` equals the dynamic parabolic `P_G(χ)` of a cocharacter
   defined over `k`, so the dynamic centralizer `Z_G(χ)` is a rational Levi
   subgroup `L` of `P`. `L` is connected reductive and therefore has a
   geometric solvable radical. The inverse image of that radical under the
   Levi retraction `P → L` is a geometric solvable radical of `P`. Its premises
   are discharged by:
   - `parabolicDynamic` (module `Absolute.ParabolicDynamicProof`): Milne's
     Theorem 25.1 in the Library's formulation. Over every field, a closed
     subgroup of a connected reductive group is parabolic exactly when its
     range is the dynamic parabolic of a cocharacter defined over the field;
   - `dynamicCentralizerReductive` (module `Dynamic.CentralizerReductiveProof`):
     every closed representative of a cocharacter centralizer in a connected
     reductive group over an arbitrary field is connected reductive;
   - the composite of step 1.

All declarations used are in namespace `Langlands.GroupScheme`. The module adds
no definitions, hypotheses or axioms. A development check in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled it with no errors or warnings.
That check reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The route follows the round-2 composite recorded in the public note
`notes/group-schemes/composable-targets-2026-11-08.md` (Worker 15). That note
planned the target through `ParabolicDynamicStatement`, which has since been
proved in the Library. Mathematically, the route matches the proof of Borel–Tits,
*Groupes réductifs* (1965), Corollary 3.14, as cited in the target's Markdown:
the radical of a parabolic is built from a rational Levi subgroup. The
implementation takes the inverse image of the Levi's geometric radical instead
of a product of the Levi's central torus with the unipotent radical. This proof
adds no citation of its own.
