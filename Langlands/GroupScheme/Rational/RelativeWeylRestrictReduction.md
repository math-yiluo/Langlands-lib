# Reduction of `N(k)/Z(k) ≅ N(U)/Z(U)` to structural statements

Author: Worker 1122.

This module assembles a conditional proof of the target
`Langlands.GroupScheme.RelativeWeylGroupRestrictStatement` (module
`Rational.TorusNormalizerStatement`). It does not prove the target: the five structural
statements below have no Library proofs yet.

## The structural inputs

`RelativeWeylStructuralInputs.{u}` is the conjunction of five published statements, all at
universe `u`:

1. `GenericMinimalParabolicStatement`: for a maximal split torus `i` of a connected reductive
   group over a field and a generic cocharacter `ν`, the dynamic parabolic of `ν ≫ i` is a
   minimal parabolic subgroup functor.
2. `MinimalParabolicConjugacyStatement`: any two minimal parabolic subgroups are conjugate by
   a rational point.
3. `MinimalParabolicSplitTorusConjugacyStatement`: two maximal split tori in one minimal
   parabolic are conjugate by a rational point of that parabolic.
4. `GenericCentralizerStatement`: the dynamic centralizer of a generic cocharacter is the
   whole torus centralizer.
5. `ParabolicSelfNormalizerStatement`: a parabolic subgroup is its own normalizer as a
   subgroup functor on all test schemes.

The definition only bundles these statements. Its provenance is the proof below, which uses
exactly these five premises.

## The theorem

`relativeWeylGroupRestrictStatement_of_structuralInputs` proves
`RelativeWeylStructuralInputs.{u} → RelativeWeylGroupRestrictStatement.{u}`. Let `i` be a
maximal split torus of a connected reductive `G` over a field `k`, and let `U` be a test
scheme whose underlying space is connected.

- A maximal split torus is a split subtorus. So `T` is a split torus, and the closed
  immersion `i` is a monomorphism (`IsClosedSubgroup.mono`).
- **Injectivity.** `relativeWeylGroupRestrict_injective` of
  `Rational.TorusNormalizerRigidity` applies, since a connected space is nonempty.
- **Surjectivity.** `RelativeWeylSurjective.relativeWeylGroupRestrict_surjective_of_rigid` of
  `Rational.RelativeWeylSurjectiveReduction` (Worker 823) takes statements 1–4 and the body
  of statement 5 at `k` and `G`. It also needs its rigidity hypothesis: every point of the
  torus normalizer over `U` acts on `T` through one automorphism of `T`. That is
  `TorusConjugation.exists_isNormalizingAut_of_connected` of
  `Rational.TorusNormalizerRigidity`, applied to each point.

## Relation to the sources

The target's Markdown derives it from Milne, *Algebraic Groups* (2017), 25.16(b)(c) and
25.17, and Borel–Tits (1965), Théorème 5.3. The surjectivity argument follows Borel–Tits 5.3,
as explained in the Markdown of `Rational.RelativeWeylSurjectiveReduction`. The Milne errata
warning on the classical proofs of the relative root system results (entry for p.549) is
not touched here: the argument uses neither the root-system axioms of the relative roots
nor their classical proofs, only the five premises above.
