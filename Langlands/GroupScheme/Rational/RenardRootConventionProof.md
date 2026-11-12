# Proof of Renard's radical weights and simple indivisible roots

Author: Worker 4478. The composition was identified in Worker 15's note
`notes/group-schemes/composable-targets-2026-11-08.md`.

Module `Langlands.GroupScheme.Rational.RenardRootConventionProof`.

## Result

`Langlands.GroupScheme.renardRootConvention` has type exactly
`RenardRootConventionStatement.{u}`, the published proposition of
`Langlands.GroupScheme.Rational.RenardRootConventionStatement`, at an arbitrary
universe `u`. The statement and the definitions it imports are unchanged.

It applies to every field `k : Type u`, connected reductive `G`, maximal split
torus inclusion `i : T → G` and generic cocharacter `ν`. Let `U` be the actual
dynamic unipotent subgroup functor `Dynamic.unipotent (groupHom ν ≫ i)`. Let
`pos`, `redPos` and `simple` be the three local sets of the statement, built from
the conjugation Lie-weight support of `U`. The theorem proves the four
equalities

- `pos = positiveRelativeRoots i ν`;
- `redPos = RelativeRoot.indivisiblePositiveRoots i ν`;
- `redPos = reducedPositiveRelativeRoots i ν`;
- `simple = simpleRelativeRoots i ν`.

Characteristic is arbitrary and `G` need not be split. Nonreduced relative root
systems and rank zero, where all root sets are empty, are included. The proof
adds no root-system, linear-independence or comparison premise.

## Implemented proof

The proof is one application:

`renardRootConventionStatement_of_relativeRootSystem relativeRootSystem`.

Both ingredients are published Library theorems.

- `relativeRootSystem`, in module `Rational.RelativeRootSystemProof`, proves
  `RelativeRootSystemStatement.{u}` unconditionally. For each connected reductive
  `G` over a field and each maximal split torus `i`, it gives
  `HasRelativeRootSystem i`. This is a finite, crystallographic and possibly
  nonreduced root pairing on the rational span of the relative roots, whose
  roots are exactly the rationalized actual relative roots.
- `renardRootConventionStatement_of_relativeRootSystem`, in module
  `Rational.RenardIndivisibleRootComparison`, proves the implication
  `RelativeRootSystemStatement.{u} → RenardRootConventionStatement.{u}`.

The implication proceeds as follows for fixed `k`, `G`, `i` and `ν`.

1. Connected reductivity gives the affine instance and smoothness, hence local
   finite type. Maximal splitness gives the monomorphism instance and
   splitness of `T`.
2. The first equality is
   `RelativeRoot.nonzero_actionWeightSupport_dynamicUnipotent` (module
   `Rational.RenardRadicalWeightComparison`). It identifies the actual
   conjugation weight support of the dynamic radical with the positive relative
   roots. Its inputs are the published tangent-submodule computation of the
   dynamic radical and the published support bound for subgroups of it, so it
   needs neither a root-system nor a semigroup-realization assumption. The
   explicit nonzero filter changes nothing, since every relative root is
   nonzero.
3. After rewriting `pos`, `RelativeRoot.indivisibleRoots_inter_positiveRelativeRoots`
   identifies `redPos` with `indivisiblePositiveRoots i ν` by set
   extensionality, which gives the second equality.
   `RelativeRoot.indivisiblePositiveRoots_eq_reducedPositiveRelativeRoots` gives
   the third. It reorders the two quantifiers and uses that `1 < n` holds
   exactly when `2 ≤ n`.
4. The fourth equality is
   `HasRelativeRootSystem.indivisiblePositiveRootComparison`, applied to the
   root-system witness for `i` supplied by `relativeRootSystem`, splitness and
   genericity of `ν`. Its proof identifies actual roots with root-pairing
   indices and actual indivisibility with indivisibility in the pairing. The
   indecomposables of the indivisible positive roots are then the base of the
   restricted pairing `indivisiblePairing`. By the generic
   `image_baseOf_indivisiblePairing`, this base equals the base of the full,
   possibly nonreduced, pairing, which `mem_base_iff` identifies with the
   published `simpleRelativeRoots i ν`.

The kernel check of this module reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance and scope

The statement's Markdown gives the source: Renard, *Représentations des groupes
réductifs p-adiques* (9 July 2026), V.3.4 (printed p.110, PDF p.116) and V.3.12
(printed p.112, PDF p.118), extended explicitly from local fields to arbitrary
fields. This proof does not follow a proof printed in Renard. It is an internal
composition of the published theorems named above. The structural input is the
relative root system theorem, Milne 25.16–25.17 and Borel–Tits 5.8, proved in the
Library by the Conrad–Gabber–Prasad C.2.15 route.

The proof does not show that the dynamic parabolic is minimal. Compatible
parabolic presentations, independence of restricted roots and cones from choices,
central-direction decompositions and the temperedness criterion are not proved
here.
