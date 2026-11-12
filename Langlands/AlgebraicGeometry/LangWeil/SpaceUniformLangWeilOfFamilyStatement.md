# The algebraic-space form of Conrad's Lemma 4.6 from the scheme estimates in families

Author: Worker 69.

This module states the reduction of the algebraic-space form of Conrad's Lemma 4.6 to two
statements about families of schemes: the uniform Lang–Weil estimate and the uniform upper bound
for point counts. It is the last step of the Library's Lang–Weil route to the space form. The
module contains no proof.

## The statement

`SpaceUniformLangWeilOfFamilyStatement` is the implication

`FamilyLangWeilStatement → FamilyPointUpperBoundStatement → SpaceUniformLangWeilStatement`

in the same universe `u`, where

- `FamilyLangWeilStatement` (`Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilStatement.lean`)
  is the uniform Lang–Weil estimate, for every `d`: for a geometrically irreducible morphism of
  schemes `f : X ⟶ S`, locally of finite type and quasi-compact, with `S` of finite type over `ℤ`
  and every fibre of pure dimension `d`, there is `C > 0` with
  `|N_s − (#κ) ^ d| ≤ C (#κ) ^ (d − 1/2)` for every finite field `κ` and every
  `s : Spec κ ⟶ S`, where `N_s` is the number of `x : Spec κ ⟶ X` with `x ≫ f = s`;
- `FamilyPointUpperBoundStatement`
  (`Langlands/AlgebraicGeometry/LangWeil/FamilyPointUpperBoundStatement.lean`): for a morphism of
  schemes `f : X ⟶ S`, locally of finite type and quasi-compact, with `S` of finite type over `ℤ`,
  there is `C > 0` with `N_s ≤ C (#κ) ^ e` whenever the fibre of `f` over the image of `s` has
  dimension at most `e`;
- `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceUniformLangWeilStatement`
  (`Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceUniformLangWeilStatement.lean`) is the
  algebraic-space form of Conrad's Lemma 4.6: for a separated, quasi-compact, surjective
  morphism `f : Y ⟶ B` of algebraic spaces over `Spec (ULift ℤ)`, with geometrically connected
  fibres and a smooth chart square of relative dimension `d`, and `B` quasi-separated and of
  finite type over `ℤ`, there is `C > 0` with `|N_x − (#κ) ^ d| ≤ C (#κ) ^ (d − 1/2)` for every
  finite field `κ` and every `κ`-point `x` of `B`, where `N_x` is the number of `κ`-points of `Y`
  over `x`.

## Relation to the sources

Provenance: derived. Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011; registered source `conrad-2011-weil-grothendieck-adelic-points`), proof of
Theorem 5.9, printed p.17, needs Lemma 4.6 (printed p.12) "for algebraic spaces of finite
presentation over `Z`", and explains that the cohomological ingredients carry over from schemes
to separated algebraic spaces of finite type over a finite field through excision and
stratifications by schemes. This statement records the same passage from schemes to algebraic
spaces for the elementary route: the scheme results it assumes are formulated for families over
arbitrary bases of finite type over `ℤ`, so they can be applied to the finitely many scheme
strata of `B` and of `Y`. In the same spirit, Lang and Weil, *Number of points of varieties in
finite fields* (Amer. J. Math. 76 (1954); registered source `lang-weil-1954-number-of-points`),
§2, printed pp.823–824 (PDF pp.6–7), pass from projective varieties to abstract varieties by
removing lower-dimensional "frontiers", whose points are bounded by their Lemma 1.

## Expected proof route

The proof is not part of this module. A natural route:

1. The chart square makes the fibre `Y_x` over a `κ`-point `x` a separated algebraic space of
   finite type over `κ`, smooth of pure dimension `d`; with geometric connectedness it is
   geometrically irreducible.
2. A quasi-separated algebraic space of finite type over `ℤ` has a dense open subspace that is
   an affine scheme (Stacks Project, Proposition 66.13.3, Tag 06NH; the Library's
   `SeparatedDenseAffineOpenStatement` is the version over a field). By Noetherian induction
   `B` is a finite disjoint union of locally closed subspaces `B_i` that are schemes of finite
   type over `ℤ`, and over each `B_i`, after refining, `Y ×_B B_i` is a finite disjoint union of
   locally closed subspaces `Y_{ij}` that are schemes of finite type over `B_i`, one of which,
   `Y_{i0}`, has fibres that are dense open in the fibres of `Y`, while the fibres of the others
   have dimension less than `d`.
3. Every `κ`-point of `B` factors through exactly one `B_i`, since `Spec κ` is reduced and has
   one point, and its `κ`-points in `Y` are distributed among the `Y_{ij}`. Apply
   `FamilyLangWeilStatement` to `Y_{i0} ⟶ B_i` (geometrically irreducible fibres of pure
   dimension `d`) and `FamilyPointUpperBoundStatement` with `e = d − 1` to the other strata, and
   sum the finitely many bounds; for `d = 0` the lower-dimensional strata are empty.

## Status

Open. A proof is to be supplied through its own focused proof task.
