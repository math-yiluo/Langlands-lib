# Parabolic elementary subgroups under homomorphisms of reductive groups

Authors: Worker 4953.

This module proves that an arbitrary homomorphism of connected reductive
groups over a field maps the parabolic elementary subgroup of the source
into that of the target. Both theorems are proved here, with no
hypotheses beyond those displayed.

## Statements

Let `k : Type u` be a field and let `A` and `G` be group schemes over
`Spec (CommRingCat.of k)` with `IsConnectedReductive A` and
`IsConnectedReductive G`. Let `a : A ⟶ G` be any homomorphism of group
schemes. It need not be a closed immersion, and its image need not be
normal.

- `rationalPoints_range_radical_le_parabolicElementarySubgroup`. Let
  `p : P ⟶ A` and `r : U ⟶ P` be homomorphisms with `IsParabolicSubgroup p`
  and `LeviSubgroup.IsGeometricUnipotentRadical r`. Then
  `(rationalPoints.map (r ≫ p ≫ a)).range ≤ parabolicElementarySubgroup G`.
  The image in `G(k)` of the `k`-points of the geometric unipotent radical
  of any parabolic subgroup of `A` lies in the parabolic elementary
  subgroup of `G`.
- `parabolicElementarySubgroup_map_le_of_hom`. The image of
  `parabolicElementarySubgroup A` under `rationalPoints.map a` is contained
  in `parabolicElementarySubgroup G`.

Here `parabolicElementarySubgroup G` is the subgroup of `G(k)` generated
by the `k`-points of the images of the geometric unipotent radicals of all
parabolic subgroups of `G`. It is the group `G(k)^+` of the Kneser–Tits
problem.

## Proofs

For the first theorem, the published proof `parabolicDynamic` of Milne's
Theorem 25.1 (`ParabolicDynamicStatement`) gives a cocharacter `χ` of `A`
over `k` with `SubgroupFunctor.range p = Dynamic.parabolic χ`. Since `p` is
a closed immersion, `p` represents `Dynamic.parabolic χ`. The affine
centralizer scheme of `χ` represents `Dynamic.centralizer χ`, and is
connected reductive by the published `dynamicCentralizerReductive`. The
published `Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer`
then identifies `SubgroupFunctor.range (r ≫ p)` with the identity-limit
subgroup `Dynamic.unipotent χ`. So every `k`-point in the range of
`r ≫ p` lies in `Dynamic.unipotent χ`. Its image under `a` lies in the
parabolic elementary subgroup of `G`, by the published
`map_dynamicUnipotent_le_parabolicElementarySubgroup`. That theorem applies
because `G` is connected reductive and `a` maps contracting points for `χ`
to contracting points for `χ ≫ a`.

The second theorem follows from the first and the universal property
`parabolicElementarySubgroup_le_iff`, applied to the inverse image of
`parabolicElementarySubgroup G` under `rationalPoints.map a`.

Both theorems use only the standard axioms.

## Provenance

This is an internal consequence of published Library proofs. The
underlying mathematics is the functoriality of the subgroup `G(k)^+` under
homomorphisms of reductive groups: a unipotent radical of a parabolic
subgroup is `U_A(χ)` for a cocharacter `χ`, and `a(U_A(χ)) ⊆ U_G(a ∘ χ)`.
The module is used for clause 17 of
`Langlands.GroupScheme.RankOneLeviPresentationStatement` in
`Langlands.GroupScheme.SimplyConnected.RankOneLeviFactors`.
