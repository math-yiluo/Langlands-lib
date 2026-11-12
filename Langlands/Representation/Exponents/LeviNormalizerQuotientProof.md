# Finiteness and faithfulness of `N_G(M)(F)/M(F)`: proofs

Author: Worker 5148, in proof task `822bbd74-8853-4535-87b2-aede25e9a259` (Renard VI.8.5).
This module proves the two statements of
[LeviNormalizerQuotientStatements](LeviNormalizerQuotientStatements.md) and their
conjunction. They are inputs 7 and 8 of `genericInducedIrreducibility_of_statements` in
[RenardGenericIrreducibilityReduction](../Families/RenardGenericIrreducibilityReduction.md).
The module does not prove the VI.8.5 Theorem itself.

## Statements proved

All three theorems are in namespace `Langlands.Aubert.General.RepresentedParabolic`, at the
field universe `u`, with exactly the binders of the published statements. No hypothesis is
added.

- `leviNormalizerFiniteQuotient : LeviNormalizerFiniteQuotientStatement.{u}`. For a
  nonarchimedean local field `k`, a connected reductive `G` over `k`, a parabolic
  `p : P ⟶ G` and a rational Levi `l : M ⟶ P`, there are finitely many points `g j` of
  `G(k)` normalizing `M` such that every point `w` normalizing `M` is `g j · m` with
  `m ∈ M(k)` (Renard V.4.3.3).
- `leviNormalizerNormFixing : LeviNormalizerNormFixingStatement.{u}`. In the same setting,
  a point `w` normalizing `M` through `φ : M ≅ M` with
  `‖χ(φ(a))‖ = ‖χ(a)‖` for every rational character `χ` of `M` and every `a` in the centre
  of `M(k)` lies in the image of `M(k)` (Renard V.3.5).
- `leviNormalizerWeylGroupStatements : LeviNormalizerWeylGroupStatements.{u}`, the pair of
  the two theorems above.

Here "`w` normalizes `M` through `φ`" means `φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom`,
as in the statements.

## Proof

The helper `exists_dynamicParabolic_isRepresentedBy` supplies, for a parabolic
`p : P ⟶ G` of a connected reductive group over any field `k`, a cocharacter
`χ : 𝔾_m ⟶ G` defined over `k` such that `p` represents the dynamic parabolic subgroup
functor `Dynamic.parabolic χ`. It applies the published proof `parabolicDynamic` of
`ParabolicDynamicStatement` (Milne, Theorem 25.1), which gives
`SubgroupFunctor.range p = Dynamic.parabolic χ`. Since `p` is a closed subgroup, its
underlying morphism of schemes is a monomorphism (`hp.isClosedSubgroup.mono`), so
`Over.mono_of_mono_left` gives the monomorphism half of `IsRepresentedBy`, and the range
equality is the other half.

With this cocharacter, both statements are instances of published theorems in
[DynamicLeviNormalizer](DynamicLeviNormalizer.md), which assume such a dynamic
presentation of `p`:

- `IsRationalLeviSubgroup.exists_finite_normalizer_representatives_of_dynamicParabolic`
  gives the finite family of representatives of `LeviNormalizerFiniteQuotientStatement`,
  with the same conclusion verbatim;
- `IsRationalLeviSubgroup.mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic` gives
  the membership `w ∈ pointImage (l ≫ p)` of `LeviNormalizerNormFixingStatement` from the
  normalizing equation and the norm hypothesis.

The conjunction is the pair of the two proofs.

`DynamicLeviNormalizer` works with a split component `A` of `M`: from the dynamic
presentation of `p` it obtains that the torus centralizer of `A` in `G` is the range of
`l ≫ p`, and then applies its finiteness and norm-rigidity results for split components;
see its Markdown. The present module adds only the dynamic presentation, so the two
published statements no longer need it as an input.

## Source

Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`): V.3.5 (printed pp.110–111,
PDF pp.116–117) and (V.4.3.3) (printed p.119, PDF p.125). The statements' Markdown records
the correspondence. The proof route here is the Library's, through Milne's Theorem 25.1 and
the published dynamic results, not the source's argument.
