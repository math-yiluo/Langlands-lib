# Assembly of singleton sharp-fixer boundedness (KP Corollary 7.3.14)

This module puts together the pieces of the proof of KP Corollary 7.3.14 for a
single point. It works with the actual building data
`B : ValuationBuildingData G`, at arbitrary universe `u`. Here `F` is a
nonarchimedean local field, `G` is the connected reductive group of `B`, and
`i = B.i : S → G` is its maximal split torus. `Z` is the centralizer
`B.centralizer.Z` with embedding `j = B.centralizer.j`, and `N(F)` is
`normalizerPoints B.i`. `G(F)^1` and `Z(F)^1` are the norm-one subgroups
`rationalCommonNormKernel`. For a root `b` and a point `x` of the apartment,
`U_{b,x,0}` is `B.apartment.chamberRootGroup x false b`, the zero-depth root
group at `x` used in the Library's chamber-product results.

It has two explicit premises, which other parts of the project supply:

- boundedness of `j(Z(F)^1)` in `G(F)` (the image of `Z(F)^1`);
- the KP Proposition 7.3.12 cover of the sharp fixer for generic cocharacters
  (premise `hcover` of `sharpFixerBoundedness_of_cover`, described below).

No Bruhat decomposition, boundedness of stabilizers or
`HasBoundedOpenStabilizers` is assumed.

## Root-group products are bounded

- `exists_indivisiblePositiveRoots_enumeration`: for every cocharacter `ν`, the
  set `RelativeRoot.indivisiblePositiveRoots B.i ν` (the indivisible roots
  positive on `ν`) is the range of a map `Fin n → relativeRoots B.i`. The relative
  roots form a finite set (`IsSplitTorus.finite_relativeRoots`), so this subset
  can be listed by an equivalence with `Fin (card)`.
- `isAlgebraicallyBounded_iSup_chamberRootGroup`: under the apartment axioms
  (`hB : B.apartment.SatisfiesApartmentAxioms B.centralizer`), for every point
  `x`, depth flag `strict` and cocharacter `ν`, the subgroup
  `⨆_{b > 0 on ν} U_{b,x,0}` (or `U_{b,x,0+}`) is algebraically bounded in `G(F)`.

  Proof: by the Library's `range_orderedPositiveChamberBlockProduct_eq_iSup`,
  applied to the enumeration above, this subgroup equals the range of a finite
  ordered product of chamber root blocks. Its hypotheses, that the extended
  affine roots form an affine root system (in the sense of
  `IsAffineRootSystemWithRankZero`, which allows every rank, including rank
  zero) and that their derivatives are the relative roots, come from the
  apartment axioms. The range is compact (`isCompact_range_orderedChamberBlockProduct`,
  from topology compatibility). Compact sets are bounded
  (`isAlgebraicallyBounded_of_isCompact`).

## The exchange product

- `normOneExchangeProduct B x ν` (definition): the subset
  `U⁻_x · U⁺_x · N(F)^1_x` of `G(F)`, where
  `U⁻_x = ⨆_{b > 0 on -ν} U_{b,x,0}`, `U⁺_x = ⨆_{b > 0 on ν} U_{b,x,0}`, and
  `N(F)^1_x = normOneNormalizerStabilizer B x` is the subgroup of elements of
  `N(F)` of norm one that fix `x`.
- `isAlgebraicallyBounded_normOneExchangeProduct`: under the apartment axioms,
  if `j(Z(F)^1)` is bounded then so is `normOneExchangeProduct B x ν`. Each factor
  is bounded: the first two by the previous section, and `N(F)^1_x` by
  `isAlgebraicallyBounded_normOneNormalizerStabilizer`. Products of bounded sets
  are bounded (`IsAlgebraicallyBounded.mul`).

## From the cover to the sharp fixer

- `sharpFixer_inf_stabilizer_le_normOneNormalizerStabilizer`: when the apartment
  is topology compatible, `G(F)^♯_x ⊓ N(F)_x ≤ N(F)^1_x`, where
  `G(F)^♯_x = B.sharpFixer {x}` and `N(F)_x` is the image in `G(F)` of the
  stabilizer of `x` in `N(F)`. This holds because the sharp fixer lies in
  `G(F)^1` (`sharpFixer_le_rationalCommonNormKernel`).
- `isAlgebraicallyBounded_sharpFixer_of_subset`: under the apartment axioms, if
  `j(Z(F)^1)` is bounded and
  `G(F)^♯_x ⊆ U⁻_x · U⁺_x · (G(F)^♯_x ⊓ N(F)_x)` for one cocharacter `ν`, then
  `G(F)^♯_x` is bounded. The right side lies in `normOneExchangeProduct B x ν` by
  the previous lemma.
- `isAlgebraicallyBounded_image_centralizerNormKernel_of_isCompact`: if `Z(F)^1`
  is compact in the canonical topology of `Z(F)`, then `j(Z(F)^1)` is bounded
  in `G(F)`. Compact sets are bounded, and images of bounded sets under
  morphisms of affine schemes are bounded
  (`IsAlgebraicallyBounded.image_rationalPointsMap`). The local instance
  `sharpAssemblyCentralizerAffine` records that `Z` is affine: `j` is a closed
  immersion into the affine `G`.
- `sharpFixerBoundedness_of_cover`: the target statement
  `B.SharpFixerBoundednessStatement` follows from two premises. The first is
  boundedness of `j(Z(F)^1)`. The second, `hcover`, says: under the apartment
  axioms, for every `x` and every generic cocharacter `ν`
  (`IsGenericCocharacter B.i ν`, no relative root vanishes on it),
  `G(F)^♯_x ⊆ U⁻_x · U⁺_x · (G(F)^♯_x ⊓ N(F)_x)`.

  Proof: a generic cocharacter exists (`IsSplitTorus.exists_genericCocharacter`,
  for the split torus `S`), and the previous lemma applies.

## Provenance and scope

This is an internal assembly for KP Corollary 7.3.14 (Kaletha–Prasad 2023, §7.3,
printed pp. 250–252, PDF pp. 281–283). KP prove it from Proposition 7.3.12,
`G(k)^♯_x = U⁻_x U⁺_x N(k)^♯_x` for the subgroups generated by the root groups of
the roots negative and positive on a generic direction. They then use that the
root-group factors are bounded and that `N(k)^♯_x` is bounded because its image
in the affine Weyl group fixes `x` and `Z(k)_0` is bounded. Products of bounded
sets are bounded (KP Lemma 2.2.6).

Here the cover is the premise `hcover`, with third factor
`G(F)^♯_x ⊓ N(F)_x`. It is placed inside the larger subgroup `N(F)^1_x`, which
is bounded by the module `NormalizerNormOneFixerBoundedness` once `Z(F)^1` is.
The root-group factors are bounded because they are compact finite ordered
products of chamber root blocks, which the Library proves under the apartment
axioms. The premise `hcover` and the boundedness of `j(Z(F)^1)` are not proved
here. Only the singleton case `Ω = {x}` of the corollary is treated.
