# Standard parabolics of a standard Levi for the negated cocharacter

Lean module: `Langlands.Representation.LanglandsClassification.OppositeUntwistLeviRoots`.

This is an internal helper module for the proof of
`OppositeUntwistTemperedCriterionStatement` (module
`OppositeUntwistTemperedCriterion`). That proof applies the standard
reduction of Casselman's temperedness criterion to the standard Levi `M_K` of a
label `K`. It uses the maximal split torus of `G` and the negated generic
cocharacter `-ν`. This module lists the standard data of `M_K` for `-ν` and
relates them to the standard and opposite data of `G` for `ν`. Nothing here is
a statement from the literature. These are the elementary root-system and
subgroup identities that the reduction needs, at the level of the Library's
actual group-scheme objects.

## Negation of roots (namespace `Langlands.GroupScheme`)

Fix a torus `i : T → G` and a cocharacter `ν`. Suppose the relative roots are
stable under negation.

- `latticePairing_neg_cocharacter`: `⟨α, -ζ⟩ = ⟨-α, ζ⟩`.
- `mem_positiveRelativeRoots_neg`, `mem_simpleRelativeRoots_neg`: `α` is
  positive (simple) for `-ν` iff `-α` is positive (simple) for `ν`.
- The imported `IsGenericCocharacter.neg` supplies genericity of `-ν`.
- `IsStandardCocharacter.negIndexSet`: if `ζ` is a standard cocharacter of
  `(ν, J)`, then `-ζ` is a standard cocharacter of `(-ν, -J)`.
  - `-J` is the pointwise negation of the set `J`.
- `neg_subset_simpleRelativeRoots_neg`: if `J` consists of simple roots for
  `ν`, then `-J` consists of simple roots for `-ν`.

This module reuses `IsGenericCocharacter.neg` from
`RationalOppositeChamber`. That module also has `IsStandardCocharacter.neg`,
whose set argument uses the image `Neg.neg '' J`; the pointwise-set version
`negIndexSet` is retained here.

## Standard and opposite data (namespace `...OppositeStandardJacquetFamily.Nesting`)

Here `G` is connected reductive, `i` is a maximal split torus and `ν` is a
generic cocharacter.

- `relativeRoots_neg_mem`: the relative roots are stable under negation. This
  is the Library's `relativeRootNegation`.
- `standardLevi_neg`: for `J ⊆ Δ(ν)`, the standard Levi of `(-ν, -J)` equals
  the standard Levi of `(ν, J)`.
- `standardParabolic_neg`: the standard parabolic of `(-ν, -J)` is the range of
  the chosen opposite parabolic `(OppositeStandardJacquetFamily.datum J).p`,
  which is the opposite of the standard parabolic of `J`.

## Inside the standard Levi `M_K`

- `leviTorus K`: the maximal split torus `T`, factored through the standard Levi
  `M_K = Standard.leviScheme i ν K`. Then `leviTorus_comp` says that composing
  with the inclusion `M_K → G` gives back `i`, and
  `isMaximalSplitTorus_leviTorus` says that it is a maximal split torus of `M_K`.
- `isRepresentedBy_leviHom_neg`, `standardLeviTorusFactor_neg`: the comparison
  maps of the Library's standard-Levi family theorem for `(-ν, -K)` are the
  ones above.
- `leviTorus_neg_families`: inside `M_K` with the torus `leviTorus K` and the
  cocharacter `-ν`, the following hold. The simple roots are exactly `-K`;
  `-ν` is generic; and for every `J' ⊆ -K`, the standard parabolic and standard
  Levi of `(-ν, J')` in `M_K` are the preimages, under `M_K → G`, of the
  standard parabolic and standard Levi of `(-ν, J')` in `G`. This applies the
  Library's `standardLeviStandardFamilies` to `(-ν, -K)`.
- `negIndex hJ'`: for `J' ⊆ -K`, the set `-J'` as a standard label for `ν`.
  Then `negIndex_val` gives its value, and `negIndex_subset` says that it is
  contained in `K`.
- `range_comp_leviHom_of_standardParabolic`: take a parabolic `p' : P' → M_K`
  whose range is the standard parabolic of `(-ν, J')` in `M_K`. Then the range
  of `P' → M_K → G` is the intersection of `M_K` with the opposite parabolic of
  the label `-J'`. `pointImage_comp_leviHom_of_standardParabolic` is the same
  statement for rational points.
- `isRepresentedBy_leviInclusion`: the inclusion `M_J → M_K` (from
  `OppositeStandardNesting`) represents the preimage in `M_K` of the standard
  Levi of `J`.
- `isRepresentedBy_comp_of_standardLevi`: take a Levi `l' : M' → P'` whose
  composite range is the standard Levi of `(-ν, J')` in `M_K`. Then `l' ≫ p'`
  represents the same subgroup functor as `M_{-J'} → M_K`.
- `testLeviIso`, `testLeviIso_hom_comp`: the resulting isomorphism
  `M' ≅ M_{-J'}`, which is compatible with the maps into `M_K`.
