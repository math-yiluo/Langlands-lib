# Defining cocharacters in the specified Levi split component

Author: Worker 200.

This is an internal derived construction on the existing
`Langlands.GroupScheme` framework. It combines the published
[whole-group centralizer factorization](TorusCentralizerFactorization.md),
[split-torus factorization](SplitTorusFactorization.md), and
[compatible parabolic root presentation](ParabolicRootPresentation.md).
It introduces no new assertion from the literature and assumes no
representation-theoretic or analytic result.

The field `k : Type u` and its characteristic are arbitrary. The ambient
group need not be split or quasisplit. All subgroup equalities below concern
the full subgroup functors, including every test scheme and refinement.
The zero cocharacter and rank-zero cases are allowed.

## Factoring a defining cocharacter

Let `j : M → G` represent `Dynamic.centralizer χ`, where
`χ : Gm → G`, and suppose `M` has affine structure morphism. For any
specified actual split component `a : A → M`,
`IsSplitComponent.exists_cocharacter_factor_of_dynamicCentralizer` proves

`∃ ν : cocharacterLattice A, groupHom ν ≫ a ≫ j = χ`.

The published `torusCentralizer_gm_eq_dynamicCentralizer` turns the given
representative into a representative of the whole-group centralizer of `χ`.
The existing `torusCentralizerFactor` then factors `χ` through `M`, and
`isCentral_torusCentralizerFactor` proves that this factor is central in `M`.
The multiplicative group is split, so `IsSplitComponent.exists_factor`
factors this central map through the specified `A`. Writing that map as an
additive cocharacter and composing the two factorization equations proves
the displayed equality.

This result needs neither a closed representative nor smoothness,
connectedness or reductivity of either group. It assumes a representative
and an actual split component; it does not construct those objects.

## Preserving the original presentation torus

Let `r : ParabolicRootPresentation p l a` be an existing compatible
presentation of the specified maps `p : P → G`, `l : M → P` and
`a : A → M`, with affine `G`. Write `T,i,ν₀,J,f` for its data.
For every actual cocharacter `ζ` of `T` satisfying

`range (l ≫ p) = Dynamic.centralizer (groupHom ζ ≫ i)`,

`exists_splitComponentCocharacter_lift` produces a cocharacter `ν` of the
specified `A` with both

- `RealTorusSpace.cocharacterMapInt f ν = ζ`;
- `groupHom ν ≫ a ≫ l ≫ p = groupHom ζ ≫ i`.

Affineness of `M` follows from the connected-reductivity field of the
supplied rational Levi. Closedness of `l` and `p` makes their composite
monomorphic, so the assumed equality supplies the centralizer
representative required by the preceding factorization theorem.
The compatibility equation `groupHom f ≫ i = a ≫ l ≫ p` then identifies
the two ambient composites. Cancelling the monomorphic torus inclusion `i`,
which follows from its maximal splitness, proves the exact integral
cocharacter equality in `T`. No scalar multiple, conjugation or change of
torus is used.

## A chosen defining cocharacter

The presentation's existing `realization` field supplies one standard `ζ`
realizing both the specified parabolic and its Levi. Applying the lift
theorem to that witness proves `exists_splitComponentCocharacter`.
`splitComponentCocharacter` chooses a witness from this derived existence
theorem. Its three intrinsic laws state:

- `isStandard_splitComponentCocharacter`: its image under
  `cocharacterMapInt f` is standard for the original `i,ν₀,J`;
- `parabolic_eq_splitComponentCocharacter`: its ambient composite has
  dynamic parabolic exactly `range p`;
- `levi_eq_splitComponentCocharacter`: the same ambient composite has
  dynamic centralizer exactly `range (l ≫ p)`.

These laws preserve the literal specified maps and subgroup functors.
They do not assert uniqueness of the defining cocharacter.

The supplied compatible presentation retains all its structural
hypotheses, including its realization field. This construction proves no
general existence or independence theorem for such presentations and no
comparison with the opposite parabolic or its geometric unipotent radical.
In particular it does not discharge
`DynamicGeometricUnipotentRadicalStatement`, intertwining convergence,
rational continuation or any Plancherel assertion.
