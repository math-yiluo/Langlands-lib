# Proof of the nonvanishing criterion for the spaces `E(λ)`

This module proves `Langlands.GroupScheme.SplitBorelInducedNonvanishingStatement.{u}` (module
[`Rational.BorelInducedNonvanishingStatement`](BorelInducedNonvanishingStatement.md)) as the
theorem `Langlands.GroupScheme.splitBorelInducedNonvanishing`. The theorem's type is exactly the
published proposition, in every universe `u`, and it adds no hypotheses: `k` is an arbitrary field,
`G` an affine group scheme over `Spec k` with a split pinning `p`, `ν` any cocharacter of the
pinned torus with `⟨α, ν⟩ < 0` for every simple root `α`, `i : B' ⟶ G` any closed subgroup
representing the dynamic parabolic `P(ν)`, `t` any factorization of the torus inclusion through
`B'`, and `χ` any character of `B'`. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

The statement is Milne, *Algebraic Groups* (2022 corrected reprint), Proposition 22.27(a),
p.471: `E(λ) ≠ 0` if and only if `λ` is dominant. The proof below does not follow Milne's route
through the contragredient of a simple module of highest weight `−w₀λ`. It reduces both directions
to the Library's realized coordinates (`SplitPinning.IsRealizedBy`, module
`Reductive.SplitBorelCell`): a coordinate realizes `λ` when it is left covariant for the negative
Borel subgroup `p.negativeBorel` with the extended character `p.borelCharacter λ`, invariant under
right multiplication by the positive unipotent subgroup `p.positiveUnipotent`, and has value one at
the identity.

## Auxiliary results in this module

- `SplitPinning.nonneg_latticePairing_root_iff_not_isPos`: if `⟨α, ν⟩ < 0` for every simple root
  `α`, then a root `β` satisfies `0 ≤ ⟨β, ν⟩` exactly when `β` is not positive for `p.base`.
  Mathlib's `RootPairing.Base.exists_root_eq_sum_int` writes `β` as an integral combination of the
  simple roots whose coefficients are all nonnegative (and not all zero) or all nonpositive (and
  not all zero). In the first case `⟨β, ν⟩ < 0` and the height of `β`, the sum of the
  coefficients (`RootPairing.Base.height_eq_sum`), is positive; in the second case `⟨β, ν⟩ > 0`
  and the height is negative.
- `SplitPinning.parabolic_eq_of_neg_simpleRoots`: under the same hypothesis on `ν`, the dynamic
  parabolic `P(ν)` of `groupHom ν ≫ p.inclusion` equals the dynamic parabolic of
  `Dynamic.oppositeCocharacter p.positiveGm`, which `p.negativeBorelHom` represents. The opposite
  of `p.positiveGm` is the cocharacter `−p.positiveCocharacter`
  (`groupHom_neg_comp_eq_oppositeCocharacter`, module `Rational.RelativeTitsNondegeneracy`), which
  is also negative on the simple roots, because `p.positiveCocharacter` pairs positively with the
  positive roots (`latticePairing_root_positiveCocharacter_pos_iff`). By the previous lemma the two
  cocharacters pair nonnegatively with the same roots; the roots of `p.inclusion` are the roots of
  `p.rootDatum` (`p.isRootDatum`). The Library theorem `relativeRootSignInclusions` (module
  `Rational.RelativeRootSignInclusionsProof`) turns this equality of nonnegative root sets into the
  two inclusions of dynamic parabolics; the torus is a maximal split torus by
  `IsMaximalTorus.isMaximalSplitTorus`.
- `HomogeneousQuotientFromEmbedding.isRightCharacterCovariant_iff_coordinate`: for any
  homomorphism `i : H ⟶ G` of affine group schemes, a global function `f` satisfies
  `IsRightCharacterCovariant i χ f` exactly when the coordinate `coordinateEquiv G f` of
  `x ↦ f(x⁻¹)` lies in `leftCovariantSubspace i (characterCoordinate H (−χ))`. This is the
  pointwise computation of the Library's `mem_rightCharacterCovariantSpace_iff_coordinate` (module
  `HomogeneousCharacterCoordinates`), stated without a homogeneous quotient: `f(gb) = χ(b) f(g)`
  for all points becomes `F(b⁻¹ g⁻¹) = χ(b) F(g⁻¹)` for `F(x) = f(x⁻¹)`, that is
  `F(h y) = χ(h)⁻¹ F(y)`, and left covariance is tested on all points by
  `mem_leftCovariantSubspace_iff_points`.
- `HomogeneousQuotientFromEmbedding.isRightCharacterCovariant_iso_iff`: for an isomorphism
  `e : H' ≅ H`, right covariance for `e.hom ≫ i` and `characterRestrict e.hom χ` is right
  covariance for `i` and `χ`. Points of `H'` and of `H` correspond through `e`, and
  `characterEval_characterRestrict` evaluates the restricted character.

## The main theorem

`splitBorelInducedNonvanishing` introduces the data and writes `λ` for
`rationalCharacters.equivCharacterLattice p.torus (characterRestrict t χ)`.

1. **Identifying `B'` with the negative Borel subgroup.** By
   `parabolic_eq_of_neg_simpleRoots`, `i` represents the dynamic parabolic that
   `p.negativeBorelHom` represents. `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives
   an isomorphism `e : p.negativeBorel ≅ B'` with `e.hom ≫ i = p.negativeBorelHom`. Since `i` is
   a monomorphism (`SubgroupFunctor.IsRepresentedBy.hom_ext`) and
   `p.torusToNegativeBorel ≫ p.negativeBorelHom = p.inclusion = t ≫ i`, also
   `p.torusToNegativeBorel ≫ e.hom = t`.
2. **Identifying the character.** Every character of the negative Borel subgroup is the extension
   of its restriction to the torus (`SplitPinning.eq_borelCharacter`). Applied to
   `characterRestrict e.hom χ`, whose restriction along `p.torusToNegativeBorel` is
   `characterRestrict t χ` (`characterRestrict_comp` and step 1), this gives
   `characterRestrict e.hom χ = p.borelCharacter λ`.
3. **The covariance condition in coordinates.** Combining the two auxiliary covariance lemmas with
   steps 1 and 2: `IsRightCharacterCovariant i (−χ) f` holds exactly when `coordinateEquiv G f`
   lies in `leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate λ)`.
4. **Nonzero `E(λ)` implies dominance.** Let `f ≠ 0` be right covariant and `F = coordinateEquiv G f`,
   which is nonzero and left covariant by step 3. Its finite regular span
   `Chevalley.affineCovariantSocle G F` (module `Reductive.CovariantSocle`) is a nonzero,
   finite-dimensional subspace stable under right translations
   (`rightAct_mem_affineCovariantSocle`) and contained in the left covariant subspace
   (`affineCovariantSocle_le_leftCovariantSubspace`). On a basis of it, the Library theorem
   `Chevalley.affineRegularRepresentation_exists_normalized_fixedVector` (module
   `Reductive.CovariantUnipotentFixedLine`), applied with the unipotent group `p.positiveUnipotent`
   and the big-cell coordinate `p.cellCoordinate` of `p.exists_factors_of_isUnit_cellCoordinate`,
   gives a vector fixed by the positive unipotent subgroup whose coordinate has value one at the
   identity. That coordinate realizes `λ`: it is left covariant because the whole span is, and right
   invariant by `affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector`. By
   `SplitPinning.IsRealizedBy.isHighestWeight_affineCovariantSocleRepresentation` (module
   `Rational.DominantHighestWeightProof`) its covariant socle representation has highest weight
   `λ`, and a highest weight is dominant (`SplitPinning.IsHighestWeight.isDominantWeight`, module
   `Rational.HighestWeightIntertwiners`).
5. **Dominance implies nonzero `E(λ)`.** For dominant `λ`,
   `SplitPinning.isRealizedWeight_of_isDominantWeight'` (module
   `Rational.SplitHighestWeightClassificationProof`, valid over every field) gives a coordinate
   `F` realizing `λ`. The global function `f = (coordinateEquiv G).symm F` is nonzero, because
   `F` has value one at the identity, and it is right covariant for `−χ` by step 3, since `F` is
   left covariant for `p.borelCharacterCoordinate λ`.
