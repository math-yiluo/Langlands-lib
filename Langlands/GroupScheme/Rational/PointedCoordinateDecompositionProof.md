# Split-torus decomposition of actual pointed affine coordinates (proof)

This file proves
`Langlands.GroupScheme.PointedCoordinateWeights.PointedCoordinateDecompositionStatement`
as the theorem `pointedCoordinateDecomposition`, at every universe `u`. The
setting is a field `k`, a split torus `S` over `k`, an affine `V` over `k` and
an actual `PointedAction S V`. The theorem gives both internal direct-sum
decompositions with no added hypothesis:

- the actual coordinate algebra `Coord V` is the internal direct sum of the
  all-algebra eigenspaces `weightSpace a χ`;
- the fixed-point augmentation ideal `augmentation a` is the internal direct sum
  of `augmentationWeightSpace a χ`.

Neither a group law on `V` nor any reducedness, finiteness or characteristic
hypothesis is used.

The mathematics is the standard fact that a split-torus action on an affine
scheme is a grading of its coordinate ring by the character lattice. The
statement's Markdown cites the use of this fact in Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), §3.3, printed pp.107–108
(PDF pp.133–134), registered source `conrad-gabber-prasad-2015-pseudo-reductive`.
The Lean proof does not follow that text. It takes the Library's
coaction/comodule route for diagonalizable character functors and checks every
step against the actual action and the all-algebra eigencondition. The new
argument is this identification. Each eigenspace is the degree piece of the
coaction, and the augmentation ideal is preserved by the coefficient maps.

## Reduction to the standard torus (section `TorusPoints`)

`IsSplitTorus S.toGrp` provides a finite index type `I` and an isomorphism
`e : S.toGrp ≅ splitTorus (Spec k) I`. All constructions below are made for a
fixed `e`. The final theorem obtains `e` from the hypothesis and gives `I` a
`Fintype` instance via `Fintype.ofFinite`.

- `torusPoint e t` is the actual `A`-point of `S` built from a homomorphism
  `t : Multiplicative (I → ℤ) →* Aˣ`. It sends the standard basis vectors to
  the coordinates of a `splitTorus` point via
  `splitTorus.algebraPointsEquiv` and then composes with `e.inv`. The lemmas
  `torusPoint_one`, `torusPoint_mul` and `torusPoint_map` show that this map
  respects the unit, the products and changes of algebra.
- `pointCharacter e s` is the inverse construction, using
  `splitTorus.exponentValue` of the coordinates of `s ≫ e.hom`.
  `torusPoint_pointCharacter` proves `torusPoint e (pointCharacter e s) = s`;
  its proof uses `exponentValue_single`.
- `characterEquiv e : (I → ℤ) ≃+ characterLattice S` composes the inverse of
  `splitTorus.characterLatticeEquiv` with `characterLattice.comapIso e`.
  `characterValue_torusPoint` and `characterValue_eq_pointCharacter` show that
  the actual character `characterEquiv e m` takes the value
  `pointCharacter e s (ofAdd m)` at `s`. The helper `exponentValue_hom` shows
  that a homomorphism on `Multiplicative ℤ^I` equals the exponent evaluation at
  its values on basis vectors.

## The coaction of the actual action

- `characterAction e a` is a `CharacterAction.Action` (from
  `Torus/CharacterActionGrading`) on `Coord V` with `M = I → ℤ`. On a
  coordinate point `x : Coord V ⟶ C` it applies the actual action
  `a.act (torusPoint e t)` and transports the point with `pointCoordinates`.
  The `one`, `mul` and `naturality` axioms follow from the torus-point lemmas,
  the action laws of `PointedAction`, and naturality of `pointCoordinates` and
  of the actual action.
- `coaction e a` is the Library's `CharacterAction.coaction` of this action.
  `pointCoordinates_act_eq` recovers every actual action
  `pointCoordinates (a.act s v)` by evaluating the coaction at `v` and
  `pointCharacter e s` (Library lemma `act_eq_coaction_evaluate`).

## Coordinate decomposition

- `coaction_coeff_mem`: the `m`-th coaction coefficient of any `z` satisfies the
  all-algebra eigencondition for `characterEquiv e m`. Evaluate the
  coaction as above, use the Library's homogeneity of coefficients
  (`coaction_coefficient_homogeneous`) and `evaluate_single`, then identify the
  character value by `characterValue_eq_pointCharacter`.
- `coaction_of_mem`: if `z ∈ weightSpace a (characterEquiv e m)`, then its
  coaction is the monomial `single m z`. Apply the eigencondition over the
  algebra `B[I → ℤ]` at the universal exponent character (through
  `torusPoint`) and the constant point.
- `coaction_sum`: the coaction coefficients sum to `z`. This is the Library
  counit identity `coaction_counit`, made explicit by `evaluate_one_apply`.
- `coefficients e a : Coord V →ₗ[k] (characterLattice S →₀ Coord V)` reads off
  the coaction coefficients and reindexes them along `characterEquiv e`.
  `coefficients_apply`, `coefficients_mem`, `coefficients_of_mem` and
  `coefficients_sum` restate the three facts above for it.
- `isInternal_weightSpace` applies the Library criterion
  `Langlands.LinearAlgebra.isInternal_of_finsupp`. A linear map into
  finitely supported families whose components lie in the pieces, which is
  diagonal on each piece and sums back to the identity, shows that the pieces
  form an internal direct sum.

## Augmentation decomposition

- `coordinateOrigin_coaction_coeff`: evaluating a coaction coefficient at the
  fixed rational point gives the `m`-th coefficient of the monomial
  `single 0 (coordinateOrigin a z)`. Apply the Library lemma `act_universal` with
  `C = k` and the origin point. The origin is fixed by the actual action
  (`PointedAction.act_origin`), so the left side is the constant point
  (`pointCoordinates_origin`). `coefficientMap_coeff` then compares
  coefficients.
- `coefficients_mem_augmentation`: hence all coefficients of an element of the
  augmentation ideal lie in the augmentation ideal.
- `augmentationCoefficients e a` restricts `coefficients` to
  `augmentation a →ₗ[k] (characterLattice S →₀ augmentation a)` using
  `Finsupp.onFinset`. `support_augmentationCoefficients_subset` compares its
  support with that of `coefficients`.
- `isInternal_augmentationWeightSpace` applies `isInternal_of_finsupp` again.
  Membership comes from `coefficients_mem`, since `augmentationWeightSpace a χ`
  is the preimage of `weightSpace a χ` in the augmentation ideal. Diagonality
  comes from `coefficients_of_mem`. The sum identity comes from
  `Finsupp.sum_of_support_subset` and `coefficients_sum`.

## Final theorem

`pointedCoordinateDecomposition` introduces `k`, `S`, the split-torus
hypothesis, `V` and `a`, extracts `I` and `e`, and returns
`⟨isInternal_weightSpace e a, isInternal_augmentationWeightSpace e a⟩`. The
statement uses `open Classical` for the decidable equality on
`characterLattice S`. The two `isInternal` lemmas hold for any instance, so
the classical one is used. The only axioms are `propext`, `Classical.choice`
and `Quot.sound`.

## Interface for reuse

Downstream work can use the theorem alone or the explicit interface for a
fixed `e`: `characterEquiv`, `coaction`, `coefficients`, `coefficients_mem`,
`coefficients_of_mem`, `coefficients_sum` and `augmentationCoefficients`. This
file proves no compatibility of these maps with equivariant pullbacks.

The module also imports [PointedCoordinateCoaction](PointedCoordinateCoaction.md),
which retains the independently accepted universal-point coefficient construction,
action transport along an isomorphism, and `isInternal_of_iso_splitTorus` assembly.
Both constructions establish the same published target; its theorem is declared
once here.
