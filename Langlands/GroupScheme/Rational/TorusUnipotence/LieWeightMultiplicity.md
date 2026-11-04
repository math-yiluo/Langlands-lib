# Lie weight multiplicities from polynomial eigen-coordinates

Let `H` be an affine group over a field `k` (`[IsAffineHom H.X.hom]`) with an action
`b : AutomorphicAction S.toGrp H` of a commutative group `S`. Suppose the coordinate algebra
`O(H) = CharacterUnits.Coord H` is a polynomial algebra on functions `t j` (`j : Fin d`), where
`t j` is an `S`-eigenfunction of weight `w j` vanishing at the identity. This module proves that
for a split torus `S`, the `χ`-weight space of the induced action on the Lie algebra of `H` has
dimension equal to the number of indices `j` with `w j = χ`.

This is a step of the proof of the Library proposition
`Langlands.GroupScheme.PositiveTorusTriangularCoordinatesStatement`. The polynomial
eigen-coordinates come from `exists_positiveWeight_coordinates` in
`TorusUnipotence/PositiveWeightCoordinates`. This module does not import that module and does
not use positivity of the weights.

Notation: the Lie algebra is `Additive (lieKernel H k)`, the kernel of reduction
`H(k[ε]) → H(k)` written additively. `Lie.kernelDerivationEquiv H x` is the `k`-derivation
`D_x : O(H) → B` at the identity attached to a kernel point `x` over `B[ε]`, characterised by
`x(f) = ε(f) + ε·D_x(f)` (Library `Lie.kernelDerivationEquiv_apply`). `Lie.pointCoordinates H x`
is the algebra map `O(H) → B` of a `B`-point `x`, and `coordCounit H` is evaluation at the
identity. `CoordinateWeights.weightSpace b χ` is the space of `χ`-eigenfunctions in `O(H)`:
`f(b.act s g) = χ(s) f(g)` for all algebras `A` and all `A`-points `s`, `g`.
`RelativeRoot.actionWeightSpace b χ` is the `k`-span of the `χ`-eigenvectors of the action on
the Lie algebra (Library `RelativeRoot.actionEigenvectors`). A tangent vector `X` is a
`χ`-eigenvector if, for every algebra `B` and `B`-point `s` of `S`, the action of the constant
dual-number point `s` sends the base change of `X` to its `ε`-scaling by `χ(s)`.

All declarations are in namespace `Langlands.GroupScheme.TorusUnipotence`.

## Main theorem

`finrank_actionWeightSpace`: assume `[IsAffineHom H.X.hom]`, `[LocallyOfFiniteType H.X.hom]`,
`hS : IsSplitTorus S.toGrp`, `b : AutomorphicAction S.toGrp H`, `t : Fin d → O(H)`,
`w : Fin d → characterLattice S`, and

- `ht`: `MvPolynomial.aeval t : MvPolynomial (Fin d) k →ₐ[k] O(H)` is bijective;
- `htw`: `t j ∈ CoordinateWeights.weightSpace b (w j)` for every `j`;
- `hε`: `coordCounit H (t j) = 0` for every `j`.

Then for every `χ : characterLattice S`,
`Module.finrank k (RelativeRoot.actionWeightSpace b χ) = Nat.card {j // w j = χ}`.

## Supporting declarations

- `eq_of_le_of_iSup_eq_top`: in a modular complete lattice, if `U i ≤ W i` for all `i`,
  `⨆ i, U i = ⊤`, and the family `W` is independent (`iSupIndep W`), then `U i = W i` for all `i`.
- `pointCoordinates_ext`: if `aeval t` is surjective, two `B`-points of `H` (for a `k`-algebra
  `B`) with the same values on every `t j` are equal.
- `pointCoordinates_kernel_of_counit`: for a kernel point `x` over `B[ε]` and `f` with
  `coordCounit H f = 0`, `pointCoordinates H x.val f = TrivSqZeroExt.inr (D_x f)`, that is,
  `x(f) = ε·D_x(f)`.
- `kernelDerivationEquiv_scale_apply`: `D` of the `ε`-scaling of `x` by `c` is `c * D_x`,
  evaluated at `f`.
- `tangentCoordinates t` (a definition): the `k`-linear map from the Lie algebra to `Fin d → k`
  sending `X` to `(D_X(t j))_j`.
- `tangentCoordinates_injective`: if `aeval t` is surjective and every `t j` vanishes at the
  identity, then `tangentCoordinates t` is injective.
- `tangentCoordinates_surjective`: if `aeval t` is bijective and every `t j` vanishes at the
  identity, then `tangentCoordinates t` is surjective.
- `tangentCoordinatesEquiv ht hε` (a definition): the resulting linear equivalence between the
  Lie algebra and `Fin d → k`.
- `mem_actionWeightSpace_of_tangentCoordinates`: under `htw`, `hε`, and surjectivity of
  `aeval t`, a tangent vector `X` with `D_X(t j) = 0` whenever `w j ≠ χ` lies in
  `RelativeRoot.actionWeightSpace b χ`. Here `S` need not be a split torus.

## Proofs

`eq_of_le_of_iSup_eq_top`. Write `V = ⨆_{j ≠ i} U j`. Then `W i = (U i ⊔ V) ⊓ W i`, which
equals `U i ⊔ (V ⊓ W i)` by the modular law since `U i ≤ W i`. Moreover
`V ⊓ W i ≤ (⨆_{j ≠ i} W j) ⊓ W i = ⊥` by independence.

`pointCoordinates_ext`. Points are determined by their algebra maps
(`Lie.pointCoordinates` is an equivalence). Two algebra maps agreeing on the generators `t j`
agree on every `aeval t p`, by induction on `p`.

`pointCoordinates_kernel_of_counit`. The first component of `x(f)` is the identity value
`ε(f) = 0` (Library `Lie.pointCoordinates_kernel`). The second component is `D_x(f)` by
definition.

`tangentCoordinates`. Additivity and `k`-linearity follow from the Library facts that `D` turns
the kernel group law into addition (`Lie.kernelDerivationEquiv_mul`) and `ε`-scaling into scalar
multiplication (`Lie.kernelDerivationEquiv_scale`).

`tangentCoordinates_injective`. If `D_X(t j) = D_Y(t j)` for all `j`, then `X` and `Y` agree on
every `t j` by `pointCoordinates_kernel_of_counit`, hence are equal by `pointCoordinates_ext`.

`tangentCoordinates_surjective`. Given `v : Fin d → k`, let `φ : O(H) → k[ε]` be the algebra
map with `φ(t j) = ε·v j`. It exists because `O(H)` is the polynomial algebra on the `t j`
(`AlgEquiv.ofBijective (aeval t) ht`). Let `x` be the `k[ε]`-point with coordinates `φ`. Its
reduction agrees with the identity on every `t j`, since both values are `0` (the identity
value is `ε(t j) = 0`). So `x` lies in the kernel by `pointCoordinates_ext`, and `D_x(t j) = v j`.

`mem_actionWeightSpace_of_tangentCoordinates`. It suffices to show that `X` is an eigenvector
(`RelativeRoot.mem_actionWeightSpace_iff`). Fix `B`, a `B`-point `s` of `S`, and let `Y` be the
base change of `X` to `B[ε]`. By `pointCoordinates_ext` it suffices to compare both sides on each
`t j`. The left side is `b.act s Y` evaluated at `t j`. It equals `w j(s) · Y(t j)` because
`t j` is a `w j`-eigenfunction and the constant point `s` has character value `w j(s)`
(`CoordinateWeights.characterValue_affineMap`). By `pointCoordinates_kernel_of_counit` and
`Lie.kernelDerivationEquiv_naturality`, this is `w j(s) · ε·D_X(t j)`. The right side, the
`ε`-scaling of `Y` by `χ(s)`, gives `ε·χ(s)·D_X(t j)` by `kernelDerivationEquiv_scale_apply`.
If `w j = χ` the two agree, using `inl a * inr m = inr (a • m)`. Otherwise
`D_X(t j) = 0` by hypothesis, and both sides vanish.

`finrank_actionWeightSpace`. Transport the standard basis of `Fin d → k` through
`tangentCoordinatesEquiv` to a basis `B` of the Lie algebra with `D_{B j}(t i) = δ_{ij}`. For a
character `ψ`, let `U ψ` be the span of the `B j` with `w j = ψ`. Then:

- `U ψ ≤ actionWeightSpace b ψ`: each such `B j` satisfies the hypothesis of
  `mem_actionWeightSpace_of_tangentCoordinates`.
- `⨆ ψ, U ψ = ⊤`: every basis vector `B j` lies in `U (w j)`.
- The weight spaces are independent (Library `RelativeRoot.iSupIndep_actionWeightSpace`, which
  uses `hS`).

Submodules form a modular lattice, so `eq_of_le_of_iSup_eq_top` gives
`U χ = actionWeightSpace b χ`. The vectors `B j` with `w j = χ` are linearly independent, so
`finrank (U χ) = #{j | w j = χ}` (`finrank_span_eq_card`).

## Provenance

This is an internal supporting module for the proof of
`PositiveTorusTriangularCoordinatesStatement` (part of the proof of
`NormOneRationalQuotientFiniteVolumeStatement`, Getz–Hahn 2024 Theorem 2.6.3). The statement is
the standard fact that the tangent space at the identity of `Spec k[t_1, …, t_d]` has the dual
basis of the differentials `dt_j`, so that the torus weights on the Lie algebra are those of the
coordinates, with multiplicity. The proof is written for this Library's definitions of the Lie
algebra (`lieKernel`) and of action weight spaces; no literature proof is followed.
