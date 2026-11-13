# The special unitary group scheme of an arbitrary nonsingular Hermitian matrix

Author: Worker 5375.

This internal construction works over fields `k` and `L` in one arbitrary universe `u`,
with a separable quadratic extension `L/k` (`Algebra.IsQuadraticExtension k L` and
`Algebra.IsSeparable k L`). No characteristic is excluded. The matrix index `Idx` is any
finite type with decidable equality in `Type`. This matches the index universe of
`SpecialLinear.WeilRoot.groupScheme`. `H : Form (fieldInvolution k L) Idx` is an
arbitrary nonsingular Hermitian Gram matrix, as in the published `HermitianMatrix`
interface. The module generalizes the published `SU3GroupScheme` construction, which
fixes `Idx = Fin 3` and one particular Gram matrix, to every such `H`. It gives the
published presentation interface `HermitianMatrix.SchemeModel.Presentation` a concrete
group scheme for every `H`.

Write `Mᴴ = adjoint c M`, the conjugate transpose for a ring involution `c`.

## Matrix algebra (namespace `Langlands.GroupScheme.HermitianMatrix`)

For commutative rings `A`, `B` with involutions `c`, `d`:

- `det_adjoint`: `det (Mᴴ) = c̄ (det M)`.
- `gram_mul_gram_inv` and `gram_inv_mul_gram`: the Gram matrix of a form times its inverse
  in `GL` is `1`, on either side.
- `adjoint_mul_adjoint_inv` and `adjoint_inv_mul_adjoint`: for `g ∈ SL`,
  `gᴴ (g⁻¹)ᴴ = 1 = (g⁻¹)ᴴ gᴴ`.
- `gramTwist H : SL_Idx(A) →* SL_Idx(A)` sends `g` to `H⁻¹ (g⁻¹)ᴴ H`, where `H` here
  denotes the Gram matrix. Its determinant is `1` because `det (g⁻¹)ᴴ = c̄ 1 = 1`, and it
  is multiplicative. `coe_gramTwist` states the matrix formula.
- `gramTwist_eq_self_iff`: `gramTwist H g = g` holds exactly when `gᴴ H g = H`.
- `gramTwist_map`: for a ring map `f : A →+* B` with `f ∘ c̄ = d̄ ∘ f`, applying `f`
  entrywise commutes with the twist, using the mapped form `H.map f hf`.

## The group scheme (namespace `HermitianMatrix.GroupModel`)

- `ambient k L Idx` is the published Weil restriction
  `SpecialLinear.WeilRoot.groupScheme (n := Idx) k L` of `SL_Idx` from `L` to `k`. Its
  points over a test scheme `T` are identified with `SL_Idx(L ⊗_k Γ(T))` by the
  published `tensorMatrixEquiv k L T`.
- `twistPoints k L H T` transports `gramTwist (SchemeModel.tensorForm k L H T)` along
  `tensorMatrixEquiv`, where `tensorForm` is the published scalar extension of `H` to
  `L ⊗_k Γ(T)` with involution `coefficientInvolution`.
  `tensorMatrixEquiv_twistPoints` states this.
- `tensorForm_map` states that restricting the extended form along a test morphism `a`
  gives the extended form on the new test scheme. `twistPoints_naturality` follows from
  it and `gramTwist_map`.
- `twist` is the group-scheme endomorphism of `ambient` built from these natural
  homomorphisms by the published `homOfPoints`. `tensorMatrixEquiv_twist` gives its
  effect on points.
- `fixedFunctor` is the published `endomorphismFixedSubgroup twist`.
  `mem_fixedFunctor_iff` shows that a point is fixed exactly when its tensor matrix
  preserves the extended form (`Preserves`).
- `groupScheme k L H` is the representing group scheme of `fixedFunctor`, with underlying
  scheme the equalizer of `twist` and the identity. It uses the published factorization
  criterion `mem_endomorphismFixedSubgroup_iff_factors`. `inclusion` is the equalizer
  inclusion into `ambient`, and `inclusion_hom` states this.
- Instances: `inclusion` is a closed immersion, because `ambient` is separated. Hence
  `groupScheme k L H` is affine and its structure morphism is affine.

## All-test points

- `fixedPointsEquiv k L H T` is the multiplicative bijection from points of
  `groupScheme k L H` over `T` to the fixed subgroup functor over `T`. It is induced by
  composition with `inclusion`.
- `tensorPoints_preserves` and `tensorPoints_det` unpack membership in the published
  `SchemeModel.tensorPoints k L H T`, the determinant-one isometries of the extended form
  in `GL_Idx(L ⊗_k Γ(T))`. `tensorPointsToSL` regards such a point as a matrix of
  determinant one.
- `fixedTensorEquiv k L H T` is the group isomorphism from the fixed subgroup functor
  over `T` onto `SchemeModel.tensorPoints k L H T`. It takes the tensor matrix and
  includes `SL` into `GL`.
- `pointsEquiv k L H T` is the composite group isomorphism from the points of
  `groupScheme k L H` over `T` to `SchemeModel.tensorPoints k L H T`.
  - `pointsEquiv_val` states that its underlying matrix is the tensor matrix of
    `x ≫ inclusion`.
  - `pointsEquiv_naturality` states that for every test morphism `a : T' ⟶ T`, the matrix
    of `a ≫ x` is the matrix of `x` with `tensorMap k L a` applied to every entry.
- `presentation k L H : SchemeModel.Presentation k L H (groupScheme k L H)` packages
  `pointsEquiv` and its naturality.

## Provenance and scope

The provenance is internal. The special unitary group of a nonsingular Hermitian form is
the fixed-point group scheme of the inverse-adjoint involution on the Weil restriction of
`SL` from `L` to `k`. This module implements that construction with the same published
tools as `SU3GroupScheme`:
- the Weil-restriction point model;
- the endomorphism-fixed subgroup functor;
- its representability by a scheme equalizer.

The new ingredient is the Gram-twist algebra above for an arbitrary Gram matrix. The
module asserts representability, affineness and the all-test matrix presentation. It
makes no claim about smoothness, reductivity, simple connectedness or Tits indices.
It supplies the group scheme for the descent step of Task 6209
(`OuterTypeAHermitianPresentationStatement`).
