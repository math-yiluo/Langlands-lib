# Character gradings of corepresented groups with split-torus actions

This module sets up the algebra of a split-torus action on a corepresented group
functor. All declarations are in namespace `Langlands.GroupScheme.Corepresented`.
Throughout, `R : CommRingCat.{u}`, `F : CommAlgCat R ⥤ GrpCat` is a group-valued
functor on commutative `R`-algebras, and `e : (F ⋙ forget GrpCat).CorepresentableBy B`
says that `B` corepresents its underlying set functor. `I` is a finite type with
decidable equality, and the exponent lattice is `I → ℤ`.

## Monomials and torus actions

- `monomialUnit I A m` is the unit `X^m` of the group algebra
  `AddMonoidAlgebra A (I → ℤ)`, and `universalUnits I A i = X^{δᵢ}` is the
  family of coordinate monomials. `exponentValue_universalUnits` says that the
  character `m` of the split torus takes the value `X^m` at this family
  (`splitTorus.exponentValue` from `Langlands.GroupScheme.Torus.UniversalPoint`).
- `TorusAction F I` is an action of families `t : I → Aˣ` on `F.obj A`, for every
  `R`-algebra `A`: `act 1 = id`, `act (t * t') = act t ∘ act t'`, each `act t` is
  multiplicative, and the action is natural in `A` (units are pushed forward along
  the algebra map). This is the action of the split torus `𝔾ₘ^I` on `F` written on
  `A`-points.

## Coordinates

- `coord e x : B →ₐ[R] A` is the classifying algebra map of a point `x : F.obj A`,
  and `ofCoord e f` is the point classified by `f`. They are inverse
  (`coord_ofCoord`, `ofCoord_coord`, `coord_injective`) and natural:
  `coord_map` gives `coord e (F.map g x) = g ∘ coord e x`.
- `AffineLinearEmbedding.counit e : B →ₐ[R] R` is the coordinate map of the identity point over `R`, and
  `coord_one` shows that the identity point over any `A` has coordinates
  `algebraMap R A ∘ AffineLinearEmbedding.counit e`.

## The coaction

Fix `σ : TorusAction F I`.

- `laurent I A` is the `R`-algebra `A[I → ℤ] = AddMonoidAlgebra A (I → ℤ)`, and
  `constHom I A : A ⟶ laurent I A` is the inclusion of constants.
- `evalHom I f t : B[I → ℤ] →ₐ[R] A` applies `f` to coefficients and evaluates
  `X^m` at the value of the character `m` at `t`; `evalHom_single` and
  `evalHom_apply` compute it.
- `hat σ : F.obj A →* F.obj (laurent I A)` sends `x` to the point `x` over the
  constants twisted by the universal family `universalUnits I A`. It is a group
  homomorphism because each `act t` is.
- `univ e : F.obj B` is the universal point and `rho e σ : B →ₐ[R] B[I → ℤ]` is the
  coordinate map of `hat σ (univ e)`. This is the coaction of the character
  lattice on `B`, i.e. the `X(𝔾ₘ^I)`-grading of `B`.

The main formulas:

- `coord_act`: `coord e (σ.act t x) = evalHom I (coord e x) t ∘ rho e σ`. The proof
  writes `σ.act t x` as the image of `hat σ (univ e)` under the algebra map
  `B[I → ℤ] → A` sending `b X^m` to `coord e x b · m(t)`, using naturality of the
  action and of `e`.
- `coord_hat`: the coordinates of `hat σ x` are `rho e σ` followed by applying
  `coord e x` to coefficients (`evalHom_const` identifies the evaluation at the
  universal units with coefficientwise mapping).
- `comp e σ m : B →ₗ[R] B` is the weight-`m` component, the `m`-th coefficient of
  `rho e σ`. `coord_hat_coeff` gives `(coord e (hat σ x) f)_m = coord e x (comp e σ m f)`.
- `sum_comp` and `sum_support_comp`: every `f` is the sum of its weight components
  (from `σ.act_one`).
- `counit_comp`: the counit of `comp e σ m f` is `AffineLinearEmbedding.counit e f` for `m = 0` and `0`
  otherwise (from `hat σ 1 = 1` and `coord_one`).
- `coord_hat_hat`: twisting twice by the universal units is the diagonal twist,
  using `σ.act_mul` and naturality. As a consequence `comp_comp` shows that the
  components are idempotent and orthogonal:
  `comp e σ n (comp e σ m f) = if n = m then comp e σ m f else 0`.
- `comp_mul`: the components of a product are given by the multiplication of
  `B[I → ℤ]`, since `rho e σ` is an algebra map.
- `exponentValue_mul` and `exponentValue_map` are the multiplicativity and the
  naturality of character values used in these proofs.

## Homogeneous elements and the grading

- `IsHomogeneous e σ m f` means `rho e σ f = f X^m`. `isHomogeneous_iff`
  characterizes it by the components, `isHomogeneous_comp` shows that components
  are homogeneous, and `IsHomogeneous.comp_eq`, `IsHomogeneous.comp_self`,
  `IsHomogeneous.mul` (weights add), `IsHomogeneous.add`, `IsHomogeneous.smul`,
  `isHomogeneous_zero`, `isHomogeneous_algebraMap` (scalars have weight `0`) and
  `IsHomogeneous.counit_eq_zero` (a homogeneous element of nonzero weight has zero
  counit) are the closure properties.
- `coord_hat_of_isHomogeneous` and `coord_act_of_isHomogeneous`: on a homogeneous
  function of weight `m`, the twist multiplies by `X^m` and the action of `t`
  multiplies the coordinate by the value of `m` at `t`.
- `homogeneousSubmodule e σ m` is the `R`-submodule of homogeneous elements of
  weight `m`.
- Regrading. For an additive monoid `ι` and an injective additive map
  `φ : ι →+ (I → ℤ)`, the submodules `homogeneousSubmodule e σ (φ i)` form a graded
  monoid (`gradedMonoid_homogeneousSubmodule`). If every nonzero component has its
  weight in the range of `φ` (`hsupp`), they are an internal direct sum
  (`isInternal_homogeneousSubmodule`; `comp_coeAddMonoidHom` recovers the summands
  from the components), and `gradedAlgebra hφ hsupp` is the resulting
  `GradedAlgebra` structure indexed by `ι`. This is used later with `ι = ℕ` and
  `φ n = n • a` for a nonzero character `a`.
- `weightGradedAlgebra e σ` is the `GradedAlgebra` structure on `B` indexed by all
  of `I → ℤ` (`φ = id`).

## Provenance

This is internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement`
(task 023326af), following the route of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, 2nd ed., Lemma 3.3.8 and its proof, which works with the grading of the
coordinate ring of a group with a torus action by the character lattice. The
module formalizes the standard dictionary between actions of a split torus
`𝔾ₘ^I` on an affine group and `ℤ^I`-gradings of its coordinate ring, in the
corepresented-functor language of this Library; it does not formalize a specific
numbered statement of a source.

The algebra-point constructor `ofCoord` reuses `AffineLinearEmbedding.pt`;
the augmentation is the existing `AffineLinearEmbedding.counit`. The
`monomialUnit` abbreviation reuses `splitTorus.exponentUnit` over the
coefficient ring. These identifications preserve the coordinate conventions
and keep the distinct ring-category counit in `Dynamic.Representability`.
