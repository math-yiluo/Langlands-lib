# Regular families of points of an affine group scheme

Module `Langlands.Global.LocalModularCharacter.RegularFamily`.

This module treats a family of points of a group scheme, indexed by a parameter set, as a single
point with coefficients in an algebra of functions. Products, inverses and constant families of
such families therefore stay in the same class. This avoids explicit Hopf-algebra formulas for
the group law. The main use is the algebra of functions that are strictly differentiable at a
point. It gives the differentiability of the chart expressions for the group law and for
conjugation, which are needed to compare the modular character with the adjoint representation.

Throughout, `F` is a field in universe `u`, `G` is a group scheme over `Spec F` whose underlying
scheme is affine, `K` is a commutative `F`-algebra, `T` is a type, and `𝒮` is an `F`-subalgebra
of the algebra of functions `T → K`. Points are `Lie.AffinePoints G K`, the relative points of
`G` with coefficients in `K`. Regular functions are global sections `a : Γ(G.X.left, ⊤)`, and
`G.affinePointEvaluation` evaluates them at a point.

## Definitions

- `strictDiffSubalgebra F K t₀`: for a nontrivially normed field `K` that is an `F`-algebra and a
  normed `K`-space `T`, the `F`-subalgebra of functions `T → K` that are strictly differentiable
  at `t₀` (`HasStrictFDerivAt` for some continuous linear map). It is closed under sums and
  products by the sum and product rules, and contains the constants.
- `familyEval 𝒮 t : 𝒮 →ₐ[F] K`: evaluation at the parameter `t`.
- `familyValue G f a : T → K`: the function `t ↦ a(f t)` for a family `f : T → G(K)`.
- `IsRegularFamily G 𝒮 f`: every function `familyValue G f a` lies in `𝒮`.
- `familyAlgHom G f`: the `F`-algebra map from the coordinate ring of `G` to `T → K` that sends
  `a` to `t ↦ a(f t)`. It is the product, over `t`, of the algebra maps corresponding to the
  points `f t` under `affineSchemePointEquiv`.
- `liftFamily G 𝒮 f hf : G(𝒮)`: for a regular family, the point of `G` with coefficients in `𝒮`
  whose coordinate algebra map is `familyAlgHom G f`, with values restricted to `𝒮`.

## Results

- `mem_strictDiffSubalgebra`, `const_mem_strictDiffSubalgebra`: membership in
  `strictDiffSubalgebra` unfolded, and the constant functions are members.
- `familyAlgHom_apply`: `familyAlgHom G f a = familyValue G f a`.
- `affinePointEvaluation_liftFamily`: the value of `a` at `liftFamily G 𝒮 f hf` is the element
  `familyValue G f a` of `𝒮`.
- `affinePointEvaluation_family_apply`: for any point `P` of `G(𝒮)`, the value of `a` at `P`,
  evaluated at `t`, is the value of `a` at the specialization of `P` along `familyEval 𝒮 t`.
- `affineMap_familyEval_liftFamily`: the specialization of `liftFamily G 𝒮 f hf` at `t` is `f t`.
- `liftFamily_eq`: a point `P` of `G(𝒮)` whose specialization at every `t` is `f t` equals
  `liftFamily G 𝒮 f hf`.
- `affinePointEvaluation_affineMap`: for an `F`-algebra map `f : A →ₐ[F] B` and a point `x` of
  `G(A)`, the value of `a` at `Lie.affineMap G f x` is `f` applied to the value of `a` at `x`.
- `isRegularFamily_of_specialization`: if a point `P` of `G(𝒮)` specializes at each `t` to
  `f t`, then `f` is regular.
- `IsRegularFamily.mul`, `IsRegularFamily.inv`: the families `t ↦ f t * g t` and
  `t ↦ (f t)⁻¹` are regular when `f` and `g` are.
- `liftFamily_mul`: the lift of the product family `t ↦ f t * g t` is the product of the lifts.
- `isRegularFamily_const`: if `𝒮` contains the constant functions, every constant family is
  regular.
- `IsRegularFamily.comp`: if precomposition with `σ : T' → T` sends `𝒮` into `𝒮'`, then
  `f ∘ σ` is regular for `𝒮'` when `f` is regular for `𝒮`.

## Proofs

Evaluating a regular function commutes with change of coefficients
(`affinePointEvaluation_map`), which gives `affinePointEvaluation_family_apply`.
`affineSchemePointEquiv_evaluation` identifies the algebra map of a point with the evaluation of
regular functions. With it, `liftFamily` evaluates to the expected functions, and its
specializations are the points `f t`, because points of an affine scheme are determined by their
values (`affinePointEvaluation_injective`).

For products, specialization along `familyEval 𝒮 t` is a group homomorphism `G(𝒮) → G(K)`.
So the product of the lifts of `f` and `g` specializes at `t` to `f t * g t`, and
`isRegularFamily_of_specialization` applies. Inverses are handled the same way. `liftFamily_eq`
compares values of regular functions, using `affinePointEvaluation_family_apply`, and
`liftFamily_mul` follows from it and the same specialization computation.
`affinePointEvaluation_affineMap` is `affinePointEvaluation_map` for the morphism
`CommAlgCat.ofHom f`. The constant and
composition statements follow directly from the definitions.

## Provenance

This is an internal step, written for this project, toward the Library statement
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. It cites no
literature statement. It is the functor-of-points description of morphisms from a parameter
space to an affine group scheme, applied to algebras of functions.
