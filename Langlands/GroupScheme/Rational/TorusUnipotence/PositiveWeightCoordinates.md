# Torus-eigen polynomial coordinates on groups with positive weights

This module proves two facts about a smooth affine group `H` of finite type over a field `k`
with an action `b : AutomorphicAction S.toGrp H` of a split torus `S`, when every augmentation
weight of the action pairs positively with a fixed cocharacter `ν`.

1. The coordinate algebra `O(H) = CharacterUnits.Coord H` is a polynomial algebra on
   `S`-eigenfunctions `t j` vanishing at the identity, with weights `w j` such that
   `⟨w j, ν⟩ > 0` and `⟨w j, ν⟩` is nondecreasing in `j`.
2. In such coordinates the group law is triangular:
   `(x y)_j = x_j + y_j + P_j(x_i, y_i : i < j)`.

These are the algebraic steps of the proof of the Library proposition
`Langlands.GroupScheme.PositiveTorusTriangularCoordinatesStatement`. There `H` is the standard
unipotent subgroup `N = U(ν)` with the conjugation action of the maximal split torus `T`. The
remaining steps (weight multiplicities in the Lie algebra, and identifying `N` and its weights)
are separate modules.

Notation: `CoordinateWeights.weightSpace b χ` is the space of `χ`-eigenfunctions in `O(H)`.
Being a `χ`-eigenfunction means `f(b.act s g) = χ(s) f(g)` for all algebras `A` and all
`A`-points `s, g` (`CoordinateWeights.IsEigenfunction`). `CoordinateWeights.support b` is the
set of weights of nonzero eigenfunctions in the augmentation ideal. `coordCounit H` is
evaluation at the identity, `coordComul H` is the comultiplication,
`latticePairing S χ ν` is the pairing `⟨χ, ν⟩ ∈ ℤ`, and `Lie.pointCoordinates H x` is the
algebra map `O(H) → B` of a `B`-point `x`.

All declarations are in namespace `Langlands.GroupScheme.TorusUnipotence`.

## Main theorems

`exists_positiveWeight_coordinates`: assume `[IsAffineHom H.X.hom]`,
`[LocallyOfFiniteType H.X.hom]`, `[Smooth H.X.hom]`, `hS : IsSplitTorus S.toGrp`, a cocharacter
`ν : cocharacterLattice S`, and
`hsupp : ∀ χ ∈ CoordinateWeights.support b, 0 < latticePairing S χ ν`. Then there are `d : ℕ`,
`w : Fin d → characterLattice S` and `t : Fin d → O(H)` such that

- `MvPolynomial.aeval t : MvPolynomial (Fin d) k →ₐ[k] O(H)` is bijective;
- `t j ∈ CoordinateWeights.weightSpace b (w j)` for every `j`;
- `coordCounit H (t j) = 0` for every `j`;
- `0 < latticePairing S (w j) ν` for every `j`;
- `fun j => latticePairing S (w j) ν` is monotone.

`exists_triangular_mul`: assume `[IsAffineHom H.X.hom]`, `hS`, `ν`, and `d`, `w`, `t` as in the
conclusion of the previous theorem (bijectivity of `aeval t`, the eigenfunction property, the
vanishing at the identity, positivity and monotonicity of `⟨w j, ν⟩`). Then there is
`P : Fin d → MvPolynomial (Fin d ⊕ Fin d) k` with

- `∀ j, ∀ v ∈ (P j).vars, Sum.elim id id v < j`: the variables `inl i` (coordinates of `x`)
  and `inr i` (coordinates of `y`) occurring in `P j` all have `i < j`;
- for every `k`-algebra `B : Type u`, all `x y : Lie.AffinePoints H B` and every `j`,
  `pointCoordinates (x * y) (t j) = pointCoordinates x (t j) + pointCoordinates y (t j) +
  aeval (Sum.elim (fun i => pointCoordinates x (t i)) (fun i => pointCoordinates y (t i))) (P j)`.

Smoothness and finiteness are not hypotheses of `exists_triangular_mul`: it only uses the
polynomial eigen-coordinates.

## Supporting declarations

- `aeval_mem_graded_of_isWeightedHomogeneous` (`k` a commutative ring,
  `[SetLike.GradedMonoid 𝒜]` for `𝒜 : Λ → Submodule k C`): if `y j ∈ 𝒜 (w j)` for all `j` and
  `p` is weighted homogeneous of weight `χ` for `w`, then `aeval y p ∈ 𝒜 χ`. The Library lemma
  `aeval_mem_of_isWeightedHomogeneous` (`TruncatedSection`) is the same statement under
  `[GradedAlgebra 𝒜]`, hence the different name.
- `isWeightedHomogeneous_rename`: if `p` is weighted homogeneous of weight `χ` for `w ∘ f`, then
  `rename f p` is weighted homogeneous of weight `χ` for `w`.
- `weightSpace_zero_eq`: if `0 ∉ CoordinateWeights.support b`, then
  `CoordinateWeights.weightSpace b 0 = LinearMap.range (Algebra.linearMap k O(H))`, i.e. the
  invariant functions are the constants.
- `mem_support_of_mem_weightSpace`: for `hS`, `χ ≠ 0`, `f ∈ CoordinateWeights.weightSpace b χ`
  and `f ≠ 0`, one has `χ ∈ CoordinateWeights.support b`.
- `weightGradedAlgebra hS b : GradedAlgebra (CoordinateWeights.weightSpace b)` (a definition,
  using classical decidable equality on `characterLattice S`): the character grading of `O(H)`.
  The decomposition is the one chosen from the Library's internal-direct-sum theorem
  `CoordinateWeights.coordinateWeightDecomposition`. The graded-monoid axioms are
  `one_mem_weightSpace_zero` and `mul_mem_weightSpace`.

## Proofs

`weightSpace_zero_eq`. Constants are invariant by `one_mem_weightSpace_zero`. Conversely, if
`f` is invariant then `f - ε(f)` is an invariant function in the augmentation ideal, and it is
`0` because `0` is not in the support. So `f = ε(f)`.

`exists_positiveWeight_coordinates`. `O(H)` is of finite type
(`Lie.coordinateAlgebraFiniteType`), formally smooth (`formallySmooth_coord`) and nontrivial
(it has the counit to `k`). Give it the grading `weightGradedAlgebra` and the height
`h = ⟨-, ν⟩ : characterLattice S →+ ℤ`. The weight-zero part is `k` by `weightSpace_zero_eq`,
since `0` is not in the support (`⟨0, ν⟩ = 0`). A nonzero eigenfunction of weight `χ ≠ 0` has
`χ` in the support (`mem_support_of_mem_weightSpace`), hence positive height by `hsupp`. The
theorem `WeightGradedFormallySmooth.exists_weight_aeval_bijective` then gives the bijective
`aeval t` on homogeneous `t j` with positive, nondecreasing heights. Each `w j` is nonzero,
since its height is positive, so `coordCounit_eq_zero` gives `ε(t j) = 0`.

`exists_triangular_mul`. Let `e : MvPolynomial (Fin d) k ≃ₐ[k] O(H)` be `aeval t`. Define
`L : O(H) ⊗ O(H) → k[X_{inl i}, X_{inr i}]` as the tensor product of `rename inl ∘ e⁻¹` and
`rename inr ∘ e⁻¹`, and put `Q j := L (Δ (t j))`, where `Δ = coordComul H`.

- Group law: by `pt_comp_comul`, the point `x y` has coordinates `l ∘ Δ`, where `l` is the
  tensor product of the coordinate maps of `x` and `y`. Evaluating at
  `Sum.elim (x_i) (y_i)` turns `L` into `l`. This is checked on pure tensors after checking it
  on `rename inl ∘ e⁻¹` and `rename inr ∘ e⁻¹` by polynomial induction. Hence
  `(x y)_j = aeval (Sum.elim (x_i) (y_i)) (Q j)`.
- Weights: `Δ (t j)` lies in `⨆ α, W_α ⊗ W_{w j - α}` (Library `coordComul_mem_iSup`). Since
  `aeval t` is injective, `e⁻¹` maps `W_α` to weighted homogeneous polynomials of weight `α`
  (`isWeightedHomogeneous_of_aeval_mem`). After renaming and multiplying, `Q j` is weighted
  homogeneous of weight `w j` for the weights `w' v = w (Sum.elim id id v)`.
- Linear terms: take `B = k[X_0, …, X_{d-1}]`, the point `x₀` with coordinate map `e⁻¹`
  (so `(x₀)_i = X_i`), and `y = 1`. The coordinates of `1` are `ε(t i) = 0`. So
  `X_j = aeval (Sum.elim X 0) (Q j)`, and `aeval (Sum.elim X 0)` is Mathlib's
  `killCompl Sum.inl_injective`. By `coeff_killCompl`, the coefficient of `X_{inl i}` in
  `Q j` is `δ_{ij}`. The same argument with `x = 1` and `y = x₀` gives the coefficient of
  `X_{inr i}`.
- Put `P j := Q j - X_{inl j} - X_{inr j}`. The group-law identity follows. If a variable `v`
  occurs in `P j`, take a monomial `m` of `P j` with `m v ≠ 0`. By the linear terms, `m` is not
  a single variable `single u 1`, so `m` is a monomial of `Q j` and has weight `w j`. Lemma
  `height_lt_of_ne_single` (from `WeightGradedFormallySmoothPolynomial`) gives
  `⟨w' v, ν⟩ < ⟨w j, ν⟩`. Monotonicity of the heights then forces `Sum.elim id id v < j`.

## Provenance

This is an internal module, with no single literature source. Its results are standard
ingredients of the structure theory of unipotent groups with a contracting torus action
(compare Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Prop. 2.1.8, and Milne,
*Algebraic Groups*, 2017, §14). The proofs here follow the graded-algebra route described
above. They do not use an exponential map or follow a specific published proof.
