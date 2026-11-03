# Weight projectors of a cocharacter of `GL_n`, and diagonalization over a field

Worker 303. Let `χ : 𝔾_m ⟶ GL_n` be an actual cocharacter of the matrix group
scheme `GeneralLinear.groupScheme n R` over `Spec R`. This module extracts the
weight projectors of `χ`. Over a field, it proves that `χ` is conjugate, by a
base point of `GL_n`, to a diagonal cocharacter `t ↦ diag(t ^ e i)`.

This is the `GL_V` step in Milne's proof that `U(λ)` is unipotent: Milne,
*Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Theorem 13.33 and its proof (printed pp.265–266, PDF pp.281–282), and
Example 14.13 (printed p.283, PDF p.299). Milne uses Theorem 12.12 (printed
pp.234–235) to choose a basis of `V` in which `λ(𝔾_m)` is diagonal. The Lean
route below implements that step directly on the actual group scheme `GL_n`
and its actual points. The downstream use is the solvability theorem in
`Langlands.GroupScheme.Dynamic.UnipotentSolvable`.

## Algebra points of `𝔾_m`

`Gm.algebraPointsEquiv A` is the published identification
`Gm.affinePointsEquiv`, applied to the affine test object
`(algSpec R).obj (op (CommAlgCat.of R A))`. It identifies points of `𝔾_m` over
the `R`-algebra `A` with `Aˣ`.

- `Gm.algebraPointsEquiv_naturality` shows that this identification commutes
  with change of test algebra along `f : A →ₐ[R] B`. The proof combines the
  published `Gm.pointsEquiv_naturality` with naturality of `ΓSpecIso`.
- `Gm.algebraPointsEquiv_symm_naturality` is the same statement for the
  inverse map.

## The matrices `χ(u)`

`cocharacterUnitsHom χ A : Aˣ →* GL n A` sends a unit `u` to the matrix of the
point `χ(u)`. It uses the published `GeneralLinear.affinePointsEquiv`.

- It is a monoid homomorphism because `χ` is a homomorphism of group schemes
  (`MonObj.one_comp`, `MonObj.mul_comp`).
- `cocharacterUnitsHom_naturality`: `χ(f u)` is the image of `χ(u)` under
  `f`, by the published `affinePointsEquiv_naturality`.

## Weight projectors

Let `T` be the Laurent coordinate, as the unit `cocharacterLaurentUnit R` of
`R[T, T⁻¹]`.

- `weightMatrix χ` is the matrix `χ(T)`.
- `weightProjector χ a` is the matrix of `T ^ a`-coefficients of `χ(T)`.
- `cocharacterWeightSupport χ` is the finite set of exponents occurring in
  some entry of `χ(T)`.
- `weightProjector_eq_zero`: the projectors vanish outside that set.
- `weightMatrix_apply`: each entry of `χ(T)` is the Laurent polynomial
  `∑ a, single a (E_a i j)`.

Two identities are proved over every commutative ring `R`.

- `sum_weightProjector`: `∑ a, E_a = 1`. The evaluation
  `cocharacterEvalOne : R[T, T⁻¹] →ₐ[R] R` at `T = 1` sends `T` to the unit
  `1`. By naturality, `χ(1) = 1` is the evaluated matrix `∑ a, E_a`.
- `weightProjector_mul`: `E_p * E_m = if p = m then E_m else 0`. Let
  `cocharacterTranslate` be the map `R[T, T⁻¹] → R[T, T⁻¹][S, S⁻¹]` with
  `T ↦ T S`.
  - On units, the image of `T` is the product of two images of `T`
    (`units_map_cocharacterTranslate`). One is the constant image
    (`singleZeroAlgHom`, the unit `T`). The other is the coefficient extension
    (`mapAlgHom`, the unit `S`).
  - Since `χ` is multiplicative and natural, `χ(T S) = χ(T) χ(S)`.
  - Comparing `S ^ m`-coefficients (`coeff_cocharacterTranslate`) gives
    `E_m T^m = χ(T) E_m` over `R[T, T⁻¹]`.
  - Comparing `T ^ p`-coefficients then gives the orthogonality relation.

## Comparison lemmas

- `affinePointsEquiv_eq_map_pointsEquiv'`: the published comparison of
  affine and global-section coordinates of `GL_n`, written with `ΓSpecIso`.
  It uses `Corepresented.affineSectionsIso_hom_ringHom`.
- `cocharacterUnitsHom_diagonalCocharacter`: for the published
  `diagonalCocharacter n R e`, `χ(u) = diagonalUnits A e u`. This uses the
  published `pointsEquiv_diagonalCocharacter` and `map_diagonalUnits`.
- `universalPoint_eq_algebraPointsEquiv_symm`: the published universal point
  `Gm.universalPoint R` is the algebra point of `T`.
- `eq_of_weightMatrix_eq`: two cocharacters of `GL_n` with the same matrix
  `χ(T)` are equal, by the published `Gm.hom_ext_universalPoint`.
- `baseOfMatrix R g`: the base point of `GL_n` with matrix `g ∈ GL n R`.
  `affinePointsEquiv_constantPoint_baseOfMatrix` proves that its constant
  points over a test algebra `A` have the matrix `g` mapped to `A`.
- `weightMatrix_innerIso`: conjugating `χ` by the inner automorphism of
  `baseOfMatrix R g` conjugates `χ(T)` by `g`. It uses the published
  `comp_innerIso_hom`.
- `cocharacterLaurentUnit_zpow`: the integer powers of the unit `T` are the
  monomials `T m`.

## Diagonalization over a field

`exists_matrix_innerIso_comp_eq_diagonalCocharacter` takes a field `K` and a
cocharacter `ψ` of `GL_n` over `Spec K`. It gives `g ∈ GL n K` and
`e : n → ℤ` with

`ψ ≫ (innerIso (groupScheme n K) (baseOfMatrix K g)).hom = diagonalCocharacter n K e`,

an equality of homomorphisms of group schemes.

The proof runs as follows.

- The weight projectors are complete orthogonal idempotents.
  `Langlands.LinearAlgebra.exists_conj_eq_diagonal_of_orthogonal` gives `P`
  and `e` with `P⁻¹ E_a P` the diagonal indicator matrix of `{i | e i = a}`.
- Every label `e i` lies in the weight support. Otherwise `E_{e i} = 0`,
  contradicting the entry `1` of the indicator matrix at `i`.
- Take `g = P⁻¹`. Then `g χ(T) g⁻¹ = ∑ a, T^a P⁻¹ E_a P = diag(T ^ e i)`, which
  is `diagonalUnits` of `T`.
- `eq_of_weightMatrix_eq` turns this equality of matrices into the equality
  of cocharacters.

No hypothesis beyond the field is needed. In particular there is no finiteness
or perfectness assumption on `K`.
