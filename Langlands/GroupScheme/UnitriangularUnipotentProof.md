# Proof of unipotence of the upper unitriangular group scheme

Module `Langlands.GroupScheme.UnitriangularUnipotentProof`. It imports
`Langlands.GroupScheme.UnitriangularUnipotentStatement`,
`Langlands.GroupScheme.Unipotent.CoordinateBialgebra` and
`Langlands.GroupScheme.UnitriangularUnipotent.Coordinates`.

The main theorem is

```lean
theorem Langlands.GroupScheme.unitriangularUnipotent :
    UnitriangularUnipotentStatement.{u}
```

It proves the Library statement `Langlands.GroupScheme.UnitriangularUnipotentStatement`
at arbitrary universe `u`. For every field `k : Type u` and every `N : ℕ`, including
`N = 0`, the scheme `GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k)
(fun i => -(i.val : ℤ))` is `IsUnipotent`. There is no condition on the field. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Literature

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a
Field* (2017), source `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Theorem 14.5,
printed pp. 281–282 (PDF pp. 297–298), shows (b)⇒(c)⇒(a). Applied to `U_N` itself,
this says that `U_N` is unipotent.

Milne's (b)⇒(c) gives `X_ij` the weight `j - i` and filters `O(U_n) = k[X_ij | i < j]`
by weight. The formula `Δ(X_ij) = X_ij ⊗ 1 + 1 ⊗ X_ij + ∑_{i<l<j} X_il ⊗ X_lj`
shows `Δ(C_r) ⊆ ∑_i C_i ⊗ C_{r-i}`, so the Hopf algebra is coconnected. His
(c)⇒(a) then filters every comodule and finds a fixed vector in the bottom step.

The Lean proof keeps the weight argument but replaces the comodule filtration of (c)⇒(a)
with a direct coefficient argument. It then uses the Library criterion
`Unipotent.isUnipotent_of_oneMemStable`. That criterion says that a corepresented
group scheme over a field is unipotent when every nonzero finite-dimensional
right-translation stable subspace of its coordinate bialgebra contains `1`
(`Unipotent.OneMemStable`). The single weight estimate needed is
`coeff_comulPoly_of_weight_le` from `WeightCore`. In the polynomial coordinates, the
coefficient of the second-factor monomial `m` in `Δ f` is the constant `f.coeff m`
whenever no monomial of `f` has weight above that of `m`. This is the top-weight part
of Milne's inclusion `Δ(C_r) ⊆ ∑_i C_i ⊗ C_{r-i}`.

## Authorship

Worker 1500 wrote `Langlands.GroupScheme.UnitriangularUnipotent.WeightCore`, the
polynomial weight estimate and `rid_lTensor_eval₂Hom`, from definitions agreed with
Worker 1405. Worker 1405 wrote `Langlands.GroupScheme.UnitriangularUnipotent.Coordinates`
and this module.

## Generic part

These theorems work for any group functor `F` on commutative `k`-algebras whose
underlying set functor is corepresented, `e : (F ⋙ forget GrpCat).CorepresentableBy B`.
`comul e`, `bialgebra e` and `pt e` are the Library comultiplication, bialgebra
structure and classified points (`Langlands.GroupScheme.AffineLinearEmbedding`). The
theorems are stated for a general `B` because the tensor square of the concrete
quotient ring `Coord k N` picks up a conflicting module instance.

`comul_entry_of_pt`: let `ι A : F.obj A → Matrix n n A` be multiplicative, and let
`M` be a matrix over `B` such that `ι A (pt e f) i j = f (M i j)` for every algebra
map `f : B →ₐ[k] A`. Then `comul e (M i j) = ∑_l M i l ⊗ M l j`.
Proof: `pt e (comul e)` is the product of the points classified by `includeLeft` and
`includeRight` (`pt_comul`). Apply `ι` over `B ⊗ B` and take the `(i, j)` entry.
The right side is `∑_l (M i l ⊗ 1)(1 ⊗ M l j)`.

`oneMemStable_of_coordinates`: suppose `θ : MvPolynomial (Pos N) k →ₐ[k] B` and
`χ : B →ₐ[k] MvPolynomial (Pos N) k` are inverse, and the matrix
`U = upperTri (fun q => θ (X q))` satisfies `comul e (U i j) = ∑_l U i l ⊗ U l j`.
Then `OneMemStable k B` holds for `bialgebra e`. Proof:

1. Let `V` be a nonzero stable subspace and choose `b ∈ V` with `b ≠ 0`. Then
   `χ b ≠ 0`. Choose `m` in the support of `χ b` of maximal weight
   `Finsupp.weight posWeight` (`Finset.exists_max_image`).
2. Let `κ : MvPolynomial (Pos N) (MvPolynomial (Pos N) k) → B ⊗ B` be `eval₂Hom`.
   It sends inner coefficients `c` to `θ c ⊗ 1` and outer variables `X q` to
   `1 ⊗ θ (X q)`. Then `comul e ∘ θ = κ ∘ comulPoly k` as ring maps
   (`MvPolynomial.ringHom_ext`). On constants both sides are the algebra map. On a
   variable `X p`, `p = (i, j)`, write `θ (X p) = U i j`. Apply the hypothesis on
   `comul e (U i j)` and `comulPoly_X`. Then use `map_upperTri` with `includeLeft`
   and `includeRight` to match `∑_l U i l ⊗ U l j` with
   `κ (∑_l upperTri (C ∘ X) i l * upperTri X l j)`.
3. Let `φ = lcoeff m ∘ χ`, the coefficient of `m`, as a functional on `B`. Then
   `φ (θ (monomial d 1))` is `1` when `d = m` and `0` otherwise.
4. Since `b = θ (χ b)`, step 2 gives `comul e b = κ (comulPoly k (χ b))`. By
   `rightAct_apply` and `rid_lTensor_eval₂Hom`,
   `rightAct φ b = θ ((comulPoly k (χ b)).coeff m)`. By
   `coeff_comulPoly_of_weight_le` and the maximality of `m`, this is
   `θ (C ((χ b).coeff m)) = (χ b).coeff m • 1`.
5. The scalar `(χ b).coeff m` is nonzero because `m` is in the support. So
   `1 = ((χ b).coeff m)⁻¹ • rightAct φ b ∈ V`, by stability and closure under scalars.

Finite dimensionality of `V` is not used.

`isUnipotent_of_coordinates`: under the same hypotheses,
`IsUnipotent (Corepresented.groupScheme F e)`. This is
`isUnipotent_of_oneMemStable` applied to the previous theorem.

## The concrete group

`unitriangularUnipotent`: for a field `k` and `N : ℕ`, the target scheme is by
definition `Corepresented.groupScheme` of `corep k N` from `Coordinates`. Apply
`isUnipotent_of_coordinates` with `θ = theta k N`, `χ = chi k N`, and the inverse
laws `chi_theta` and `theta_chi`. The matrix hypothesis comes from
`comul_entry_of_pt`. Its inputs are:

- `ι A x`: the matrix underlying the invertible matrix `x.1` (a point of the
  unitriangular functor is a subtype element of `GL (Fin N) A`). It is
  multiplicative by definition.
- `M = upperTri (fun q => theta k N (X q))`. The required identity
  `ι A (pt (corep k N) f) i j = f (M i j)` follows from `pt_apply`
  (`ι A (pt f) i j = f (u i j)`), `upperTri_u` and `theta_X`.

The argument has no case split on `N`. For `N = 0`, `Pos 0` is empty, so the
polynomial ring is `k` and the chosen monomial `m` is `0`.
