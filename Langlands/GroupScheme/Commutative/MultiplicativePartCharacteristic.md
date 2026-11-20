# Homomorphisms from multiplicative-type to unipotent groups after base change

This internal derived unit completes Milne 2017, Theorem 16.13(a). It adds the
characteristic clause to the existence result of
`Commutative/MultiplicativePartExistence`.

## Main results

Let `k` be a field.

- `CommutativeDecomposition.baseChange_hom_eq_zero`. Let `S` be a group of
  multiplicative type over `k`, and `Q` an affine unipotent group, locally of
  finite type over `k`. For every `k`-algebra `R`, every homomorphism
  `S_R ⟶ Q_R` is trivial. Base change is along `Spec R → Spec k`. The Library
  had this statement only for `R = k`
  (`IsMultiplicativeType.hom_eq_zero_of_isUnipotent`, Milne 14.18).
- `CommutativeDecomposition.range_baseChange_comp_iso`. Let `s : S ⟶ G`
  have the same range as the kernel of `q : G ⟶ Q`, with `S` of
  multiplicative type and `Q` as above. Then for every `k`-algebra `R` and
  every automorphism `α` of `G_R`,
  `range (s_R ≫ α) = range s_R`.
- `CommutativeDecomposition.exists_characteristic_multiplicativePart`. This is
  exactly part (a) of the Library statement
  `CommutativeMultiplicativeUnipotentDecompositionStatement`. The
  multiplicative-type subgroup comes from `exists_multiplicativePart`, and its
  stability comes from `range_baseChange_comp_iso`.

## Proof of `baseChange_hom_eq_zero`

Milne proves the base-changed vanishing (Proposition 15.18) using a minimal
subgroup containing the image and the cohomology of Section 15. This module uses a different, matrix-level route.

1. **A unitriangular closed embedding of `Q`**
   (`exists_closed_pointUnitriangular`). The Library's graded Hopf algebra
   result `Algebra.GradedHopf.exists_unitriangular_matrixCoefficients` gives
   upper unitriangular generating matrix coefficients of the coordinate ring
   of `Q`. `AffineLinearEmbedding.toGLHom` turns these into a closed matrix
   representation `ρ : Q ⟶ GL_n`. `pointMatrix_toGLHom_apply` shows that every
   point matrix of `ρ` is upper unitriangular. The predicate
   `PointUnitriangular ρ` states this for points over every test scheme.
2. **Stability of the predicate.** `PointUnitriangular.restrict` covers
   precomposition with any homomorphism. `PointUnitriangular.baseChange`
   covers base change, composed with the canonical comparison
   `GeneralLinear.baseChangeIso`. Its proof uses `comp_isoOfPoints_hom` and
   `baseChangePointsEquiv_comp`.
3. **Diagonalizable groups over an arbitrary ring.** Let `ρ` be a
   representation of `D(Λ)` over any commutative ring whose point matrices
   are all upper unitriangular. Then `ρ` is trivial
   (`eq_zero_of_pointUnitriangular`). The proof evaluates at the universal
   point and so works with the universal matrix in `R[Λ]`.
   - `coefficientColumn_weight` says that each coefficient column at weight
     `m` is a weight vector: `M v = X^m v`. Downward induction on the row
     index, using unitriangularity, makes the coefficient columns at every
     `m ≠ 0` vanish (`coefficientColumn_eq_zero_of_unitriangular`).
   - So each entry of the universal matrix is a constant. The evaluation
     `universalMatrix_evaluateOne` at the trivial character then makes the
     universal matrix the identity
     (`universalMatrix_eq_one_of_unitriangular`).
   - `eq_zero_of_universalMatrix_eq_one` turns this back into triviality of
     `ρ`, via `GeneralLinear.affinePointsEquiv`.
4. **Splitting and descent.** Let `K` be the field over which `S` becomes
   diagonalizable, and `R' = R ⊗[k] K`. Let `φ : S_R ⟶ Q_R`. Composing with
   `ρ_R` and the `GL_n` comparison gives a point-unitriangular representation
   `ψ` of `S_R`. Base change along `c : Spec R' → Spec R` makes `S` become
   `D_{R'}(Λ)`, through an explicit isomorphism `E`. `E` combines
   `Diagonalizable.baseChangeIso`, the splitting isomorphism, and
   `Langlands.GroupScheme.baseChangeCompIso'` with the commuting square
   `R → R' ← K` over `k`. Step 3 shows that `E ≫ ψ_{R'}` is trivial, so
   `ψ_{R'}` is trivial. The map `R → R'` is faithfully flat, being the base
   change of `k → K`. So pullback along `c` is faithful, and `ψ` is trivial.
   Finally, the scheme morphism underlying `ρ_R` followed by the `GL_n`
   comparison is a monomorphism, because `ρ` is a closed immersion and
   pullback preserves monomorphisms. Hence `φ` is trivial.

`Langlands.GroupScheme.baseChangeCompIso'` is a local copy of the Library's `baseChangeCompIso'`
from `Torus/ConnectedQuotientCommutative`. The copy avoids importing that
module.

## Proof of the characteristic clause

Let `β` be any endomorphism of `G_R`. Then `(s_R ≫ β) ≫ q_R` is a
homomorphism `S_R ⟶ Q_R`, so it is trivial by `baseChange_hom_eq_zero`.
`range_le_baseChange_of_comp_eq_zero` shows that
`range (s_R ≫ β) ≤ range s_R`. Its proof uses `kernel_range_baseChange` and
`SubgroupFunctor.range_baseChangeHom`, together with the hypothesis that
`kernel q` and `s` have the same range. Take `β = α.hom` for one inclusion.
For the other, take `β = α.inv` and compose with `α.hom`
(`range_comp_le_range_comp`).

## Provenance

The statement of `exists_characteristic_multiplicativePart` is Milne,
*Algebraic Groups* (2017), Theorem 16.13(a), in the form of the Library
statement. `baseChange_hom_eq_zero` is Milne's Proposition 15.18, with `U` assumed
affine and locally of finite type. All proofs are
internal and use only published Library results, as described above.
