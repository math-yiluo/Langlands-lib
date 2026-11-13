# Splitting the orthogonal group of an ordinary quadratic form

This internal module supports the proof of
`Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryStatement`. Let `K` be a
field, `n` a finite type, and `q` a quadratic form for the scalar involution
`FirstKindInvolution.scalar K` (transpose on `M_n(K)`), represented by a matrix
`Q : Matrix n n K`. Let `L` be a field extension of `K`. The module shows that, after
a hyperbolic change of coordinates `P`, the base change to `L` of the isometry group
`(FirstKindInvolution.scalar K).isometryGroup q` is isomorphic to the split orthogonal
group `OrthogonalMatrix.groupScheme (Fin m) (CommRingCat.of L)` of
`Langlands.GroupScheme.OrthogonalMatrix.Basic`. Over an algebraically closed `L`
such a `P` exists by `exists_hyperbolic_matrix`
(`Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic`).

The construction follows the precedent of the published symplectic splitting in
`Langlands.GroupScheme.Quaternionic.SymplecticReductive`: points of the base change
are identified with units of `Γ(T, ⊤) ⊗[K] M_n(K)`, and the published
`isoOfPointModels` turns a natural group isomorphism on points into an isomorphism of
group schemes.

## Congruence and alternating matrices

- `isAlt_conj_iff`: if `P' * P = 1`, then `P X Pᵀ` is alternating exactly when `X`
  is.
- `isAlt_conj_sub_iff`: if `P' * P = 1` and `P Q Pᵀ - F` is alternating, then for
  every `U` the matrix `g = P U P'` satisfies "`g F gᵀ - F` is alternating" exactly
  when `U Q Uᵀ - Q` is alternating. The proof writes `g F gᵀ - F` as
  `P (U Q Uᵀ - Q) Pᵀ` plus `(P Q Pᵀ - F) - g (P Q Pᵀ - F) gᵀ`, and the second
  summand is alternating.

## The matrix chart

`chart K n R` is Mathlib's algebra isomorphism `(matrixEquivTensor n K R).symm :
R ⊗[K] M_n(K) ≃ₐ[K] M_n(R)`, with `r ⊗ M ↦ r • M.map (algebraMap K R)`
(`chart_tmul`). It carries the base change of the scalar involution to the transpose
(`chart_baseChange`). It carries the defect
`IsometryCut.defect (scalar K).matrix n Q y = y (1 ⊗ Q) ᵗy - 1 ⊗ Q` to
`Y Q_R Yᵀ - Q_R`, where `Y` is the chart of `y` (`chart_defect`). It commutes with
coefficient changes (`chart_naturality`). An element `z` lies in the base change
`R ⊗ {a - ᵗa}` of the quadratic kernel exactly when `chart K n R z` is alternating
(`mem_quadraticKernel_baseChange_iff`).

## Points of the base change

`baseChangeIsometryGroup q` abbreviates the base change of `O(q)` along
`scalarBaseMap K L`. For `T` over `Spec L`, `isometryUnitPoint q T` is the group
homomorphism from `T`-points of the base change to units of
`restrictedSections K L T ⊗[K] M_n(K)`. It composes the published
`GroupScheme.baseChangePointsEquiv`, the closed immersion `isometryGroupι q` into the
unit group scheme, and `FiniteAlgebraUnits.pointsEquiv`. The following hold.

- The defect of the unit lies in the base-changed quadratic kernel
  (`isometryUnitPoint_defect_mem`, by `mem_range_isometryGroupι_iff`).
- Restriction along `a : T' ⟶ T` acts by the induced coefficient change of global
  sections (`isometryUnitPoint_naturality`).
- Every unit whose defect lies in the base-changed quadratic kernel comes from a point
  (`exists_isometryUnitPoint_eq`).
- `isometryUnitPoint q T` is injective (`isometryUnitPoint_injective`), because
  `isometryGroupι q` is a monomorphism.

## The split matrix

Fix `P : Matrix (Fin m ⊕ Fin m) n L` and `P' : Matrix n (Fin m ⊕ Fin m) L`. For an
`R` that is a `K`- and `L`-algebra with compatible scalars, `splitMatrix K P P' R u`
is `P_R * chart K n R u * P'_R`. If `P * P' = 1` and `P' * P = 1`, it is
multiplicative and unital (`splitMatrix_one`, `splitMatrix_mul`) and injective
(`splitMatrix_injective`). If also `P Q_L Pᵀ - formMatrix (Fin m) L` is alternating
(`isAlt_map_hyperbolic` transports this to `R`), then:

- `splitMatrix K P P' R u` is orthogonal for the split form exactly when the defect
  of `u` lies in the base-changed quadratic kernel (`splitMatrix_mem_iff`, from
  `isAlt_conj_sub_iff`);
- every split orthogonal matrix `g` is `splitMatrix K P P' R w` for a unit `w` of
  this kind (`exists_splitMatrix_eq`). Take `w` to be the preimage under the chart of
  `P'_R g P_R`, whose inverse is `P'_R (invMatrix g) P_R`.

`splitMatrix_naturality` shows that `splitMatrix` commutes with `L`-algebra maps.

## The isomorphism

Assume `Submodule.Quotient.mk Q = q`, `P * P' = 1`, `P' * P = 1`, and that
`P Q_L Pᵀ - formMatrix (Fin m) L` is alternating. Then
`splitPointsHom` sends a `T`-point `x` to `splitMatrix` of `isometryUnitPoint q T x`.
It is a bijective group homomorphism onto `orthogonalGroup (Fin m) Γ(T, ⊤)`
(`splitPointsHom_bijective`), so it gives `splitPointsEquiv`. This equivalence is
natural in `T` (`splitPointsEquiv_naturality`). With the split model's
`OrthogonalMatrix.pointsEquiv` and `pointsEquiv_naturality` for the split model,
`isoOfPointModels` gives

`splittingIso : baseChangeIsometryGroup q ≅ groupScheme (Fin m) (CommRingCat.of L)`.

`nonempty_splittingIso`: let `L` be algebraically closed, `Fintype.card n = 2 * m`,
and `Q + Qᵀ` invertible. Then the base change along `scalarBaseMap K L` of the
isometry group of `Submodule.Quotient.mk Q` is isomorphic to
`groupScheme (Fin m) (CommRingCat.of L)`. The proof maps `Q` to `L`, notes that
`Q_L + Q_Lᵀ` is still invertible, obtains `P, P'` from `exists_hyperbolic_matrix`,
and applies `splittingIso`.
