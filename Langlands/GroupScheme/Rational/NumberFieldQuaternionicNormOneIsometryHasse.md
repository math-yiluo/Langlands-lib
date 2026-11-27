# The Hasse principle for quaternionic norm-one isometry groups

Module: `Langlands.GroupScheme.Rational.NumberFieldQuaternionicNormOneIsometryHasse`.

The module proves `Langlands.GroupScheme.numberFieldQuaternionicNormOneIsometryHasse :
NumberFieldQuaternionicNormOneIsometryHasseStatement`: over a number field, for a central
quaternion division algebra `D` with an orthogonal involution `σ` (`dim D^σ = 3`), every
rank `n ≥ 1` and every nondegenerate `q : σ.QuadraticForms (Fin n)`, every cocycle of
`σ.normOneIsometryGroup q` on a finite Galois cover that is trivial after pullback to every
completion is trivial (Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §5.11, printed p. 101).

## Points in matrix coordinates

- `ambientMatrix F D n R` sends an affine point of the unit group of `M_n(D)` over `R` to
  its matrix over `R ⊗ D` (`FiniteAlgebraUnits.affinePointsEquiv` followed by
  `coefficientEquiv`); it is injective and natural in `R` (`ambientMatrix_naturality`).
  `ambient_reducedNorm_eq_one_iff`: the point lies in the kernel of the reduced-norm
  character exactly when its matrix has `matrixReducedNorm` one.
- `mem_range_normOneIsometryAmbientι_affine_iff`: an ambient affine point lies in the image
  of `σ.normOneIsometryGroup q` exactly when its matrix lies in `suGroup τ H R`, where `τ` is
  the canonical conjugation and `H = σ.conjugationSkewGram q`. The isometry part uses the
  isomorphism `conjugationSkewIsometryIso` of `σ.isometryGroup q` with the unitary group of
  `H` (compatible with the ambient inclusions by
  `IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp`), `mem_range_unitaryGroupι_affine_iff` and
  `isometry_iff_coefficientEquiv`.
- `normOnePointMatrix` is the resulting injective homomorphism from points of
  `σ.normOneIsometryGroup q` to `suGroup τ H R` (`normOnePointMatrix_mem`), onto it
  (`exists_normOnePointMatrix_eq`), natural in `R` (`normOnePointMatrix_naturality`).

## The proof

`normOneIsometry_isTrivial_of_locallyTrivial`: the values `GaloisCocycle.value ξ s` give a
crossed homomorphism `c` with values in `suGroup τ H L` (`GaloisCocycle.value_mul`). For each
completion `K`, triviality of the pulled-back cocycle gives, by
`GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial`, coboundary data over every
finite Galois `M ⊇ K, L`; hence `IsLocallyCoboundary τ H c`. The Galois-level Hasse principle
`SkewUnitary.suHasse` (with `isAntihermitian_conjugationSkewGram`,
`isUnit_conjugationSkewGram`) gives `a ∈ suGroup τ H L` with `c s = a * s(a)⁻¹`, and the
point `x` with matrix `a` trivializes `ξ` by `GaloisCocycle.isTrivial_iff`.
