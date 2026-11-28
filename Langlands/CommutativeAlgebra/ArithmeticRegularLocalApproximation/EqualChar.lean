import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Base

/-! # Regular local charts for complete discrete valuation rings of equal characteristic -/

universe u w

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation

/-- Let `W'` be a complete discrete valuation ring whose residue characteristic is zero in `W'`
(equal characteristic). Then every map from a finite type `ℤ`-algebra to `Frac W'` factors
through a regular local chart. The presentation used is `W' = W'[X] ⧸ (X - ϖ)`. -/
theorem chartConclusion_equalChar
    {W' : Type u} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
    [IsAdicComplete (maximalIdeal W') W'] {ϖ : W'} (hϖ : Irreducible ϖ)
    (hchar : ((ringChar (ResidueField W') : ℕ) : W') = 0)
    (C : Type w) [CommRing C] [Algebra.FiniteType ℤ C] (F' : C →+* FractionRing W') :
    ChartConclusion W' C F' := by
  refine chartConclusion_of_dvr hϖ
    (intCast_prime_cases (ringChar (ResidueField W')) (Or.inl hchar))
    (RingHom.id W') (X - Polynomial.C ϖ) (monic_X_sub_C ϖ) (by simp) ?_
    (fun y => ⟨Polynomial.C y, by simp⟩) ?_ C F'
  · rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Ideal.neg_mem_iff]
    exact irreducible_notMem_maximalIdeal_sq hϖ
  · intro q hq
    rw [dvd_iff_isRoot, IsRoot.def, ← eval₂_id]
    exact hq

end Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation
