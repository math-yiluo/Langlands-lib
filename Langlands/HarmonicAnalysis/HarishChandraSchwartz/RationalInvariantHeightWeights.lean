import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable

/-! # Convolution weights for invariant real height majorants

The auxiliary height may be any continuous nonnegative subadditive
left-compact-invariant majorant of the original matrix height.
It need not itself come from a matrix representation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type*} [MeasurableSpace Γ] {mu : Measure Γ} {Ξ σ₀ σ : Γ → ℝ}

/-- A larger height preserves the weighted Xi-square estimate at the same
natural exponent. -/
theorem SquareIntegrableWeight.mono_height
    (h : SquareIntegrableWeight mu Ξ σ₀)
    (hσ₀ : ∀ g, 0 ≤ σ₀ g) (hle : ∀ g, σ₀ g ≤ σ g) :
    SquareIntegrableWeight mu Ξ σ := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, lt_of_le_of_lt (lintegral_mono fun g => ?_) hd⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (Ξ g))
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hσ₀ g])
    (by linarith [hle g]) (neg_nonpos.mpr (Nat.cast_nonneg d))

end Generic

section Majorant

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- The real-height conditions needed to replace a matrix height in
convolution weights. This does not require a new matrix realization. -/
def IsConvolutionHeightMajorant (K : Subgroup Γ) (σ₀ σ : Γ → ℝ) : Prop :=
  (∀ g, 0 ≤ σ g) ∧ Continuous σ ∧
    (∀ g h, σ (g * h) ≤ σ g + σ h) ∧
    (∀ k ∈ K, ∀ g, σ (k * g) = σ g) ∧
    ∀ g, σ₀ g ≤ σ g

end Majorant

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

include hKo in
/-- The actual Xi gives convolution weights for every invariant continuous
subadditive height majorant, from the original local Xi-square estimate.
No relation between the matrix image of `K` and integral matrices is needed. -/
theorem rationalConvolutionWeights_of_heightMajorant
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) [CompactSpace K]
    {mu : Measure (rationalPoints G)} {σ : rationalPoints G → ℝ}
    (hσ : IsConvolutionHeightMajorant K (rationalHeight (F := F) ρ) σ)
    (hsq : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ)) :
    ConvolutionWeights mu K (rationalXi hKc hPK) σ where
  pos := rationalXi_pos hKo hKc hPK
  nonneg := hσ.1
  continuous_xi := continuous_rationalXi hKo hKc hPK
  continuous_sigma := hσ.2.1
  one_add_le := one_add_le_of_le_add hσ.1 hσ.2.2.1
  xi_mul_left k hk g := by
    simpa only [mul_one] using rationalXi_mul_mul hKo hKc hPK hk K.one_mem g
  sigma_mul_left := hσ.2.2.2.1
  xi_inv := rationalXi_inv hG hi hν hKo hKc hPK
  integral_xi := integral_rationalXi_mul_mul hKo hKc hPK
  square := hsq.mono_height (rationalHeight_nonneg ρ) hσ.2.2.2.2

end Rational

end Langlands.HarishChandraSchwartz
