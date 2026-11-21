import Langlands.Geometry.Analytic.DrinfeldAdaptedBasis
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.GaussPoint

/-! # Lifting norms to points of Drinfeld's upper half space -/

noncomputable section

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open AnalyticAffineSpace PresentedAffinoidAlgebra GeneralizedTateAlgebra

variable {F : Type v} [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

/-- Affine-linear monomials: the constant, then the coordinate monomials. -/
private def linearExponent (d : ℕ) (i : Fin (d + 1)) : Fin d →₀ ℕ :=
  Fin.cases 0 (fun j => Finsupp.single j 1) i

private theorem linearExponent_injective (d : ℕ) : Function.Injective (linearExponent d) := by
  intro i j h
  induction i using Fin.cases <;> induction j using Fin.cases
  · rfl
  · rename_i j
    have h' := congrArg (fun e : Fin d →₀ ℕ => e j) h
    simp [linearExponent] at h'
  · rename_i i
    have h' := congrArg (fun e : Fin d →₀ ℕ => e i) h
    simp [linearExponent] at h'
  · rename_i i j
    congr 1
    by_contra hn
    have h' := congrArg (fun e : Fin d →₀ ℕ => e i) h
    change (Finsupp.single i 1 : Fin d →₀ ℕ) i = Finsupp.single j 1 i at h'
    exact Nat.one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hn] using h')

private def diagonalWeight (r : PositivePolyradius (Fin d)) (i : Fin (d + 1)) : ℝ :=
  Fin.cases 1 (fun j => r j) i

private theorem diagonalWeight_pos (r : PositivePolyradius (Fin d)) (i : Fin (d + 1)) :
    0 < diagonalWeight r i :=
  Fin.cases one_pos r.positive i

private theorem weight_linearExponent (r : PositivePolyradius (Fin d)) (i : Fin (d + 1)) :
    r.weight (linearExponent d i) = diagonalWeight r i := by
  induction i using Fin.cases
  · exact r.weight_zero
  · simp [linearExponent, diagonalWeight, PositivePolyradius.weight]

omit [CompleteSpace K] in
private theorem affine_series_eq_sum (r : PositivePolyradius (Fin d)) (c : Fin (d + 1) → K) :
    algebraMap K (GeneralizedTateAlgebra r K) (c 0) + ∑ i : Fin d, c i.succ • X r K i =
      ∑ i, monomial r K (linearExponent d i) (c i) := by
  rw [Fin.sum_univ_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show linearExponent d i.succ = Finsupp.single i 1 from rfl, monomial_eq,
    StrictTateAlgebra.monomialValue, Finsupp.prod_single_index (by simp), pow_one,
    Algebra.smul_def]

omit [CompleteSpace K] in
private theorem norm_affine_series_le_iff (r : PositivePolyradius (Fin d)) (c : Fin (d + 1) → K)
    {B : ℝ} (hB : 0 ≤ B) :
    ‖algebraMap K (GeneralizedTateAlgebra r K) (c 0) + ∑ i : Fin d, c i.succ • X r K i‖ ≤ B ↔
      ∀ i, ‖c i‖ * diagonalWeight r i ≤ B := by
  rw [affine_series_eq_sum K r c, norm_sum_monomial_le_iff _ (linearExponent_injective d) _ hB]
  simp only [weight_linearExponent]

private def restrictDisc (m : ℕ) (r : PositivePolyradius (Fin d)) (hr : ∀ i, r i ≤ radius K m) :
    BoundedAlgHom K (disc K d m) (GeneralizedTateAlgebra r K) := by
  letI := (disc K d m).ideal_closed
  exact BoundedAlgHom.liftQuotient K (disc K d m).ideal
    (boundedRestrictRadius (polyradius K d m) r hr K) (fun a ha => by
      have ha0 : a = 0 := ha
      rw [ha0, map_zero])

omit [CompleteSpace K] in
private theorem restrictDisc_coordinate (m : ℕ) (r : PositivePolyradius (Fin d))
    (hr : ∀ i, r i ≤ radius K m) (i : Fin d) :
    restrictDisc K m r hr (coordinate K (disc K d m) i) = X r K i := by
  change restrictRadius (polyradius K d m) r hr K (X (polyradius K d m) K i) = _
  exact restrictRadius_X _ _ _ _ _

private theorem exists_diagonalGaussPoint (r : PositivePolyradius (Fin d)) :
    ∃ z : Omega F K d, ∀ (a : Fin (d + 1) → F) (B : ℝ), 0 ≤ B →
      (omegaNorm K z a ≤ B ↔ ∀ i, ‖a i‖ * diagonalWeight r i ≤ B) := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (∑ i : Fin d, r i) (one_lt_inv_norm_scale K)
  have hr (i : Fin d) : r i ≤ radius K m :=
    (Finset.single_le_sum (fun j _ => (r.positive j).le) (Finset.mem_univ i)).trans hm.le
  let φ := restrictDisc K m r hr
  let y := chart K d m (BanachSpectrum.comap φ.toBoundedRingHom (gaussPoint r K))
  have heval (a : Fin (d + 1) → F) :
      linearNorm K d (coefficients F K d a) y =
      ‖algebraMap K (GeneralizedTateAlgebra r K) (algebraMap F K (a 0)) +
        ∑ i : Fin d, algebraMap F K (a i.succ) • X r K i‖ := by
    change gaussPoint r K (φ (linearForm K d m (coefficients F K d a))) = _
    rw [gaussPoint_apply]
    unfold linearForm
    simp only [map_add, AlgHom.commutes, map_sum, map_smul, φ, restrictDisc_coordinate, coefficients]
  have hbound (a : Fin (d + 1) → F) (B : ℝ) (hB : 0 ≤ B) :
      linearNorm K d (coefficients F K d a) y ≤ B ↔ ∀ i, ‖a i‖ * diagonalWeight r i ≤ B := by
    rw [heval]
    simpa only [coefficients, norm_algebraMap'] using
      norm_affine_series_le_iff K r (coefficients F K d a) hB
  have hy : y ∈ Omega F K d := by
    intro a ha hz
    have h := (hbound a 0 le_rfl).1 hz.le
    apply ha
    ext i
    have hi := nonpos_of_mul_nonpos_left (h i) (diagonalWeight_pos r i)
    exact norm_le_zero_iff.1 hi
  exact ⟨⟨y, hy⟩, hbound⟩

/-- The matrix acting on row vectors by taking coordinates in a basis. -/
private def coordinateMatrix (b : Module.Basis (Fin (d + 1)) F (Fin (d + 1) → F)) :
    Matrix.GeneralLinearGroup (Fin (d + 1)) F :=
  let δ := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun)
  { val := δ.val.transpose
    inv := δ.inv.transpose
    val_inv := by rw [← Matrix.transpose_mul, δ.inv_val, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, δ.val_inv, Matrix.transpose_one] }

private theorem vecMul_coordinateMatrix
    (b : Module.Basis (Fin (d + 1)) F (Fin (d + 1) → F)) (a : Fin (d + 1) → F) :
    Matrix.vecMul a (coordinateMatrix b : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
      fun i => b.repr a i := by
  let δ := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun)
  change Matrix.vecMul a δ.val.transpose = _
  rw [Matrix.vecMul_transpose]
  change Matrix.mulVecLin δ.val a = _
  rw [← Matrix.GeneralLinearGroup.toLin_apply δ a]
  simp only [δ, MulEquiv.apply_symm_apply, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv]
  rfl

variable [ProperSpace F] [NeZero d]

private theorem exists_reduction_eq (ν : VectorNorm F (Fin (d + 1) → F)) :
    ∃ z : Omega F K d, reduction K z = ⟦ν⟧ := by
  have hN : Module.finrank F (Fin (d + 1) → F) = d + 1 := Module.finrank_fin_fun F
  let a₀ : Fin (d + 1) → F := Pi.single 0 1
  have ha₀ : a₀ ≠ 0 := by
    intro h
    have h' := congrFun h 0
    simp [a₀] at h'
  obtain ⟨b, hb, -⟩ := ν.exists_isAdaptedBasis_with_first hN ha₀
  let r : PositivePolyradius (Fin d) :=
    ⟨fun i => ν (b i.succ) / ν (b 0), fun i => div_pos (ν.pos (b.ne_zero _)) (ν.pos (b.ne_zero _))⟩
  have hb0 : 0 < ν (b 0) := ν.pos (b.ne_zero _)
  have hweight (i : Fin (d + 1)) : diagonalWeight r i = ν (b i) / ν (b 0) := by
    induction i using Fin.cases
    · exact (div_self hb0.ne').symm
    · rfl
  obtain ⟨z, hz⟩ := exists_diagonalGaussPoint (F := F) K r
  let γ := coordinateMatrix b
  refine ⟨actionMap K γ z, ?_⟩
  rw [reduction_actionMap]
  have hcomp (a : Fin (d + 1) → F) : (γ • omegaNorm K z) a = ν a / ν (b 0) := by
    rw [VectorNorm.smul_apply, vecMul_coordinateMatrix]
    have hiff (C : ℝ) (hC : 0 ≤ C) :
        omegaNorm K z (fun i => b.repr a i) ≤ C ↔ ν a / ν (b 0) ≤ C := by
      rw [hz _ _ hC, div_le_iff₀ hb0, hb.apply_le_iff (mul_nonneg hC hb0.le)]
      simp only [hweight, ← mul_div_assoc, div_le_iff₀ hb0]
    have h1 := (hiff _ (div_nonneg (ν.nonneg a) hb0.le)).2 le_rfl
    have h2 := (hiff _ ((omegaNorm K z).nonneg _)).1 le_rfl
    exact le_antisymm h1 h2
  change (⟦γ • omegaNorm K z⟧ : NormClass F (Fin (d + 1) → F)) = ⟦ν⟧
  have hh : VectorNorm.Homothetic ν (γ • omegaNorm K z) :=
    ⟨(ν (b 0))⁻¹, inv_pos.2 hb0, fun a => (hcomp a).trans (div_eq_inv_mul _ _)⟩
  exact (Quotient.sound hh).symm

/-- A point of Drinfeld's upper half space lifting the class of a vector norm. -/
def pointOfVectorNorm (ν : VectorNorm F (Fin (d + 1) → F)) : Omega F K d :=
  (exists_reduction_eq K ν).choose

@[simp] theorem reduction_pointOfVectorNorm (ν : VectorNorm F (Fin (d + 1) → F)) :
    reduction K (pointOfVectorNorm K ν) = ⟦ν⟧ :=
  (exists_reduction_eq K ν).choose_spec

/-- The reduction map is surjective on the homothety classes of ultrametric norms. -/
theorem reduction_surjective : Function.Surjective (reduction (F := F) K (d := d)) := by
  intro x
  obtain ⟨ν, rfl⟩ := Quotient.exists_rep x
  exact ⟨pointOfVectorNorm K ν, reduction_pointOfVectorNorm K ν⟩

end Langlands.Analytic.DrinfeldUpperHalfSpace
