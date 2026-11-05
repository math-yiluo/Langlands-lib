import Langlands.Representation.Exponents.UnrestrictedCompressedLatticeBoundStatement
import Langlands.Representation.Exponents.CompressedLatticeCoefficientBoundProof

/-! # Operator-norm growth bounds for compressed finite lattices -/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uG uV uI

namespace UnrestrictedLatticeBound

/-- A submultiplicative endomorphism size bounds powers with no spectral
assumption, including on the zero vector space. -/
theorem endNorm_pow_le
    {W : Type uV} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : Module.End ℂ W) (n : ℕ) :
    EndomorphismBound.endNorm (f ^ n) ≤
      (EndomorphismBound.endNorm (1 : Module.End ℂ W) + 1) *
        (EndomorphismBound.endNorm f + 2) ^ n := by
  have h1 := EndomorphismBound.endNorm_nonneg (1 : Module.End ℂ W)
  have hf := EndomorphismBound.endNorm_nonneg f
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    calc
      _ ≤ EndomorphismBound.endNorm (f ^ n) * EndomorphismBound.endNorm f :=
        EndomorphismBound.endNorm_mul_le _ _
      _ ≤ ((EndomorphismBound.endNorm (1 : Module.End ℂ W) + 1) *
          (EndomorphismBound.endNorm f + 2) ^ n) *
            (EndomorphismBound.endNorm f + 2) := by
        apply mul_le_mul ih (by linarith)
        · exact EndomorphismBound.endNorm_nonneg f
        · positivity
      _ = _ := by ring

/-- Finitely many generator norms give radii uniform in the input vector and
functional, without constraining eigenvalues. -/
theorem exists_apply_le_prod
    {I : Type uI} [Fintype I] [DecidableEq I]
    {W : Type uV} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : (I → ℕ) → Module.End ℂ W)
    (hadd : ∀ a b, f (a + b) = f a * f b) :
    ∃ a : I → ℝ, (∀ i, 1 < a i) ∧
      ∀ (v : W) (φ : Module.Dual ℂ W),
        ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ, ‖φ (f n v)‖ ≤ C * ∏ i, a i ^ n i := by
  let a : I → ℝ := fun i => EndomorphismBound.endNorm (f (Pi.single i 1)) + 2
  let c : I → ℝ := fun _ => EndomorphismBound.endNorm (1 : Module.End ℂ W) + 1
  have ha : ∀ i, 1 < a i := by
    intro i
    dsimp [a]
    linarith [EndomorphismBound.endNorm_nonneg (f (Pi.single i 1))]
  have hc : ∀ i, 0 ≤ c i := fun _ => by
    dsimp [c]
    linarith [EndomorphismBound.endNorm_nonneg (1 : Module.End ℂ W)]
  refine ⟨a, ha, fun v φ => ?_⟩
  obtain ⟨D, hD, hbound⟩ := EndomorphismBound.exists_apply_le_endNorm φ v
  let E := EndomorphismBound.endNorm (f 0) * ∏ i, c i
  have hE : 0 ≤ E := mul_nonneg (EndomorphismBound.endNorm_nonneg _)
    (Finset.prod_nonneg fun i _ => hc i)
  refine ⟨D * E + 1, by positivity, fun n => ?_⟩
  have hp : 0 ≤ ∏ i, a i ^ n i :=
    Finset.prod_nonneg fun i _ => pow_nonneg (by linarith [ha i]) _
  calc
    ‖φ (f n v)‖ ≤ D * EndomorphismBound.endNorm (f n) := hbound _
    _ ≤ D * (E * ∏ i, a i ^ n i) :=
      mul_le_mul_of_nonneg_left
        (CompressedLatticeBound.endNorm_le_prod_of_pow_bounds f hadd c a
          (fun i k => endNorm_pow_le (f (Pi.single i 1)) k) n) hD
    _ ≤ (D * E + 1) * ∏ i, a i ^ n i := by nlinarith

end UnrestrictedLatticeBound

/-- Actual multiplicative compact compressions give unrestricted product
exponential bounds for original coefficients fixed by that compact subgroup. -/
theorem unrestrictedCompressedLatticeBound :
    UnrestrictedCompressedLatticeBoundStatement.{uG, uV, uI} := by
  intro G _ _ _ V _ _ I _ _ ρ hρ K hK N M Nbar hfactor τ hup hlow hmid
  let W := fixedVectors ρ K.toSubgroup
  have : FiniteDimensional ℂ W := hρ.2 K
  let f : (I → ℕ) → Module.End ℂ W :=
    fun n => Jacquet.compressedAction ρ hρ.1 K hK (τ (.ofAdd n))
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    change Jacquet.compressedAction ρ hρ.1 K hK (τ (.ofAdd a * .ofAdd b)) = _
    rw [map_mul]
    exact Jacquet.compressedAction_mul_of_factor ρ hρ.1 K hK N M Nbar hfactor _ _
      (hup a) (hlow b) (hmid b)
  obtain ⟨a, ha, hbound⟩ := UnrestrictedLatticeBound.exists_apply_le_prod f hadd
  refine ⟨a, ha, fun v φ hφ => ?_⟩
  obtain ⟨C, hC, hcoeff⟩ := hbound v (φ.comp W.subtype)
  refine ⟨C, hC, fun n => ?_⟩
  rw [StrictCartanBound.dual_apply_eq_compressedAction ρ hρ.1 K hK φ hφ]
  exact hcoeff n

end Langlands
