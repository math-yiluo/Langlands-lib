import Langlands.Global.PrimitiveAdelicMinimum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Rational bases adapted to primitive adelic height minima -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The first standard rational coordinate vector in positive dimension. -/
def firstVector (hn : 0 < n) : Fin n → F :=
  Pi.single ⟨0, hn⟩ 1

theorem firstVector_ne_zero (hn : 0 < n) : firstVector F n hn ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp [firstVector] at this

/-- Every nonzero rational vector is the first column of a rational invertible
matrix, in every positive finite dimension. -/
theorem exists_rational_basis_change (hn : 0 < n) (v : Fin n → F) (hv : v ≠ 0) :
    ∃ γ : RationalGL F n, γ.val *ᵥ firstVector F n hn = v := by
  let e := LinearEquiv.toSpanNonzeroSingleton F (Fin n → F)
    (firstVector F n hn) (firstVector_ne_zero F n hn)
  let f := LinearEquiv.toSpanNonzeroSingleton F (Fin n → F) v hv
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq (e.symm.trans f)
  let b := LinearMap.GeneralLinearGroup.ofLinearEquiv a
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm b, ?_⟩
  have hfirst : a (firstVector F n hn) = v := by
    have h := ha (e 1)
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
    simp only [f, e, LinearEquiv.toSpanNonzeroSingleton_apply, one_smul] at h
    exact h.symm
  have hb : Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.toLin.symm b) = b :=
    Matrix.GeneralLinearGroup.toLin.apply_symm_apply b
  have h := congrArg (fun c : LinearMap.GeneralLinearGroup F (Fin n → F) =>
    c.toLinearEquiv (firstVector F n hn)) hb
  exact h.trans hfirst

theorem rational_mulVec (γ : RationalGL F n) (v : Fin n → F) :
    rational F n (γ.val *ᵥ v) = (AdelicGL.rational F n γ).val *ᵥ rational F n v := by
  funext i
  exact RingHom.map_mulVec (diagonal F) γ.val v i

theorem rationalHeight_mul_rational (g : AdelicGL F n) (γ : RationalGL F n)
    (v : Fin n → F) :
    rationalHeight F n (g * AdelicGL.rational F n γ) v =
      rationalHeight F n g (γ.val *ᵥ v) := by
  unfold rationalHeight
  rw [rational_mulVec, Matrix.mulVec_mulVec, Units.val_mul]

omit [NumberField F] in
theorem rational_mulVec_ne_zero (γ : RationalGL F n) {v : Fin n → F} (hv : v ≠ 0) :
    γ.val *ᵥ v ≠ 0 := by
  intro h
  apply hv
  calc
    v = (γ⁻¹).val *ᵥ (γ.val *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

/-- Right multiplication by an actual rational invertible matrix does not change
the rational height minimum. -/
theorem minimumRationalHeight_mul_rational (g : AdelicGL F n) (γ : RationalGL F n)
    (hn : 0 < n) :
    minimumRationalHeight F n (g * AdelicGL.rational F n γ) hn =
      minimumRationalHeight F n g hn := by
  apply le_antisymm
  · have hw := rational_mulVec_ne_zero F n γ⁻¹ (minimumRationalVector_ne_zero F n g hn)
    calc minimumRationalHeight F n (g * AdelicGL.rational F n γ) hn
        ≤ rationalHeight F n (g * AdelicGL.rational F n γ)
            ((γ⁻¹).val *ᵥ minimumRationalVector F n g hn) :=
          minimumRationalVector_min F n _ hn _ hw
      _ = minimumRationalHeight F n g hn := by
          rw [rationalHeight_mul_rational, Matrix.mulVec_mulVec, ← Units.val_mul,
            mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
          rfl
  · calc minimumRationalHeight F n g hn
        ≤ rationalHeight F n g
            (γ.val *ᵥ minimumRationalVector F n (g * AdelicGL.rational F n γ) hn) :=
          minimumRationalVector_min F n g hn _
            (rational_mulVec_ne_zero F n γ (minimumRationalVector_ne_zero F n _ hn))
      _ = minimumRationalHeight F n (g * AdelicGL.rational F n γ) hn := by
          rw [← rationalHeight_mul_rational]
          rfl

/-- A rational invertible matrix with the chosen global minimizing vector as
its first column. -/
def minimumBasisChange (g : AdelicGL F n) (hn : 0 < n) : RationalGL F n :=
  (exists_rational_basis_change F n hn (minimumRationalVector F n g hn)
    (minimumRationalVector_ne_zero F n g hn)).choose

theorem minimumBasisChange_first (g : AdelicGL F n) (hn : 0 < n) :
    (minimumBasisChange F n g hn).val *ᵥ firstVector F n hn =
      minimumRationalVector F n g hn :=
  (exists_rational_basis_change F n hn (minimumRationalVector F n g hn)
    (minimumRationalVector_ne_zero F n g hn)).choose_spec

/-- The actual adelic matrix after the rational change of basis. -/
def minimumAdaptedMatrix (g : AdelicGL F n) (hn : 0 < n) : AdelicGL F n :=
  g * AdelicGL.rational F n (minimumBasisChange F n g hn)

theorem minimumAdaptedMatrix_first_height (g : AdelicGL F n) (hn : 0 < n) :
    rationalHeight F n (minimumAdaptedMatrix F n g hn) (firstVector F n hn) =
      minimumRationalHeight F n g hn := by
  rw [minimumAdaptedMatrix, rationalHeight_mul_rational, minimumBasisChange_first]
  rfl

theorem minimumAdaptedMatrix_first_min (g : AdelicGL F n) (hn : 0 < n)
    (v : Fin n → F) (hv : v ≠ 0) :
    rationalHeight F n (minimumAdaptedMatrix F n g hn) (firstVector F n hn) ≤
      rationalHeight F n (minimumAdaptedMatrix F n g hn) v := by
  rw [minimumAdaptedMatrix_first_height, minimumAdaptedMatrix, rationalHeight_mul_rational]
  exact minimumRationalVector_min F n g hn _
    (rational_mulVec_ne_zero F n _ hv)

end Langlands.Global.PrimitiveAdelicHeight
