import Langlands.Representation.Archimedean.TransposePairing
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # The inverse-transpose twist of an archimedean module -/

noncomputable section

universe uV

set_option autoImplicit false

open scoped TensorProduct Matrix

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable (𝕂 : Type) [RCLike 𝕂] (n : ℕ)

/-- Pullback of the compact action by actual inverse transpose. -/
def transposeTwistRep {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V :=
  ρ.comp (compactIota 𝕂 n).toMonoidHom

/-- Pullback of the Lie action by the complexification of negative transpose. -/
def transposeTwistLie {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V :=
  π.comp (complexifiedMatrixLieIota 𝕂 n).toLieHom

@[simp]
theorem transposeTwistRep_apply {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V)
    (k : Matrix.unitaryGroup (Fin n) 𝕂) :
    transposeTwistRep 𝕂 n ρ k = ρ (compactIota 𝕂 n k) := rfl

@[simp]
theorem transposeTwistLie_apply {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) :
    transposeTwistLie 𝕂 n π X = π (complexifiedMatrixLieIota 𝕂 n X) := rfl

@[simp]
theorem transposeTwistRep_twice {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V) :
    transposeTwistRep 𝕂 n (transposeTwistRep 𝕂 n ρ) = ρ := by
  ext k v
  simp only [transposeTwistRep_apply, compactIota_involutive]

@[simp]
theorem transposeTwistLie_twice {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    transposeTwistLie 𝕂 n (transposeTwistLie 𝕂 n π) = π := by
  ext X v
  simp only [transposeTwistLie_apply, complexifiedMatrixLieIota_involutive]

theorem continuous_compactIota : Continuous (compactIota 𝕂 n) := by
  refine continuous_induced_rng.mpr (continuous_matrix fun i j => ?_)
  change Continuous fun k : Matrix.unitaryGroup (Fin n) 𝕂 =>
    star ((k : Matrix (Fin n) (Fin n) 𝕂) i j)
  have h : Continuous fun A : Matrix (Fin n) (Fin n) 𝕂 => A i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact (h.comp continuous_subtype_val).star

/-- Inverse transpose carries compact conjugation to conjugation of negative transpose. -/
theorem matrixLieIota_compact_conj (k : Matrix.unitaryGroup (Fin n) 𝕂)
    (X : Matrix (Fin n) (Fin n) 𝕂) :
    matrixLieIota 𝕂 n
        ((k : Matrix (Fin n) (Fin n) 𝕂) * X * star (k : Matrix (Fin n) (Fin n) 𝕂)) =
      (compactIota 𝕂 n k : Matrix (Fin n) (Fin n) 𝕂) * matrixLieIota 𝕂 n X *
        star (compactIota 𝕂 n k : Matrix (Fin n) (Fin n) 𝕂) := by
  change -((k : Matrix (Fin n) (Fin n) 𝕂) * X *
      star (k : Matrix (Fin n) (Fin n) 𝕂)).transpose =
    (star (k : Matrix (Fin n) (Fin n) 𝕂)).transpose * (-X.transpose) *
      star ((star (k : Matrix (Fin n) (Fin n) 𝕂)).transpose)
  have hstar : star ((star (k : Matrix (Fin n) (Fin n) 𝕂)).transpose) =
      (k : Matrix (Fin n) (Fin n) 𝕂).transpose := by
    ext i j
    exact star_star _
  rw [hstar]
  simp only [Matrix.transpose_mul, mul_neg, neg_mul, Matrix.mul_assoc]

namespace TransposeTwist

/-- A tangent vector to the unitary group at the identity is skew-Hermitian. -/
theorem star_eq_neg_of_hasDerivAt
    (γ : ℝ → Matrix.unitaryGroup (Fin n) 𝕂)
    (X : Matrix (Fin n) (Fin n) 𝕂) (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) 𝕂) i j)
      (X i j) 0) (i j : Fin n) :
    star (X j i) = -X i j := by
  have hd : HasDerivAt
      (fun t => ∑ l, star ((γ t : Matrix (Fin n) (Fin n) 𝕂) l i) *
        (γ t : Matrix (Fin n) (Fin n) 𝕂) l j)
      (∑ l, (star (X l i) * (γ 0 : Matrix (Fin n) (Fin n) 𝕂) l j +
        star ((γ 0 : Matrix (Fin n) (Fin n) 𝕂) l i) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ => ((hγ l i).star).mul (hγ l j)
  have hc : (fun t => ∑ l, star ((γ t : Matrix (Fin n) (Fin n) 𝕂) l i) *
      (γ t : Matrix (Fin n) (Fin n) 𝕂) l j) =
      fun _ => (1 : Matrix (Fin n) (Fin n) 𝕂) i j := by
    funext t
    rw [← Matrix.UnitaryGroup.star_mul_self (γ t), Matrix.mul_apply]
    rfl
  rw [hc] at hd
  have h := (hasDerivAt_const (0 : ℝ)
    ((1 : Matrix (Fin n) (Fin n) 𝕂) i j)).unique hd
  rw [h0] at h
  simp [Matrix.one_apply, Finset.sum_add_distrib] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The actual compact twist has derivative negative ordinary transpose. -/
theorem hasDerivAt_compactIota
    (γ : ℝ → Matrix.unitaryGroup (Fin n) 𝕂)
    (X : Matrix (Fin n) (Fin n) 𝕂) (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) 𝕂) i j)
      (X i j) 0) (i j : Fin n) :
    HasDerivAt
      (fun t => (compactIota 𝕂 n (γ t) : Matrix (Fin n) (Fin n) 𝕂) i j)
      (matrixLieIota 𝕂 n X i j) 0 := by
  have h := (hγ i j).star
  rw [star_eq_neg_of_hasDerivAt 𝕂 n γ X h0 hγ j i] at h
  exact h

end TransposeTwist

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V)

theorem orbitSpan_transposeTwistRep (v : V) :
    FiniteVectors.orbitSpan (transposeTwistRep 𝕂 n ρ) v = FiniteVectors.orbitSpan ρ v := by
  unfold FiniteVectors.orbitSpan
  congr 1
  ext w
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨compactIota 𝕂 n k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨compactIota 𝕂 n k, by simp only [transposeTwistRep_apply,
      compactIota_involutive]⟩

@[simp]
theorem isFiniteVector_transposeTwistRep_iff (v : V) :
    FiniteVectors.IsFiniteVector (transposeTwistRep 𝕂 n ρ) v ↔
      FiniteVectors.IsFiniteVector ρ v := by
  unfold FiniteVectors.IsFiniteVector
  rw [orbitSpan_transposeTwistRep]

theorem isIrreducibleGKModule_transposeTwist
    (hirr : IsIrreducibleGKModule ρ π) :
    IsIrreducibleGKModule (transposeTwistRep 𝕂 n ρ) (transposeTwistLie 𝕂 n π) := by
  refine ⟨hirr.1, fun W hK hL => hirr.2 W ?_ ?_⟩
  · intro k w hw
    simpa only [transposeTwistRep_apply, compactIota_involutive] using
      hK (compactIota 𝕂 n k) w hw
  · intro X w hw
    simpa only [transposeTwistLie_apply, complexifiedMatrixLieIota_involutive] using
      hL (complexifiedMatrixLieIota 𝕂 n X) w hw

@[simp]
theorem isIrreducibleGKModule_transposeTwist_iff :
    IsIrreducibleGKModule (transposeTwistRep 𝕂 n ρ) (transposeTwistLie 𝕂 n π) ↔
      IsIrreducibleGKModule ρ π := by
  refine ⟨fun h => ?_, isIrreducibleGKModule_transposeTwist 𝕂 n ρ π⟩
  simpa only [transposeTwistRep_twice, transposeTwistLie_twice] using
    isIrreducibleGKModule_transposeTwist 𝕂 n _ _ h

/-- Pulling both compact representations back by an involution identifies the same
intertwiner space. -/
theorem gkIntertwiners_transposeTwist (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) 𝕂 →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners (transposeTwistRep 𝕂 n ρ) d τ =
      gkIntertwiners ρ d (τ.comp (compactIota 𝕂 n).toMonoidHom) := by
  ext T
  constructor
  · intro h k x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      transposeTwistRep_apply, compactIota_involutive] using
      h (compactIota 𝕂 n k) x
  · intro h k x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      transposeTwistRep_apply, compactIota_involutive] using
      h (compactIota 𝕂 n k) x

theorem isAdmissibleGKModule_transposeTwist
    (hadm : IsAdmissibleGKModule ρ) :
    IsAdmissibleGKModule (transposeTwistRep 𝕂 n ρ) := by
  intro d τ hτ
  rw [gkIntertwiners_transposeTwist]
  exact hadm d (τ.comp (compactIota 𝕂 n).toMonoidHom)
    (hτ.comp (continuous_compactIota 𝕂 n))

@[simp]
theorem isAdmissibleGKModule_transposeTwist_iff :
    IsAdmissibleGKModule (transposeTwistRep 𝕂 n ρ) ↔ IsAdmissibleGKModule ρ := by
  refine ⟨fun h => ?_, isAdmissibleGKModule_transposeTwist 𝕂 n ρ⟩
  simpa only [transposeTwistRep_twice] using
    isAdmissibleGKModule_transposeTwist 𝕂 n _ h

section Real

variable {n}
  {ρR : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {πR : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}

theorem isRealGKModule_transposeTwist (hgk : IsRealGKModule n ρR πR) :
    IsRealGKModule n (transposeTwistRep ℝ n ρR) (transposeTwistLie ℝ n πR) := by
  refine ⟨fun v => (isFiniteVector_transposeTwistRep_iff ℝ n ρR v).2 (hgk.1 v),
    fun v ℓ => (hgk.2.1 v ℓ).comp (continuous_compactIota ℝ n), ?_, ?_⟩
  · intro γ X h0 hγ v ℓ
    exact hgk.2.2.1 (fun t => compactIota ℝ n (γ t)) (matrixLieIota ℝ n X)
      (by simp [h0]) (TransposeTwist.hasDerivAt_compactIota ℝ n γ X h0 hγ) v ℓ
  · intro k X v
    have h := hgk.2.2.2 (compactIota ℝ n k) (matrixLieIota ℝ n X) v
    rw [← matrixLieIota_compact_conj] at h
    simpa only [transposeTwistRep_apply, transposeTwistLie_apply,
      complexifiedMatrixLieIota_tmul, matrixLieIota_apply] using h

@[simp]
theorem isRealGKModule_transposeTwist_iff :
    IsRealGKModule n (transposeTwistRep ℝ n ρR) (transposeTwistLie ℝ n πR) ↔
      IsRealGKModule n ρR πR := by
  refine ⟨fun h => ?_, isRealGKModule_transposeTwist⟩
  simpa only [transposeTwistRep_twice, transposeTwistLie_twice] using
    isRealGKModule_transposeTwist h

end Real

section Complex

variable {n}
  {ρC : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {πC : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

theorem isComplexGKModule_transposeTwist (hgk : IsComplexGKModule n ρC πC) :
    IsComplexGKModule n (transposeTwistRep ℂ n ρC) (transposeTwistLie ℂ n πC) := by
  refine ⟨fun v => (isFiniteVector_transposeTwistRep_iff ℂ n ρC v).2 (hgk.1 v),
    fun v ℓ => (hgk.2.1 v ℓ).comp (continuous_compactIota ℂ n), ?_, ?_⟩
  · intro γ X h0 hγ v ℓ
    exact hgk.2.2.1 (fun t => compactIota ℂ n (γ t)) (matrixLieIota ℂ n X)
      (by simp [h0]) (TransposeTwist.hasDerivAt_compactIota ℂ n γ X h0 hγ) v ℓ
  · intro k X v
    have h := hgk.2.2.2 (compactIota ℂ n k) (matrixLieIota ℂ n X) v
    rw [← matrixLieIota_compact_conj] at h
    simpa only [transposeTwistRep_apply, transposeTwistLie_apply,
      complexifiedMatrixLieIota_tmul, matrixLieIota_apply] using h

@[simp]
theorem isComplexGKModule_transposeTwist_iff :
    IsComplexGKModule n (transposeTwistRep ℂ n ρC) (transposeTwistLie ℂ n πC) ↔
      IsComplexGKModule n ρC πC := by
  refine ⟨fun h => ?_, isComplexGKModule_transposeTwist⟩
  simpa only [transposeTwistRep_twice, transposeTwistLie_twice] using
    isComplexGKModule_transposeTwist h

end Complex

end Langlands.Archimedean
