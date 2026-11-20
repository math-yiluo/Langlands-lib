import Langlands.BaseChange.TwistedCharacter
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof

/-! # Common invariant parameters for ordinary and twisted conjugacy in base change -/

noncomputable section

namespace Langlands.BaseChange.SigmaLiftCharacterIdentity

open Langlands.JacquetLanglands

section Coefficients

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The coefficients below the leading term of the characteristic polynomial. -/
def coefficients (g : GeneralLinear n R) : Fin n → R :=
  fun i => (g : Matrix (Fin n) (Fin n) R).charpoly.coeff i

lemma coefficients_conj (x g : GeneralLinear n R) :
    coefficients (x⁻¹ * g * x) = coefficients g := by
  funext i
  simp only [coefficients, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

variable [TopologicalSpace R] [IsTopologicalRing R]

lemma continuous_charpoly_coefficient (k : ℕ) :
    Continuous fun g : GeneralLinear n R => (g : Matrix (Fin n) (Fin n) R).charpoly.coeff k := by
  have h : (fun g : GeneralLinear n R => (g : Matrix (Fin n) (Fin n) R).charpoly.coeff k) =
      fun g : GeneralLinear n R => MvPolynomial.eval
        (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) R) ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom R) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
    funext g
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom,
      Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2)

lemma continuous_coefficients : Continuous (coefficients (n := n) (R := R)) :=
  continuous_pi fun i => continuous_charpoly_coefficient (R := R) (n := n) i

end Coefficients

section BaseChange

variable {F : Type*} [Field F] {E : Type*} [CommRing E] [Algebra F E]
variable {l n : ℕ} {σ : E ≃ₐ[F] E}

lemma coefficients_cyclicNorm_conj (hσ : σ ^ l = 1) (x δ : GeneralLinear n E) :
    coefficients (cyclicNorm σ l (x⁻¹ * δ * entrywiseAut σ n x)) =
      coefficients (cyclicNorm σ l δ) := by
  rw [cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, coefficients_conj]

lemma coefficients_associated {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (h : IsNormAssociated σ l δ γ) :
    coefficients (cyclicNorm σ l δ) = coefficients (baseChange F E n γ) := by
  obtain ⟨x, hx⟩ := h
  rw [← hx, coefficients_conj]

lemma coefficients_baseChange_conj (x γ : GeneralLinear n F) :
    coefficients (baseChange F E n (x⁻¹ * γ * x)) = coefficients (baseChange F E n γ) := by
  rw [map_mul, map_mul, map_inv, coefficients_conj]

lemma coefficients_baseChange (γ : GeneralLinear n F) (i : Fin n) :
    coefficients (baseChange F E n γ) i = algebraMap F E (coefficients γ i) := by
  change ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E)).charpoly.coeff i = _
  rw [Matrix.charpoly_map, Polynomial.coeff_map]
  rfl

lemma charpoly_eq_of_baseChange_coefficients (hE : IsCyclicAlgebra σ l)
    {γ γ' : GeneralLinear n F}
    (h : coefficients (baseChange F E n γ) = coefficients (baseChange F E n γ')) :
    (γ : Matrix (Fin n) (Fin n) F).charpoly = (γ' : Matrix (Fin n) (Fin n) F).charpoly := by
  have := hE.1
  have : Nontrivial E := Module.finrank_pos_iff.mp (hE.2.1.symm ▸ hE.pos)
  apply HarmonicAnalysis.Distribution.charpoly_eq_of_coeff_eq
  intro i
  apply (algebraMap F E).injective
  change algebraMap F E (coefficients γ i) = algebraMap F E (coefficients γ' i)
  simpa only [coefficients_baseChange] using congrFun h i

variable [TopologicalSpace F] [TopologicalSpace E]
variable [IsTopologicalRing E] [IsModuleTopology F E]

variable [IsTopologicalRing F] in
lemma continuous_baseChange : Continuous (baseChange F E n) := by
  have hmap : Continuous (algebraMap F E) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)
  apply Units.continuous_iff.mpr
  have hc : Continuous fun γ : GeneralLinear n F => ((baseChange F E n γ : GeneralLinear n E) :
      Matrix (Fin n) (Fin n) E) :=
    continuous_pi fun i => continuous_pi fun j => hmap.comp (Units.continuous_val.matrix_elem i j)
  exact ⟨hc, by simpa only [Function.comp_def, map_inv] using hc.comp continuous_inv⟩

lemma continuous_entrywiseAut (σ : E ≃ₐ[F] E) : Continuous (entrywiseAut σ n) := by
  have hσ : Continuous σ := IsModuleTopology.continuous_of_linearMap σ.toLinearMap
  apply Units.continuous_iff.mpr
  have hc : Continuous fun δ : GeneralLinear n E => ((entrywiseAut σ n δ : GeneralLinear n E) :
      Matrix (Fin n) (Fin n) E) :=
    continuous_pi fun i => continuous_pi fun j => hσ.comp (Units.continuous_val.matrix_elem i j)
  exact ⟨hc, by simpa only [Function.comp_def, map_inv] using hc.comp continuous_inv⟩

lemma continuous_cyclicNorm (σ : E ≃ₐ[F] E) (l : ℕ) :
    Continuous (fun δ : GeneralLinear n E => cyclicNorm σ l δ) := by
  induction l with
  | zero => simpa only [cyclicNorm_zero] using continuous_const (y := (1 : GeneralLinear n E))
  | succ l ih =>
    simpa only [cyclicNorm_succ, Pi.mul_def] using
      ih.mul (continuous_entrywiseAut (n := n) (σ ^ l))

end BaseChange

end Langlands.BaseChange.SigmaLiftCharacterIdentity
