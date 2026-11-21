import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section

open Matrix Polynomial Set Topology

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.TraceFormula
open SigmaLiftCharacterIdentity (coefficients coefficients_associated coefficients_baseChange
  coefficients_conj continuous_coefficients continuous_cyclicNorm)
open Langlands.HarmonicAnalysis.Distribution (charpoly_eq_of_coeff_eq)

section Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The monic polynomial reconstructed from its coefficients below degree `n`. -/
def polynomialOfCoefficients (b : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ)

theorem polynomialOfCoefficients_map {S : Type*} [CommRing S] (f : R →+* S)
    (b : Fin n → R) :
    (polynomialOfCoefficients b).map f = polynomialOfCoefficients (f ∘ b) := by
  simp [polynomialOfCoefficients, Polynomial.map_sum]

theorem polynomialOfCoefficients_coefficients [Nontrivial R] (x : GeneralLinear n R) :
    polynomialOfCoefficients (coefficients x) = x.val.charpoly := by
  conv_rhs => rw [x.val.charpoly_monic.as_sum, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  unfold polynomialOfCoefficients coefficients
  exact congrArg (X ^ n + ·)
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => C (x.val.charpoly.coeff i) * X ^ i) n)

theorem polynomialOfCoefficients_isMonicOfDegree [Nontrivial R] (b : Fin n → R) :
    IsMonicOfDegree (polynomialOfCoefficients b) n := by
  refine (isMonicOfDegree_iff _ _).mpr ⟨(natDegree_le_iff_coeff_eq_zero).mpr ?_, ?_⟩
  · intro k hk
    simp [polynomialOfCoefficients, coeff_X_pow, coeff_mul_X_pow', Nat.ne_of_gt hk,
      coeff_C, show ∀ i : Fin n, k - (i : ℕ) ≠ 0 from fun i => by have := i.isLt; omega]
  · simp [polynomialOfCoefficients, coeff_mul_X_pow', coeff_C,
      show ∀ i : Fin n, n - (i : ℕ) ≠ 0 from fun i => by have := i.isLt; omega]

end Polynomial

section Parameters

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

private def rationalAssociate (h : IsCyclicAlgebra σ l) (δ : GeneralLinear n E) :
    GeneralLinear n F := Classical.choose ((cyclicNormLemma F E σ l n h).1 δ)

private theorem rationalAssociate_associated (h : IsCyclicAlgebra σ l) (δ : GeneralLinear n E) :
    IsNormAssociated σ l δ (rationalAssociate h δ) :=
  Classical.choose_spec ((cyclicNormLemma F E σ l n h).1 δ)

/-- The coefficients over `F` of the characteristic polynomial of a rational norm associate. -/
def normCoefficients (h : IsCyclicAlgebra σ l) (δ : GeneralLinear n E) : Fin n → F :=
  coefficients (rationalAssociate h δ)

theorem normCoefficients_eq_of_associated (h : IsCyclicAlgebra σ l)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (ha : IsNormAssociated σ l δ γ) :
    normCoefficients h δ = coefficients γ := by
  obtain ⟨g, hg⟩ := (cyclicNormLemma F E σ l n h).2.1 δ _ _ (rationalAssociate_associated h δ) ha
  rw [← hg, coefficients_conj]
  rfl

theorem charpoly_norm_of_associated {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (ha : IsNormAssociated σ l δ γ) :
    (cyclicNorm σ l δ).val.charpoly = γ.val.charpoly.map (algebraMap F E) := by
  obtain ⟨g, hg⟩ := ha
  have hconj : (g⁻¹ * cyclicNorm σ l δ * g).val.charpoly = (cyclicNorm σ l δ).val.charpoly := by
    simpa only [Units.val_mul, Matrix.coe_units_inv] using
      Matrix.charpoly_units_conj' g (cyclicNorm σ l δ).val
  calc
    _ = (g⁻¹ * cyclicNorm σ l δ * g).val.charpoly := hconj.symm
    _ = _ := by
      rw [hg]
      exact Matrix.charpoly_map γ.val (algebraMap F E)

theorem charpoly_norm_eq_of_normCoefficients_eq (h : IsCyclicAlgebra σ l)
    {δ δ' : GeneralLinear n E} (he : normCoefficients h δ = normCoefficients h δ') :
    (cyclicNorm σ l δ).val.charpoly = (cyclicNorm σ l δ').val.charpoly := by
  rw [charpoly_norm_of_associated (rationalAssociate_associated h δ),
    charpoly_norm_of_associated (rationalAssociate_associated h δ')]
  congr 1
  exact charpoly_eq_of_coeff_eq _ _ (congrFun he)

theorem exists_conj_of_regular_coefficients_eq {γ γ' : GeneralLinear n F}
    (hγ : IsRegularSemisimple γ) (he : coefficients γ = coefficients γ') :
    ∃ g : GeneralLinear n F, g⁻¹ * γ * g = γ' := by
  obtain ⟨g, hg⟩ := exists_matrix_conj_of_charpoly_eq_of_separable γ.val γ'.val hγ
    (charpoly_eq_of_coeff_eq _ _ fun i => (congrFun he i).symm)
  exact ⟨g⁻¹, by simpa only [inv_inv] using Units.ext hg⟩

theorem normCoefficients_eq_iff_associated (h : IsCyclicAlgebra σ l)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) :
    normCoefficients h δ = coefficients γ ↔ IsNormAssociated σ l δ γ := by
  refine ⟨fun he => ?_, normCoefficients_eq_of_associated h⟩
  obtain ⟨g, hg⟩ := exists_conj_of_regular_coefficients_eq hγ he.symm
  have ha := (rationalAssociate_associated h δ).twistedConj h.pow_eq_one 1 g⁻¹
  have hg' : g * rationalAssociate h δ * g⁻¹ = γ := by rw [← hg]; group
  simpa only [inv_inv, hg', mul_one, inv_one, one_mul, map_one] using ha

theorem normCoefficients_twistedConj (h : IsCyclicAlgebra σ l) (g δ : GeneralLinear n E) :
    normCoefficients h (twistedConj (entrywiseAut σ n) g δ) = normCoefficients h δ := by
  have ha := (rationalAssociate_associated h δ).twistedConj h.pow_eq_one g 1
  change normCoefficients h _ = coefficients (rationalAssociate h δ)
  simpa only [twistedConj, inv_one, one_mul, mul_one] using normCoefficients_eq_of_associated h ha

theorem exists_twistedConj_of_regular_normCoefficients_eq (h : IsCyclicAlgebra σ l)
    {δ δ' : GeneralLinear n E} (hδ : IsSigmaRegular σ l δ)
    (he : normCoefficients h δ = normCoefficients h δ') :
    ∃ x : GeneralLinear n E, twistedConj (entrywiseAut σ n) x δ = δ' := by
  obtain ⟨γ, ⟨g, hg⟩, hγ⟩ := hδ
  have hδ' := (normCoefficients_eq_iff_associated h hγ).mp
    (he.symm.trans (normCoefficients_eq_of_associated h ⟨g, hg⟩))
  obtain ⟨g', hg'⟩ := hδ'
  apply (cyclicNormLemma F E σ l n h).2.2
  refine ⟨g * g'⁻¹, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  calc
    _ = g' * (g⁻¹ * cyclicNorm σ l δ * g) * g'⁻¹ := by group
    _ = cyclicNorm σ l δ' := by rw [hg, ← hg']; group

variable [TopologicalSpace F] [IsTopologicalRing F]
variable [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

/-- Descending the norm coefficients along the scalar inclusion preserves continuity. -/
theorem continuous_normCoefficients (h : IsCyclicAlgebra σ l) :
    Continuous (normCoefficients (n := n) h) := by
  let : Module.Finite F E := h.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (h.2.1 ▸ h.pos)
  let a : F →ₗ[F] E := Algebra.linearMap F E
  obtain ⟨r, hr⟩ := a.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have hra : Function.LeftInverse r a := DFunLike.congr_fun hr
  have hcont : Continuous r := IsModuleTopology.continuous_of_linearMap r
  refine continuous_pi fun i => ?_
  have he : (fun δ : GeneralLinear n E => normCoefficients h δ i) =
      fun δ => r (coefficients (cyclicNorm σ l δ) i) := by
    funext δ
    rw [coefficients_associated (rationalAssociate_associated h δ), coefficients_baseChange]
    exact (hra _).symm
  rw [he]
  exact hcont.comp ((continuous_apply i).comp (continuous_coefficients.comp (continuous_cyclicNorm σ l)))

end Parameters

section Regular

variable {F : Type*} [Field F] {n : ℕ}

variable [CharZero F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] in

/-- The discriminant condition defines an open subset of the coefficient space. -/
theorem isOpen_separable_polynomialOfCoefficients (n : ℕ) :
    IsOpen {b : Fin n → F | (polynomialOfCoefficients b).Separable} := by
  let p : (MvPolynomial (Fin n) F)[X] := polynomialOfCoefficients MvPolynomial.X
  let D := p.resultant p.derivative n (n - 1)
  have hD (b : Fin n → F) :
      MvPolynomial.eval b D = (polynomialOfCoefficients b).resultant
        (polynomialOfCoefficients b).derivative n (n - 1) := by
    let ev := MvPolynomial.eval₂Hom (RingHom.id F) b
    have hp : p.map ev = polynomialOfCoefficients b := by
      rw [polynomialOfCoefficients_map]
      congr 1
      funext i
      simp [ev]
    change ev (p.resultant p.derivative n (n - 1)) = _
    rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map, hp]
  have heq : {b : Fin n → F | (polynomialOfCoefficients b).Separable} =
      (fun b => MvPolynomial.eval b D) ⁻¹' {0}ᶜ := by
    ext b
    let q := polynomialOfCoefficients b
    have hq := polynomialOfCoefficients_isMonicOfDegree b
    have he : MvPolynomial.eval b D = q.resultant q.derivative q.natDegree q.derivative.natDegree := by
      have hn : q.natDegree = n := hq.natDegree_eq
      rw [Polynomial.natDegree_derivative, hn]
      exact hD b
    change q.Separable ↔ MvPolynomial.eval b D ≠ 0
    rw [he, ← isUnit_iff_ne_zero, Polynomial.isUnit_resultant_iff_isCoprime hq.monic]
    rfl
  rw [heq]
  exact isOpen_compl_singleton.preimage (MvPolynomial.continuous_eval D)

theorem isRegularSemisimple_iff_separable_coefficients (γ : GeneralLinear n F) :
    IsRegularSemisimple γ ↔ (polynomialOfCoefficients (coefficients γ)).Separable := by
  rw [polynomialOfCoefficients_coefficients]
  rfl

theorem isSigmaRegular_iff_separable_normCoefficients {E : Type*} [CommRing E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) (δ : GeneralLinear n E) :
    IsSigmaRegular σ l δ ↔ (polynomialOfCoefficients (normCoefficients h δ)).Separable := by
  refine ⟨fun ⟨γ, ha, hγ⟩ => ?_, fun hs => ?_⟩
  · rw [normCoefficients_eq_of_associated h ha]
    exact (isRegularSemisimple_iff_separable_coefficients γ).mp hγ
  · exact ⟨rationalAssociate h δ, rationalAssociate_associated h δ,
      (isRegularSemisimple_iff_separable_coefficients _).mpr hs⟩

variable [CharZero F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

theorem isOpen_regularSemisimple (n : ℕ) :
    IsOpen {γ : GeneralLinear n F | IsRegularSemisimple γ} := by
  rw [show {γ : GeneralLinear n F | IsRegularSemisimple γ} =
      coefficients ⁻¹' {b : Fin n → F | (polynomialOfCoefficients b).Separable} from
    Set.ext isRegularSemisimple_iff_separable_coefficients]
  exact (isOpen_separable_polynomialOfCoefficients n).preimage continuous_coefficients

theorem isOpen_sigmaRegular {E : Type*} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) (n : ℕ) :
    IsOpen {δ : GeneralLinear n E | IsSigmaRegular σ l δ} := by
  rw [show {δ : GeneralLinear n E | IsSigmaRegular σ l δ} =
      normCoefficients h ⁻¹' {b : Fin n → F | (polynomialOfCoefficients b).Separable} from
    Set.ext (isSigmaRegular_iff_separable_normCoefficients h)]
  exact (isOpen_separable_polynomialOfCoefficients n).preimage (continuous_normCoefficients h)

end Regular

universe u v

/-- Continuous coefficient parameters detect regularity and give the norm and orbit comparisons. -/
def RegularOrbitParametersStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (h : IsCyclicAlgebra σ l),
    Continuous (coefficients (R := F) (n := n)) ∧
    Continuous (normCoefficients (n := n) h) ∧
    IsOpen {b : Fin n → F | (polynomialOfCoefficients b).Separable} ∧
    (∀ γ : GeneralLinear n F,
      IsRegularSemisimple γ ↔ (polynomialOfCoefficients (coefficients γ)).Separable) ∧
    (∀ δ : GeneralLinear n E,
      IsSigmaRegular σ l δ ↔ (polynomialOfCoefficients (normCoefficients h δ)).Separable) ∧
    (∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsRegularSemisimple γ →
      (normCoefficients h δ = coefficients γ ↔ IsNormAssociated σ l δ γ)) ∧
    (∀ γ γ' : GeneralLinear n F, IsRegularSemisimple γ → coefficients γ = coefficients γ' →
      ∃ g : GeneralLinear n F, g⁻¹ * γ * g = γ') ∧
    (∀ δ δ' : GeneralLinear n E, IsSigmaRegular σ l δ →
      normCoefficients h δ = normCoefficients h δ' →
      ∃ g : GeneralLinear n E, twistedConj (entrywiseAut σ n) g δ = δ')

theorem regularOrbitParameters : RegularOrbitParametersStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n h
  exact ⟨continuous_coefficients, continuous_normCoefficients h,
    isOpen_separable_polynomialOfCoefficients n, isRegularSemisimple_iff_separable_coefficients,
    isSigmaRegular_iff_separable_normCoefficients h,
    fun _ _ => normCoefficients_eq_iff_associated h,
    fun _ _ => exists_conj_of_regular_coefficients_eq,
    fun _ _ => exists_twistedConj_of_regular_normCoefficients_eq h⟩

end Langlands.BaseChange
