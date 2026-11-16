import Langlands.Representation.Archimedean.ComplexStandardHomTransposeProof
import Langlands.Representation.Archimedean.ComplexJacquetKernel

/-!
# Transposing an intertwiner inside a `U(n)`-integral matrix coefficient

Let `T` be a `(𝔤, K)`-intertwiner from the `U(n)`-finite functions of the principal series of
`χ` to those of `ψ`. For `v` in the `U(n)`-finite principal series of `ψ⁻¹` there is `u` in that
of `χ⁻¹` with `⟨u, h⟩ = ⟨v, T h⟩` for the integration pairings (`exists_pairing_transpose`), and
then `∫ (T w)(κ g) v(κ) dκ = ∫ w(κ g) u(κ) dκ` for every `g ∈ GL_n(ℂ)`
(`integral_mul_transfer`): the two sides agree on `U(n)`, have the same derivatives, and are real
analytic along the `KAK` decomposition.
-/

noncomputable section

open MeasureTheory Matrix

open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff MonoidAlgebra

namespace Langlands.Archimedean

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace ComplexReverseTransfer

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexDuality
  ComplexStandardHomTransposeProof ComplexPartialJacquet ComplexMatrixCoefficientAnalytic
  ComplexGramFormula

variable {n : ℕ}

/-! ## The transpose of a vector -/

/-- **The pairing transpose.** Let `χ` be phase-power characters and `T` a `U(n)`-equivariant
linear map from the `U(n)`-finite principal series of `χ` to that of `ψ`. For every
`U(n)`-finite `v` in the principal series of `ψ⁻¹` there is a `U(n)`-finite `u` in the principal
series of `χ⁻¹` with `⟨u, h⟩ = ⟨v, T h⟩` for all `h`. -/
theorem exists_pairing_transpose {χ ψ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} (hχ : IsPhasePower χ e)
    (T : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (principalSeries ℂ n ψ) (unitaryCompact ℂ n))
    (hTK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)),
      T (principalSeriesRep ℂ n χ k f) = principalSeriesRep ℂ n ψ k (T f))
    (v : kFiniteFunctions (principalSeries ℂ n (dualChar ψ)) (unitaryCompact ℂ n)) :
    ∃ u : kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n),
      ∀ h, integralPairing n (dualChar χ) χ u h = integralPairing n (dualChar ψ) ψ v (T h) := by
  set Qc := integralPairing n (dualChar ψ) ψ with hQc
  set Qd := integralPairing n (dualChar χ) χ with hQd
  have hd : ∀ i z, dualChar χ i z * χ i z = 1 := fun i z => inv_mul_cancel₀ (hχ.ne_zero i z)
  set Λ := Qc.compl₂ T with hΛ
  have hΛapp : ∀ f h, Λ f h = Qc f (T h) := fun f h => rfl
  have hQdK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) g,
      Qd (principalSeriesRep ℂ n (dualChar χ) k g) = (principalSeriesRep ℂ n χ).dual k (Qd g) := by
    intro k g
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply]
    have e := integralPairing_principalSeriesRep (dualChar χ) χ k g
      (principalSeriesRep ℂ n χ k⁻¹ h)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have hΛK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
      Λ (principalSeriesRep ℂ n (dualChar ψ) k f) = (principalSeriesRep ℂ n χ).dual k (Λ f) := by
    intro k f
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply, hΛapp, hΛapp, hTK]
    have e := integralPairing_principalSeriesRep (dualChar ψ) ψ k f
      (principalSeriesRep ℂ n ψ k⁻¹ (T h))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have hgkd := isComplexGKModule_principalSeries n χ
  have hgkd' := isComplexGKModule_principalSeries n (dualChar χ)
  have hgkc' := isComplexGKModule_principalSeries n (dualChar ψ)
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℂ]
      (principalSeriesRep ℂ n χ).asModule :=
    KFiniteDual.isSemisimpleModule hgkd.1 hgkd.2.1
  have hblock := KFiniteDual.finiteDimensional_block hgkd.1 hgkd.2.1
    (isAdmissibleGKModule_principalSeriesRep (n := n) χ)
  let W' : Subrepresentation (principalSeriesRep ℂ n χ).dual :=
    { toSubmodule := LinearMap.range Qd
      apply_mem_toSubmodule := by
        rintro k _ ⟨g, rfl⟩
        exact ⟨principalSeriesRep ℂ n (dualChar χ) k g, hQdK k g⟩ }
  have hW' : ∀ w ∈ W', FiniteVectors.IsFiniteVector (principalSeriesRep ℂ n χ).dual w := by
    rintro _ ⟨g, rfl⟩
    exact isFiniteVector_dual_of_equivariant Qd hQdK (hgkd'.1 g)
  have hsep : ∀ h, (∀ w ∈ W', w h = 0) → h = 0 := by
    intro h hh
    by_contra hne
    obtain ⟨g, hg⟩ := exists_integralPairing_ne_zero_left hd
      (ComplexJacquetKernel.normSq_dualChar hχ) h hne
    exact hg (hh _ ⟨g, rfl⟩)
  obtain ⟨u, hu⟩ := KFiniteDual.mem_of_separating hblock W' hW' hsep
    (isFiniteVector_dual_of_equivariant Λ hΛK (hgkc'.1 v))
  exact ⟨u, fun h => congrArg (fun ℓ => ℓ h) hu⟩

/-! ## Equality of matrix coefficients from equality on `U(n)` -/

section Pairs

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure μ]

/-- **Equality of two families of matrix coefficients.** Let `P` be a relation between
`U(n)`-finite functions of the principal series of `χ₁` and of `χ₂`, stable under right
translation by `U(n)` and under all right derivatives applied to both sides. If the matrix
coefficients against `φ₁`, `φ₂` of related functions agree at `1`, they agree everywhere. -/
theorem matrixCoefficient_eq_of_rel {χ₁ χ₂ : ℕ → ℂˣ → ℂ} (e₁ e₂ : ℕ → ℂ)
    (hχ₁ : ∀ (l : ℕ) (z : ℂˣ), χ₁ l z = χ₁ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e₁ l)
    (hχ₂ : ∀ (l : ℕ) (z : ℂˣ), χ₂ l z = χ₂ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e₂ l)
    (P : (Langlands.GeneralLinear n ℂ → ℂ) → (Langlands.GeneralLinear n ℂ → ℂ) → Prop)
    (hP : ∀ a b, P a b → a ∈ kFiniteFunctions (principalSeries ℂ n χ₁) (unitaryCompact ℂ n) ∧
      b ∈ kFiniteFunctions (principalSeries ℂ n χ₂) (unitaryCompact ℂ n))
    (hPK : ∀ k ∈ unitaryCompact ℂ n, ∀ a b, P a b →
      P (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k a)
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k b))
    (hPD : ∀ (X : Matrix (Fin n) (Fin n) ℂ) a b, P a b →
      P (rightDerivative (matrixModel ℂ n) X a) (rightDerivative (matrixModel ℂ n) X b))
    {φ₁ φ₂ : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (h1 : ∀ a b, P a b → ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ 1 = ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ 1) :
    ∀ a b, P a b → ∀ g, ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ g = ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ g := by
  -- along a real diagonal one-parameter subgroup
  have hexp : ∀ (h : Fin n → ℝ) (g : Langlands.GeneralLinear n ℂ),
      (∀ a b, P a b → ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ g = ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ g) →
      ∀ a b, P a b → ∀ t : ℝ, ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ (g * expDiag h t) =
        ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ (g * expDiag h t) := by
    intro h g h0 a b hab t
    have hderiv : ∀ a b, P a b →
        deriv (fun t => ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ (g * expDiag h t) -
          ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ (g * expDiag h t)) =
        fun t => ComplexMatrixCoefficientAnalytic.matrixCoefficient μ
            (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) a) φ₁
            (g * expDiag h t) -
          ComplexMatrixCoefficientAnalytic.matrixCoefficient μ
            (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) b) φ₂
            (g * expDiag h t) := fun a b hab => funext fun t =>
      ((analyticAt_matrixCoefficient μ e₁ hχ₁ (hP a b hab).1 hφ₁ g h t).2.sub
        (analyticAt_matrixCoefficient μ e₂ hχ₂ (hP a b hab).2 hφ₂ g h t).2).deriv
    have hiter : ∀ j : ℕ, ∀ a b, P a b →
        iteratedDeriv j (fun t => ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ (g * expDiag h t) -
          ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ (g * expDiag h t)) 0 = 0 := by
      intro j
      induction j with
      | zero =>
        intro a b hab
        rw [iteratedDeriv_zero]
        simp only [expDiag_zero, mul_one]
        rw [h0 a b hab, sub_self]
      | succ j ih =>
        intro a b hab
        rw [iteratedDeriv_succ', hderiv a b hab]
        exact ih _ _ (hPD _ a b hab)
    have := MatrixCoefficientAnalytic.eq_zero_of_iteratedDeriv_eq_zero
      (fun t _ => (analyticAt_matrixCoefficient μ e₁ hχ₁ (hP a b hab).1 hφ₁ g h t).1.sub
        (analyticAt_matrixCoefficient μ e₂ hχ₂ (hP a b hab).2 hφ₂ g h t).1)
      (hiter · a b hab)
    exact sub_eq_zero.mp (congrFun this t)
  intro a b hab g
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := exists_kak g
  rw [matrixCoefficient_mul_unitary μ a φ₁ (k₁ * expDiag h 1) k₂,
    matrixCoefficient_mul_unitary μ b φ₂ (k₁ * expDiag h 1) k₂]
  have hk1 : ∀ a b, P a b → ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ k₁ = ComplexMatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ k₁ :=
    fun a b hab => by
      have e1 := matrixCoefficient_mul_unitary μ a φ₁ 1 k₁
      have e2 := matrixCoefficient_mul_unitary μ b φ₂ 1 k₁
      rw [one_mul] at e1 e2
      rw [e1, e2]
      exact h1 _ _ (hPK k₁ hk₁ a b hab)
  exact hexp h k₁ hk1 _ _ (hPK k₂ hk₂ a b hab) 1

end Pairs

/-! ## The transfer identity -/

theorem toUnits_mk {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ : Matrix.unitaryGroup (Fin n) ℂ) = k :=
  Units.ext rfl

/-- **The transfer identity.** Let `T` be a `(𝔤, K)`-intertwiner from the `U(n)`-finite
principal series of `χ` to that of `ψ` (both phase-power), `v` a `U(n)`-finite function of the
principal series of `ψ⁻¹` and `u` one of `χ⁻¹` with `⟨u, h⟩ = ⟨v, T h⟩` for all `h`. Then
`∫ (T w)(κ g) v(κ) dκ = ∫ w(κ g) u(κ) dκ` for every `w` and every `g ∈ GL_n(ℂ)`. -/
theorem integral_mul_transfer {χ ψ : ℕ → ℂˣ → ℂ} {eχ eψ : ℕ → ℂ} (hχ : IsPhasePower χ eχ)
    (hψ : IsPhasePower ψ eψ)
    (T : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (principalSeries ℂ n ψ) (unitaryCompact ℂ n))
    (hTK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)),
      T (principalSeriesRep ℂ n χ k f) = principalSeriesRep ℂ n ψ k (T f))
    (hTX : ∀ (X : Matrix (Fin n) (Fin n) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)),
      T (principalSeriesLie ℂ n χ (1 ⊗ₜ X) f) = principalSeriesLie ℂ n ψ (1 ⊗ₜ X) (T f))
    (v : kFiniteFunctions (principalSeries ℂ n (dualChar ψ)) (unitaryCompact ℂ n))
    (u : kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n))
    (huv : ∀ h, integralPairing n (dualChar χ) χ u h = integralPairing n (dualChar ψ) ψ v (T h))
    (w : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (g : Langlands.GeneralLinear n ℂ) :
    ∫ κ, (T w : Langlands.GeneralLinear n ℂ → ℂ) ((κ : Langlands.GeneralLinear n ℂ) * g) *
        (v : Langlands.GeneralLinear n ℂ → ℂ) κ ∂unitaryHaar n =
      ∫ κ, (w : Langlands.GeneralLinear n ℂ → ℂ) ((κ : Langlands.GeneralLinear n ℂ) * g) *
        (u : Langlands.GeneralLinear n ℂ → ℂ) κ ∂unitaryHaar n := by
  set μ := (unitaryHaar n).map (ComplexJacquetDual.toUnitaryGroup n)
  set P : (Langlands.GeneralLinear n ℂ → ℂ) → (Langlands.GeneralLinear n ℂ → ℂ) → Prop :=
    fun a b => ∃ w' : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n),
      a = (T w' : Langlands.GeneralLinear n ℂ → ℂ) ∧ b = (w' : Langlands.GeneralLinear n ℂ → ℂ)
    with hPdef
  have hvc := continuous_of_mem_kFiniteFunctions v.2
  have huc := continuous_of_mem_kFiniteFunctions u.2
  have hcont : ∀ {a b : Langlands.GeneralLinear n ℂ → ℂ}, Continuous a → Continuous b →
      ∀ g : Langlands.GeneralLinear n ℂ,
        Continuous fun y : Langlands.GeneralLinear n ℂ => a (y * g) * b y :=
    fun ha hb g => (ha.comp (continuous_id.mul continuous_const)).mul hb
  have hmc : ∀ {a b : Langlands.GeneralLinear n ℂ → ℂ}, Continuous a → Continuous b →
      ∀ g : Langlands.GeneralLinear n ℂ,
        ComplexMatrixCoefficientAnalytic.matrixCoefficient μ a (b ∘ Unitary.toUnits) g =
          ∫ κ, a ((κ : Langlands.GeneralLinear n ℂ) * g) * b κ ∂unitaryHaar n := by
    intro a b ha hb g
    simp only [ComplexMatrixCoefficientAnalytic.matrixCoefficient]
    exact ComplexJacquetDual.integral_map_toUnitaryGroup (f := fun y => a (y * g) * b y)
      (hcont ha hb g)
  have key := matrixCoefficient_eq_of_rel μ eψ eχ hψ.eq hχ.eq P
    (fun a b ⟨w', ha, hb⟩ => ⟨ha ▸ (T w').2, hb ▸ w'.2⟩)
    (fun k hk a b ⟨w', ha, hb⟩ => by
      refine ⟨principalSeriesRep ℂ n χ ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ w', ?_, ?_⟩
      · rw [hTK, principalSeriesRep_apply_coe, toUnits_mk, ha]
      · rw [principalSeriesRep_apply_coe, toUnits_mk, hb])
    (fun X a b ⟨w', ha, hb⟩ => by
      refine ⟨principalSeriesLie ℂ n χ (1 ⊗ₜ X) w', ?_, ?_⟩
      · rw [hTX, principalSeriesLie_one_tmul_apply_coe, ha]
      · rw [principalSeriesLie_one_tmul_apply_coe, hb])
    (hvc.comp continuous_unitary_toUnits) (huc.comp continuous_unitary_toUnits)
    (fun a b ⟨w', ha, hb⟩ => by
      subst ha hb
      rw [hmc (continuous_of_mem_kFiniteFunctions (T w').2) hvc,
        hmc (continuous_of_mem_kFiniteFunctions w'.2) huc]
      simp only [mul_one]
      have e := huv w'
      rw [integralPairing_apply, integralPairing_apply] at e
      calc ∫ κ, (T w' : Langlands.GeneralLinear n ℂ → ℂ) (κ : Langlands.GeneralLinear n ℂ) *
              (v : Langlands.GeneralLinear n ℂ → ℂ) κ ∂unitaryHaar n
          = ∫ κ, (v : Langlands.GeneralLinear n ℂ → ℂ) (κ : Langlands.GeneralLinear n ℂ) *
              (T w' : Langlands.GeneralLinear n ℂ → ℂ) κ ∂unitaryHaar n :=
            integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)
        _ = ∫ κ, (u : Langlands.GeneralLinear n ℂ → ℂ) (κ : Langlands.GeneralLinear n ℂ) *
              (w' : Langlands.GeneralLinear n ℂ → ℂ) κ ∂unitaryHaar n := e.symm
        _ = _ := integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _))
    _ _ ⟨w, rfl, rfl⟩ g
  rwa [hmc (continuous_of_mem_kFiniteFunctions (T w).2) hvc,
    hmc (continuous_of_mem_kFiniteFunctions w.2) huc] at key

end ComplexReverseTransfer

end Langlands.Archimedean
