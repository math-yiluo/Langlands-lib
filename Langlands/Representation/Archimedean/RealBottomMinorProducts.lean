import Langlands.Representation.Archimedean.CompoundMinorProduct
import Langlands.Representation.Archimedean.RealTiedMinorProduct

/-! # Products of bottom minors as generators of real principal series -/

noncomputable section

open Finset Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean.RealBottomMinorProducts

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension RealTiedMinorScalar RealTiedMinorProduct
open RealTemperedCommutantReduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n q : ℕ} {degree : Fin q → ℕ}

abbrev Selection (n : ℕ) (degree : Fin q → ℕ) :=
  CompoundMinorProduct.Selection (Fin n) degree

/-- A matrix coefficient of a product of compound matrices on `GL_n(ℝ)`. -/
def coefficient (R C : Selection n degree) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ((CompoundMinorProduct.matrix degree (g : Matrix (Fin n) (Fin n) ℝ) R C : ℝ) : ℂ)

theorem coefficient_eq_prod (R C : Selection n degree) :
    coefficient R C = ∏ t, minorG (R t).val (C t).val := by
  funext g
  simp only [coefficient, CompoundMinorProduct.matrix, Finset.prod_apply, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro t _
  unfold CompoundMinorProduct.minor minorG
  rw [MatrixMinor.minor_eq (R t).property (C t).property]

theorem contMDiff_coefficient (R C : Selection n degree) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (coefficient R C) := by
  rw [coefficient_eq_prod]
  refine Finset.prod_induction _ (fun f => ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (fun _ _ => RealPrincipalSeriesDuality.contMDiff_mul_fun) contMDiff_const ?_
  exact fun t _ => contMDiff_minorG _ _

theorem coefficient_mem_kFiniteVectors (R C : Selection n degree) :
    coefficient R C ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
        (unitaryCompact ℝ n) := by
  rw [coefficient_eq_prod]
  classical
  have hOne : (1 : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
        (unitaryCompact ℝ n) := by
    rw [mem_kFiniteVectors_iff]
    have h : (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (1 : Langlands.GeneralLinear n ℝ → ℂ)) ⊆ {1} := by
      rintro _ ⟨k, rfl⟩
      rfl
    exact Submodule.finiteDimensional_of_le (Submodule.span_mono h)
  refine Finset.prod_induction _ _ ?_ hOne ?_
  · exact fun f h => mul_mem_kFiniteVectors
  · exact fun t _ => minorG_mem_kFiniteVectors _ _

theorem coefficient_mul (R C : Selection n degree) (g h : Langlands.GeneralLinear n ℝ) :
    coefficient R C (g * h) = ∑ D : Selection n degree, coefficient R D g * coefficient D C h := by
  let A : Matrix (Fin n) (Fin n) ℝ := g
  let B : Matrix (Fin n) (Fin n) ℝ := h
  have hMul : CompoundMinorProduct.matrix degree (A * B) =
      CompoundMinorProduct.matrix degree A * CompoundMinorProduct.matrix degree B :=
    (CompoundMinorProduct.matrixHom degree).map_mul A B
  have hEntry := congr_fun (congr_fun hMul R) C
  rw [Matrix.mul_apply] at hEntry
  simpa only [coefficient, Units.val_mul, Complex.ofReal_sum, Complex.ofReal_mul] using
    congrArg Complex.ofReal hEntry

/-- Differentiation in the right variable changes only the column configuration. -/
theorem rightDerivative_coefficient (R C : Selection n degree)
    (X : Matrix (Fin n) (Fin n) ℝ) (g : Langlands.GeneralLinear n ℝ) :
    rightDerivative (matrixModel ℝ n) X (coefficient R C) g =
      ∑ D : Selection n degree, coefficient R D g *
        rightDerivative (matrixModel ℝ n) X (coefficient D C) 1 := by
  have hProduct := hasDerivAt_mul_matrixExpUnit_smul
    ((contMDiff_coefficient R C).of_le (mod_cast le_top)) g X
  have hSum : HasDerivAt (fun s : ℝ => ∑ D : Selection n degree,
      coefficient R D g * coefficient D C (1 * matrixExpUnit n (s • X)))
      (∑ D : Selection n degree, coefficient R D g *
        rightDerivative (matrixModel ℝ n) X (coefficient D C) 1) 0 :=
    HasDerivAt.fun_sum fun D _ =>
      (hasDerivAt_mul_matrixExpUnit_smul
        ((contMDiff_coefficient D C).of_le (mod_cast le_top)) 1 X).const_mul _
  have hEq : (fun s : ℝ => coefficient R C (g * matrixExpUnit n (s • X))) =
      fun s => ∑ D : Selection n degree,
        coefficient R D g * coefficient D C (1 * matrixExpUnit n (s • X)) := by
    funext s
    rw [one_mul, coefficient_mul]
  rw [hEq] at hProduct
  exact hProduct.unique hSum

/-- The product of diagonal powers attached to the chosen row sets. -/
def diagonalFactor (R : Selection n degree) (a : Fin n → ℝˣ) : ℂ :=
  ∏ t, ∏ i ∈ (R t).val, ((a i : ℝ) : ℂ)

theorem coefficient_borel_mul (R C : Selection n degree)
    (hBottom : ∀ t, IsBottom (R t).val) (a : Fin n → ℝˣ)
    (u : upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ) :
    coefficient R C ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * g) =
      diagonalFactor R a * coefficient R C g := by
  simp only [coefficient_eq_prod, diagonalFactor, Finset.prod_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t _ => minorG_borel_mul (hBottom t) _ _ _ _

theorem sum_coefficient_sq (R : Selection n degree) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    ∑ C : Selection n degree, coefficient R C (Unitary.toUnits k) *
      coefficient R C (Unitary.toUnits k) = 1 := by
  have hOrthogonal : (k : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp k.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hTranspose (A : Matrix (Fin n) (Fin n) ℝ) (C : Selection n degree) :
      CompoundMinorProduct.matrix degree Aᵀ C R = CompoundMinorProduct.matrix degree A R C := by
    simp only [CompoundMinorProduct.matrix, CompoundMinorProduct.minor, ← Matrix.transpose_submatrix,
      Matrix.det_transpose]
  have h := congr_fun (congr_fun ((CompoundMinorProduct.matrixHom (R := ℝ) degree).map_mul
    (k : Matrix (Fin n) (Fin n) ℝ) (k : Matrix (Fin n) (Fin n) ℝ)ᵀ) R) R
  rw [hOrthogonal, map_one] at h
  let A : Matrix (Fin n) (Fin n) ℝ := k
  change (1 : Matrix (Selection n degree) (Selection n degree) ℝ) R R =
    (CompoundMinorProduct.matrix degree A * CompoundMinorProduct.matrix degree Aᵀ) R R at h
  rw [Matrix.one_apply_eq, Matrix.mul_apply] at h
  simp only [hTranspose] at h
  change (∑ C : Selection n degree,
    (↑(CompoundMinorProduct.matrix degree A R C) : ℂ) *
      (↑(CompoundMinorProduct.matrix degree A R C) : ℂ)) = 1
  simpa only [Complex.ofReal_one, Complex.ofReal_sum, Complex.ofReal_mul] using
    congrArg Complex.ofReal h.symm

section Multiplication

variable {ds es : List RealBlock}

/-- Multiply a source function by a product of bottom minors with the indicated character shift. -/
def multiply (hds : IsPrincipal ds) (hes : IsPrincipal es) (R C : Selection n degree)
    (hBottom : ∀ t, IsBottom (R t).val)
    (hShift : ∀ a : Fin n → ℝˣ,
      principalSeriesCharacter ℝ n (realPositionCharacter ds) a =
        principalSeriesCharacter ℝ n (realPositionCharacter es) a * diagonalFactor R a) :
    KF n es →ₗ[ℂ] KF n ds where
  toFun f := ⟨fun g => f.val g * coefficient R C g, by
    have hf := (mem_KF_iff hes _).mp f.property
    apply (mem_KF_iff hds _).mpr
    refine ⟨⟨RealPrincipalSeriesDuality.contMDiff_mul_fun hf.1.1 (contMDiff_coefficient R C),
      fun a u g => ?_⟩, mul_mem_kFiniteVectors hf.2 (coefficient_mem_kFiniteVectors R C)⟩
    change f.val _ * coefficient R C _ = _ * (f.val g * coefficient R C g)
    rw [hf.1.2 a u g, coefficient_borel_mul R C hBottom, hShift]
    ring⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    change (f.val g + h.val g) * _ = f.val g * _ + h.val g * _
    rw [add_mul]
  map_smul' a f := by
    apply Subtype.ext
    funext g
    change (a * f.val g) * _ = a * (f.val g * _)
    rw [mul_assoc]

variable (hds : IsPrincipal ds) (hes : IsPrincipal es) (R : Selection n degree)
  (hBottom : ∀ t, IsBottom (R t).val)
  (hShift : ∀ a : Fin n → ℝˣ,
    principalSeriesCharacter ℝ n (realPositionCharacter ds) a =
      principalSeriesCharacter ℝ n (realPositionCharacter es) a * diagonalFactor R a)

local notation "M" => fun C => multiply hds hes R C hBottom hShift

theorem multiply_lie (C : Selection n degree) (X : Matrix (Fin n) (Fin n) ℝ) (f : KF n es) :
    M C (realStandardLie n es (1 ⊗ₜ X) f) =
      realStandardLie n ds (1 ⊗ₜ X) (M C f) -
        ∑ D : Selection n degree, rightDerivative (matrixModel ℝ n) X (coefficient D C) 1 • M D f := by
  apply Subtype.ext
  funext g
  have hApply (D : Selection n degree) (v : KF n es) :
      (M D v).val = fun x => v.val x * coefficient R D x := rfl
  simp only [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply,
    realStandardLie_one_tmul_apply_coe, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hApply]
  rw [RealPrincipalSeriesDuality.rightDerivative_mul_fun
    (contMDiff_of_mem_realStandardModule f.2.1) (contMDiff_coefficient R C),
    rightDerivative_coefficient, Finset.mul_sum]
  have hTerm (D : Selection n degree) :
      f.val g * (coefficient R D g * rightDerivative (matrixModel ℝ n) X (coefficient D C) 1) =
        rightDerivative (matrixModel ℝ n) X (coefficient D C) 1 * (f.val g * coefficient R D g) := by
    ring
  simp only [hTerm, add_sub_cancel_right]

private theorem coefficient_sign_sq (a : Fin n → ℝˣ) :
    diagonalFactor R (fun i => signUnit (a i)) * diagonalFactor R (fun i => signUnit (a i)) = 1 := by
  simp only [diagonalFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun t _ => Finset.prod_eq_one fun i _ => ?_
  rw [← Complex.ofReal_mul, ← sq, signUnit_val]
  unfold signReal
  split_ifs <;> norm_num

private def compactProduct (f : KF n ds) (C : Selection n degree)
    (k : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  f.val (Unitary.toUnits k) * coefficient R C (Unitary.toUnits k)

private theorem finiteDimensional_compactProduct (f : KF n ds) (C : Selection n degree) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => compactProduct R f C (x * k))) := by
  apply finiteDimensional_translateSpan_mul
    (φ := fun k => f.val (Unitary.toUnits k))
    (ψ := fun k => coefficient R C (Unitary.toUnits k))
  · have hf : f.val ∈ kFiniteVectors (Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear n ℝ)) (unitaryCompact ℝ n) := f.2.2
    simpa only [map_mul] using finiteDimensional_restrict hf
  · simpa only [map_mul] using finiteDimensional_restrict (coefficient_mem_kFiniteVectors R C)

private def extract (f : KF n ds) (C : Selection n degree) : KF n es :=
  ⟨extension (shiftedExponent n (GramFormula.realPositionExponent es)) (compactProduct R f C), by
    apply (mem_KF_iff hes _).mpr
    refine extension_mem_kFiniteFunctions _ (RealStrictCharacterLanglandsQuotient.isSignedPower es).eq
      ((continuous_restrict (contMDiff_of_mem_realStandardModule f.2.1).continuous).mul
        (continuous_restrict (contMDiff_coefficient R C).continuous))
      (finiteDimensional_compactProduct R f C)
      (fun a k => ?_)
    have hDiag : Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * k) =
        (Iwasawa.diagonalUnits (fun i => signUnit (a i)) : Langlands.GeneralLinear n ℝ) *
          ((1 : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) * Unitary.toUnits k := by
      rw [map_mul, OneMemClass.coe_one, mul_one]
      congr 1
      apply Units.ext
      change Matrix.diagonal (fun i => signReal (a i : ℝ)) = _
      rw [Iwasawa.diagonalUnits_val]
      congr 1
      funext i
      rw [signUnit_val]
    rw [compactProduct, compactProduct, hDiag, (realStandardModule_le_principalSeries n ds f.2.1).2,
      coefficient_borel_mul R C hBottom, hShift]
    have hSquare := coefficient_sign_sq R a
    linear_combination
      (principalSeriesCharacter ℝ n (realPositionCharacter es) (fun i => signUnit (a i)) *
        f.val (Unitary.toUnits k) * coefficient R C (Unitary.toUnits k)) * hSquare⟩

theorem sum_multiply_extract (f : KF n ds) :
    ∑ C : Selection n degree, M C (extract hes R hBottom hShift f C) = f := by
  apply Subtype.ext
  have hSum := (mem_KF_iff hds _).mp (∑ C : Selection n degree,
    M C (extract hes R hBottom hShift f C)).property
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries hSum.1
    ((mem_KF_iff hds _).mp f.property).1 fun g hg => ?_
  let k : Matrix.unitaryGroup (Fin n) ℝ := ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩
  have hgk : g = Unitary.toUnits k := Units.ext rfl
  rw [hgk, Submodule.coe_sum, Finset.sum_apply]
  have hTerm (C : Selection n degree) :
      (M C (extract hes R hBottom hShift f C)).val (Unitary.toUnits k) =
        f.val (Unitary.toUnits k) * (coefficient R C (Unitary.toUnits k) *
          coefficient R C (Unitary.toUnits k)) := by
    change extension _ _ (Unitary.toUnits k) * _ = _
    rw [extension_unitary, compactProduct, mul_assoc]
  simp only [hTerm, ← Finset.mul_sum, sum_coefficient_sq, mul_one]

/-- If `T` generates the source principal series, its products with the indicated
bottom-minor coefficients generate the shifted principal series. -/
theorem eq_top_of_cyclic (T : KF n es)
    (hT : ∀ W : Submodule ℂ (KF n es), T ∈ W →
      (∀ Z, ∀ f ∈ W, realStandardLie n es Z f ∈ W) → W = ⊤)
    (W : Submodule ℂ (KF n ds))
    (hW : ∀ Z, ∀ f ∈ W, realStandardLie n ds Z f ∈ W)
    (hSeed : ∀ C, M C T ∈ W) :
    W = ⊤ := by
  let U : Submodule ℂ (KF n es) := ⨅ C, W.comap (M C)
  have hU {f : KF n es} : f ∈ U ↔ ∀ C, M C f ∈ W := by
    simp only [U, Submodule.mem_iInf, Submodule.mem_comap]
  have hStable (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (f : KF n es) (hf : f ∈ U) :
      realStandardLie n es Z f ∈ U := by
    induction Z with
    | tmul z X =>
        have heq : realStandardLie n es (z ⊗ₜ X) = z • realStandardLie n es (1 ⊗ₜ X) := by
          rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [heq, LinearMap.smul_apply]
        refine U.smul_mem z (hU.mpr fun C => ?_)
        rw [multiply_lie]
        exact W.sub_mem (hW _ _ (hU.mp hf C))
          (W.sum_mem fun D _ => W.smul_mem _ (hU.mp hf D))
    | add Y Z hY hZ =>
        rw [map_add, LinearMap.add_apply]
        exact U.add_mem hY hZ
  have hTop := hT U (hU.mpr hSeed) hStable
  refine eq_top_iff.2 fun f _ => ?_
  rw [← sum_multiply_extract hds hes R hBottom hShift f]
  exact W.sum_mem fun C _ =>
    hU.mp (hTop.symm ▸ Submodule.mem_top) C

end Multiplication

end Langlands.Archimedean.RealBottomMinorProducts
