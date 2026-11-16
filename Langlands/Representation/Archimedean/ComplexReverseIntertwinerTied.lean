import Langlands.Representation.Archimedean.ComplexReverseBlockRecursion
import Langlands.Representation.Archimedean.ComplexReverseIntertwinerStrict
import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof
import Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationProof

/-!
# Intertwiners to the reversed standard module: the Langlands-ordered case

Let `ds` be a Langlands-ordered list of `n` complex characters (weakly decreasing real parts of
the exponents) and `T` a `(𝔤, K)`-intertwiner from the `U(n)`-finite functions of the standard
module of `ds` to those of the standard module of `ds.reverse`. Assuming the block statements
`ComplexBlockChartIntegrableStatement`, `ComplexBlockParabolicIntegrationStatement` and the
tempered statement `ComplexTemperedStandardIrreducibleStatement`, `T` vanishes on every proper
`(𝔤, K)`-submodule `W` (`ComplexReverseIntertwinerTied.le_ker_of_isLanglandsOrdered`). The two
block statements are proved in the Library, so the final reduction
`complexReverseIntertwinerKernelReduction` assumes only the tempered statement.

Proof. Cut `ds` into maximal blocks of tied exponents (`ks`) and let `f₀` be a test vector with
nonzero block Jacquet functional `jac(f₀) ≠ 0`. Put `v = f₀ ∘ σ` with the twist
`σ(g) = w₀ (gᵀ)⁻¹`, and let `u` be its pairing transpose: `⟨u, h⟩ = ⟨v, T h⟩`. As in the strictly
ordered case, for `w ∈ W` and all `g`,
`∫ (T w ∘ σ)(κ g) f₀(κ) dκ = ∫ u(κ gᵀ) w(κ) dκ`.
The space `U = {T w ∘ σ : w ∈ W}` is `(𝔤, K)`-stable (the right derivative along `X` of a twisted
function is the twist of the right derivative along `-Xᵀ`, `rightDerivative_twistLin`), and `w`
is orthogonal to the annihilator of `W`, which is nonzero and `(𝔤, K)`-stable since `W` is
proper. The recursion along the blocks (`ComplexReverseBlockRecursion.mul_jac_eq_zero`) gives
`(T w)(w₀) · jac(f₀) = 0`, so `(T w)(w₀) = 0`; applied to the translates `R(w₀ k) w ∈ W` this
gives `T w = 0` on `U(n)`, hence `T w = 0`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace ComplexReverseIntertwinerTied

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexPartialJacquet
  ComplexReverseTwist ComplexStandardHomTransposeProof ComplexStrictLanglandsQuotient
  ComplexReverseIntertwinerStrict ComplexBlockFunctional ComplexBlockLanglandsQuotient
  ComplexReverseBlockRecursion ComplexGramFormula

/-! ## The right derivative of a twisted function -/

/-- **Right derivatives of twisted functions.** `R(X)(f ∘ σ) = (R(-Xᵀ) f) ∘ σ` for the twist
`σ(g) = w₀ (gᵀ)⁻¹` and smooth `f`. -/
theorem rightDerivative_twistLin {n : ℕ} {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin n) (Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (twistLin n f) g =
      rightDerivative (matrixModel ℂ n) (-Xᵀ) f (ComplexReverseTwist.twist g) := by
  rw [rightDerivative_eq_fderiv hf]
  set A : Matrix (Fin n) (Fin n) ℂ :=
    ((ComplexReverseTwist.twist g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) with hA
  set tr : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ((Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℂ).toContinuousLinearEquiv :
      Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) with htr
  set mA : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ) A with hmA
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  simp only [inv_one, Units.val_one] at hinv
  have hin : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => A * (Ring.inverse y)ᵀ)
      (mA.comp (tr.comp (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℂ) 1 1)))
      1 :=
    mA.hasFDerivAt.comp (1 : Matrix (Fin n) (Fin n) ℂ)
      (tr.hasFDerivAt.comp (1 : Matrix (Fin n) (Fin n) ℂ) hinv)
  have hval : A * (Ring.inverse (1 : Matrix (Fin n) (Fin n) ℂ))ᵀ = A := by
    rw [Ring.inverse_one, Matrix.transpose_one, Matrix.mul_one]
  have hout : HasFDerivAt (unitsExtension f) (fderiv ℝ (unitsExtension f) A)
      (A * (Ring.inverse (1 : Matrix (Fin n) (Fin n) ℂ))ᵀ) := by
    rw [hval]
    exact (differentiableAt_unitsExtension hf (Units.isUnit _)).hasFDerivAt
  have hψ := hout.comp (1 : Matrix (Fin n) (Fin n) ℂ) hin
  have hφ : ∀ h : Langlands.GeneralLinear n ℂ, twistLin n f (g * h) =
      unitsExtension f (A * (Ring.inverse (h : Matrix (Fin n) (Fin n) ℂ))ᵀ) := by
    intro h
    rw [twistLin_apply, Ring.inverse_unit, ComplexReverseTwist.twist_mul, hA, ← transposeGL_inv_val, ← conjAut_apply,
      ← Units.val_mul, unitsExtension_val]
  have h := mfderiv_eq_fderiv_of_eq_comp
    (φ := fun h => twistLin n f (g * h))
    (ψ := fun y : Matrix (Fin n) (Fin n) ℂ => unitsExtension f (A * (Ring.inverse y)ᵀ))
    hφ 1 (by rw [Units.val_one]; exact hψ.differentiableAt)
  have hX := congrArg (fun L => L X) h
  change rightDerivative (matrixModel ℂ n) X (twistLin n f) g =
    fderiv ℝ (unitsExtension f ∘ fun y : Matrix (Fin n) (Fin n) ℂ => A * (Ring.inverse y)ᵀ)
      1 X at hX
  rw [hψ.fderiv] at hX
  rw [hX]
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one, hmA, htr,
    ContinuousLinearMap.mul_apply', ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv', Matrix.transposeLinearEquiv_apply]
  rfl

/-! ## The Langlands-ordered case -/

/-- **Intertwiners to the reversed standard module, Langlands-ordered case.** Assume
`ComplexBlockChartIntegrableStatement`, `ComplexBlockParabolicIntegrationStatement` and
`ComplexTemperedStandardIrreducibleStatement`. Let `ds` be a Langlands-ordered list of `n` complex
characters, `T` a `(𝔤, K)`-intertwiner from the `U(n)`-finite functions of the standard module of
`ds` to those of the standard module of `ds.reverse`, and `W` a proper `(𝔤, K)`-submodule. Then
`W ≤ ker T`. -/
theorem le_ker_of_isLanglandsOrdered (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hU : ComplexTemperedStandardIrreducibleStatement) (n : ℕ) (ds : List ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n ds.reverse) (unitaryCompact ℂ n))
    (W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)))
    (hn : ds.length = n) (hord : IsComplexLanglandsOrdered ds)
    (hT : IsComplexStandardIntertwining n (complexStandardRep n ds.reverse)
      (complexStandardLie n ds.reverse) ds T)
    (hW : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W) (hW' : W ≠ ⊤) :
    W ≤ LinearMap.ker T := by
  have hχ := isPhasePower ds
  have hψ := isPhasePower ds.reverse
  have hp := complexPositionCharacter_phase ds
  have hdom : ∀ l : ℕ, l + 1 < n →
      (complexPositionExponent ds (l + 1)).re ≤ (complexPositionExponent ds l).re := by
    subst hn
    exact exponent_ordered hord
  obtain ⟨ks, hdim, hks⟩ := exists_blockOrdered n (complexPositionExponent ds) hdom
  subst hdim
  have hTK : ∀ (k : Matrix.unitaryGroup (Fin (dim ks)) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ (dim ks) (complexPositionCharacter ds))
        (unitaryCompact ℂ (dim ks))),
      T (principalSeriesRep ℂ (dim ks) (complexPositionCharacter ds) k f) =
        principalSeriesRep ℂ (dim ks) (complexPositionCharacter ds.reverse) k (T f) :=
    fun k f => map_complexStandardRep hT k f
  have hTX : ∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ (dim ks) (complexPositionCharacter ds))
        (unitaryCompact ℂ (dim ks))),
      T (principalSeriesLie ℂ (dim ks) (complexPositionCharacter ds) (1 ⊗ₜ X) f) =
        principalSeriesLie ℂ (dim ks) (complexPositionCharacter ds.reverse) (1 ⊗ₜ X) (T f) :=
    fun X f => map_complexStandardLie hT X f
  -- the characters of the twisted functions
  have hA : ∀ (j : Fin (dim ks)) (z : ℂˣ), dualChar (complexPositionCharacter ds.reverse) j z =
      complexPositionCharacter ds (Fin.rev j) z⁻¹ := by
    intro j z
    have h := complexPositionCharacter_reverse hn (Fin.rev j)
    rw [Fin.rev_rev] at h
    simp only [dualChar, h, complexPositionCharacter_inv]
  have hB : ∀ (j : Fin (dim ks)) (z : ℂˣ), dualChar (complexPositionCharacter ds) j z =
      complexPositionCharacter ds.reverse (Fin.rev j) z⁻¹ := by
    intro j z
    simp only [dualChar, complexPositionCharacter_reverse hn j, complexPositionCharacter_inv]
  -- `W` as a space of functions, and its annihilator
  have hWX : W.map (kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks))).subtype ≤
      kFiniteFunctions (principalSeries ℂ (dim ks) (complexPositionCharacter ds))
        (unitaryCompact ℂ (dim ks)) := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hWK : ∀ k ∈ unitaryCompact ℂ (dim ks), ∀ w ∈ W.map (kFiniteFunctions
      (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))).subtype,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℂ) k w ∈
        W.map (kFiniteFunctions (complexStandardModule (dim ks) ds)
          (unitaryCompact ℂ (dim ks))).subtype := by
    intro k hk _ hw
    obtain ⟨w, hwW, rfl⟩ := hw
    refine ⟨complexStandardRep (dim ks) ds ⟨(k : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ),
      hk⟩ w, hW.1 _ w hwW, ?_⟩
    change ((complexStandardRep (dim ks) ds _ w : kFiniteFunctions
      (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))) :
        Langlands.GeneralLinear (dim ks) ℂ → ℂ) = _
    rw [principalSeriesRep_apply_coe, ComplexReverseTransfer.toUnits_mk hk]
    rfl
  have hWD : ∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), ∀ w ∈ W.map (kFiniteFunctions
      (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))).subtype,
      rightDerivative (matrixModel ℂ (dim ks)) X w ∈ W.map (kFiniteFunctions
        (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks))).subtype := by
    intro X _ hw
    obtain ⟨w, hwW, rfl⟩ := hw
    exact ⟨complexStandardLie (dim ks) ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
      principalSeriesLie_one_tmul_apply_coe ℂ (dim ks) (complexPositionCharacter ds) X w⟩
  obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks)), g ∉ W := by
    by_contra hcon
    exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
  have hgW' : g ∉ W.map (kFiniteFunctions (complexStandardModule (dim ks) ds)
      (unitaryCompact ℂ (dim ks))).subtype := by
    rintro ⟨w, hwW, hw⟩
    apply hgW
    have : w = ⟨g, hgS⟩ := Subtype.ext hw
    rw [← this]
    exact hwW
  have horth : ∀ w ∈ W, IsOrthStable (dim ks) (complexPositionCharacter ds)
      (w : Langlands.GeneralLinear (dim ks) ℂ → ℂ) := fun w hw =>
    ⟨ComplexJacquetKernel.annihilator _ _ hWX, ComplexJacquetKernel.annihilator_le _ hWX,
      ComplexJacquetKernel.annihilator_rightTranslation _ hWX hWK,
      ComplexJacquetKernel.annihilator_rightDerivative hχ _ hWX hWD,
      ComplexJacquetKernel.annihilator_ne_bot hχ _ hWX hWK hgS hgW',
      fun _ hv => hv.2 _ ⟨w, hw, rfl⟩⟩
  -- a test vector with nonzero block Jacquet functional, and its twist
  obtain ⟨av, L, -, hne⟩ := ComplexBlockNonvanishing.exists_jac_testVector_ne_zero hT1 ks
    (complexPositionWeight ds) hχ hp hks
  have hf₀ := ComplexBlockNonvanishing.testVector_mem (n := dim ks) hχ hp av L
  generalize ComplexBlockNonvanishing.testVector (dim ks) (complexPositionExponent ds)
    (complexPositionWeight ds) av L = f₀ at hne hf₀
  set v : kFiniteFunctions (principalSeries ℂ (dim ks)
        (dualChar (complexPositionCharacter ds.reverse)))
      (unitaryCompact ℂ (dim ks)) := ⟨twistLin (dim ks) f₀, twistLin_mem_kFiniteFunctions hA hf₀⟩
    with hvdef
  obtain ⟨u, huv⟩ := ComplexReverseTransfer.exists_pairing_transpose hχ T hTK v
  -- the transposed identity of matrix coefficients
  have hM : ∀ w ∈ W, ∀ g : Langlands.GeneralLinear (dim ks) ℂ,
      ∫ κ, (u : Langlands.GeneralLinear (dim ks) ℂ → ℂ)
          ((κ : Langlands.GeneralLinear (dim ks) ℂ) * g) *
        (w : Langlands.GeneralLinear (dim ks) ℂ → ℂ) κ ∂ComplexDuality.unitaryHaar (dim ks) =
      ∫ κ, twistLin (dim ks) (T w : Langlands.GeneralLinear (dim ks) ℂ → ℂ)
          ((κ : Langlands.GeneralLinear (dim ks) ℂ) * transposeGL g) *
        f₀ κ ∂ComplexDuality.unitaryHaar (dim ks) := by
    intro w _ g
    have h1 := ComplexReverseTransfer.integral_mul_transfer hχ hψ T hTK hTX v u huv w g⁻¹
    have h2 := ComplexReverseRecursion.integral_mul_swap hχ w.2.1 u.2.1 g⁻¹
    have h3 := integral_mul_inv_eq_twist
      (ComplexDuality.continuous_of_mem_kFiniteFunctions (T w).2)
      (ComplexDuality.continuous_of_mem_kFiniteFunctions v.2) g
    rw [inv_inv] at h2
    rw [← h2, ← h1, h3]
    refine integral_congr_ae (ae_of_all _ fun κ => ?_)
    show (T w : Langlands.GeneralLinear (dim ks) ℂ → ℂ)
        (ComplexReverseTwist.twist ((κ : Langlands.GeneralLinear (dim ks) ℂ) * transposeGL g)) *
        f₀ (ComplexReverseTwist.twist
          (ComplexReverseTwist.twist (κ : Langlands.GeneralLinear (dim ks) ℂ))) =
      (T w : Langlands.GeneralLinear (dim ks) ℂ → ℂ)
        (ComplexReverseTwist.twist ((κ : Langlands.GeneralLinear (dim ks) ℂ) * transposeGL g)) *
          f₀ κ
    rw [ComplexReverseTwist.twist_twist]
  -- the twisted image of `W`
  set Φ : kFiniteFunctions (complexStandardModule (dim ks) ds) (unitaryCompact ℂ (dim ks)) →ₗ[ℂ]
      (Langlands.GeneralLinear (dim ks) ℂ → ℂ) :=
    (twistLin (dim ks)).comp ((kFiniteFunctions (complexStandardModule (dim ks) ds.reverse)
      (unitaryCompact ℂ (dim ks))).subtype.comp T) with hΦ
  have hΦapp : ∀ w, Φ w = twistLin (dim ks) (T w : Langlands.GeneralLinear (dim ks) ℂ → ℂ) :=
    fun w => rfl
  have hUle : W.map Φ ≤ kFiniteFunctions (principalSeries ℂ (dim ks)
      (dualChar (complexPositionCharacter ds))) (unitaryCompact ℂ (dim ks)) := by
    rintro _ ⟨w, -, rfl⟩
    rw [hΦapp]
    exact twistLin_mem_kFiniteFunctions hB (T w).2
  have hUK : ∀ κ ∈ unitaryCompact ℂ (dim ks), ∀ x ∈ W.map Φ,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℂ) κ x ∈ W.map Φ := by
    intro κ hκ _ hx
    obtain ⟨w, hwW, rfl⟩ := hx
    have hκ' := conjAut_mem hκ
    refine ⟨complexStandardRep (dim ks) ds ⟨((conjAut κ : Langlands.GeneralLinear (dim ks) ℂ) :
      Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), hκ'⟩ w, hW.1 _ w hwW, ?_⟩
    rw [hΦapp, hΦapp, rightTranslation_twistLin]
    congr 1
    rw [hTK, principalSeriesRep_apply_coe, ComplexReverseTransfer.toUnits_mk hκ']
  have hUD : ∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), ∀ x ∈ W.map Φ,
      rightDerivative (matrixModel ℂ (dim ks)) X x ∈ W.map Φ := by
    intro X _ hx
    obtain ⟨w, hwW, rfl⟩ := hx
    refine ⟨complexStandardLie (dim ks) ds (1 ⊗ₜ (-Xᵀ)) w, hW.2 _ w hwW, ?_⟩
    rw [hΦapp, hΦapp]
    funext y
    rw [rightDerivative_twistLin (T w).2.1.1, twistLin_apply]
    change ((T (principalSeriesLie ℂ (dim ks) (complexPositionCharacter ds) (1 ⊗ₜ (-Xᵀ)) w) :
      kFiniteFunctions (complexStandardModule (dim ks) ds.reverse) (unitaryCompact ℂ (dim ks))) :
        Langlands.GeneralLinear (dim ks) ℂ → ℂ) (ComplexReverseTwist.twist y) = _
    rw [hTX, principalSeriesLie_one_tmul_apply_coe]
  -- the transposed expansions
  have hexp : ∀ x ∈ W.map Φ, HasTransposeExpansion (dim ks) (complexPositionCharacter ds) x f₀ := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨Unit, inferInstance, fun _ => (u : Langlands.GeneralLinear (dim ks) ℂ → ℂ),
      fun _ => (w : Langlands.GeneralLinear (dim ks) ℂ → ℂ), fun _ => u.2, fun _ => w.2,
      fun _ => horth w hw, fun g => ?_⟩
    rw [Fintype.sum_unique, hΦapp]
    have h := hM w hw (transposeGL g)
    rw [transposeGL_transposeGL] at h
    exact h.symm
  have hrec := mul_jac_eq_zero hT1 hT3 (tiedIrreducible hU) ks (complexPositionWeight ds) hχ hp
    hks hUle hUK hUD hf₀ hexp
  -- `(T w)(w₀) = 0` for `w ∈ W`
  have hw0 : ∀ w ∈ W, (T w : Langlands.GeneralLinear (dim ks) ℂ → ℂ) (w0GL (dim ks)) = 0 := by
    intro w hw
    have h := hrec (Φ w) ⟨w, hw, rfl⟩
    rw [hΦapp, twistLin_apply, ComplexReverseTwist.twist_one] at h
    exact (mul_eq_zero.mp h).resolve_right hne
  intro w hw
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  refine ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn (T w).2.1 fun k hk => ?_
  have hk' : w0GL (dim ks) * k ∈ unitaryCompact ℂ (dim ks) := mul_mem w0GL_mem hk
  have h := hw0 _ (hW.1 ⟨((w0GL (dim ks) * k : Langlands.GeneralLinear (dim ks) ℂ) :
    Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), hk'⟩ w hw)
  rw [hTK, principalSeriesRep_apply_coe, ComplexReverseTransfer.toUnits_mk hk'] at h
  change (T w : Langlands.GeneralLinear (dim ks) ℂ → ℂ)
    (w0GL (dim ks) * (w0GL (dim ks) * k)) = 0 at h
  rwa [← mul_assoc, w0GL_mul_self, one_mul] at h

end ComplexReverseIntertwinerTied

/-- **Intertwiners to the reversed standard module from tempered irreducibility.** The statement
`ComplexTemperedStandardIrreducibleStatement` implies `ComplexReverseIntertwinerKernelStatement`.
The block statements `ComplexBlockChartIntegrableStatement` and
`ComplexBlockParabolicIntegrationStatement` used by the proof are discharged by the Library
theorems `complexBlockChartIntegrable` and `complexBlockParabolicIntegration`. -/
def ComplexReverseIntertwinerKernelReductionStatement : Prop :=
  ComplexTemperedStandardIrreducibleStatement → ComplexReverseIntertwinerKernelStatement

theorem complexReverseIntertwinerKernelReduction :
    ComplexReverseIntertwinerKernelReductionStatement :=
  fun hU n ds T W hn hord hT hW hW' =>
    ComplexReverseIntertwinerTied.le_ker_of_isLanglandsOrdered complexBlockChartIntegrable
      complexBlockParabolicIntegration hU n ds T W hn hord hT hW hW'

end Langlands.Archimedean
