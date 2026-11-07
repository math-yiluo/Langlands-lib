import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Complete valued fields are henselian

Conrad restricts attention to complete ground fields (printed p.14): the absolute value of a
complete nontrivially normed field extends uniquely to every algebraic extension. This module
proves `IsHenselianValuedField` for complete fields that are either non-archimedean or
isometrically embedded in `ℂ`.

Uniqueness holds for every complete field: two power-multiplicative algebra norms on an
algebraic extension are equivalent on each finite subextension, hence equal. Existence uses
the spectral norm in the non-archimedean case and an embedding of the extension into `ℂ` in the
archimedean case.
-/

noncomputable section

universe u v

open IntermediateField

namespace Langlands.AlgebraicGeometry.PointTopology

namespace CompleteHenselian

variable {K : Type u} [NontriviallyNormedField K]

/-- An absolute value extending the norm of `K` is a power-multiplicative `K`-algebra norm. -/
def toAlgebraNorm {L : Type v} [Field L] [Algebra K L] (f : AbsoluteValue L ℝ)
    (hf : ∀ x : K, f (algebraMap K L x) = ‖x‖) : AlgebraNorm K L :=
  { MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f with
    smul' k x := by
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
      rw [Algebra.smul_def, map_mul]
      congr
      rw [← hf k]
      rfl
    mul_le' x y := by simp [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] }

theorem toAlgebraNorm_apply {L : Type v} [Field L] [Algebra K L] (f : AbsoluteValue L ℝ)
    (hf : ∀ x : K, f (algebraMap K L x) = ‖x‖) (x : L) : toAlgebraNorm f hf x = f x := rfl

variable [CompleteSpace K]

set_option allowUnsafeReducibility true in
/-- Over a complete field, two power-multiplicative algebra norms on an algebraic extension
agree. The argument is Mathlib's proof of `spectralNorm_unique` with the spectral norm replaced
by an arbitrary power-multiplicative norm. -/
theorem algebraNorm_eq {L : Type v} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (f g : AlgebraNorm K L) (hf : IsPowMul f) (hg : IsPowMul g) : f = g := by
  apply eq_of_powMul_faithful f hf g hg
  intro x
  let E : Type v := id K⟮x⟯
  let : Field E := id <| show Field K⟮x⟯ by infer_instance
  let : Module K E := id <| show Module K K⟮x⟯ by infer_instance
  let id1 : K⟮x⟯ →ₗ[K] E := LinearMap.id
  let id2 : E →ₗ[K] K⟮x⟯ := LinearMap.id
  set hs_norm : RingNorm E :=
    { toFun y := g (id2 y : L)
      map_zero' := by simp [map_zero, ZeroMemClass.coe_zero]
      add_le' a b := map_add_le_add g _ _
      neg' a := by simp [map_neg, NegMemClass.coe_neg, map_neg_eq_map]
      mul_le' a b := map_mul_le_mul g _ _
      eq_zero_of_map_eq_zero' a ha := by
        simpa [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk,
          map_eq_zero_iff_eq_zero, ZeroMemClass.coe_eq_zero] using! ha }
  let n1 : NormedRing E := RingNorm.toNormedRing hs_norm
  let N1 : NormedSpace K E :=
    { one_smul e := by simp [one_smul]
      mul_smul k1 k2 e := by simp [mul_smul]
      smul_zero e := by simp
      smul_add k e_1 e_ := by simp [smul_add]
      add_smul k1 k2 e := by simp [add_smul]
      zero_smul e := by simp [zero_smul]
      norm_smul_le k y := by
        change (g (id2 (k • y) : L) : ℝ) ≤ ‖k‖ * g (id2 y : L)
        rw [map_smul, IntermediateField.coe_smul, map_smul_eq_mul] }
  set hf_norm : RingNorm K⟮x⟯ :=
    { toFun y := f ((algebraMap K⟮x⟯ L) y)
      map_zero' := map_zero _
      add_le' a b := map_add_le_add _ _ _
      neg' y := by simp [(algebraMap K⟮x⟯ L).map_neg y]
      mul_le' a b := map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' a ha := by
        simpa [map_eq_zero_iff_eq_zero, map_eq_zero] using! ha }
  let n2 : NormedRing K⟮x⟯ := RingNorm.toNormedRing hf_norm
  let N2 : NormedSpace K K⟮x⟯ :=
    { one_smul e := by simp [one_smul]
      mul_smul k1 k2 e := by simp [mul_smul]
      smul_zero e := by simp
      smul_add k e1 e2 := by simp [smul_add]
      add_smul k1 k2 e := by simp [add_smul]
      zero_smul e := by simp [zero_smul]
      norm_smul_le k y := by
        change (f ((algebraMap K⟮x⟯ L) (k • y)) : ℝ) ≤ ‖k‖ * f (algebraMap K⟮x⟯ L y)
        have : (algebraMap (↥K⟮x⟯) L) (k • y) = k • algebraMap (↥K⟮x⟯) L y := by
          simp [IntermediateField.algebraMap_apply]
        rw [this, map_smul_eq_mul] }
  have hKx_fin : FiniteDimensional K ↥K⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : FiniteDimensional K E := hKx_fin
  set Id1 : K⟮x⟯ →L[K] E := ⟨id1, id1.continuous_of_finiteDimensional⟩
  set Id2 : E →L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finiteDimensional⟩
  obtain ⟨C1, hC1_pos, hC1⟩ : ∃ C1 : ℝ, 0 < C1 ∧ ∀ y : K⟮x⟯, ‖id1 y‖ ≤ C1 * ‖y‖ :=
    Id1.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ : ∃ C2 : ℝ, 0 < C2 ∧ ∀ y : E, ‖id2 y‖ ≤ C2 * ‖y‖ :=
    Id2.isBoundedLinearMap.bound
  exact ⟨C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y ↦ hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y ↦ hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩

/-- **Uniqueness.** Over a complete field, two absolute values on an algebraic extension that
extend the norm agree. -/
theorem absoluteValue_eq {L : Type v} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (f g : AbsoluteValue L ℝ) (hf : ∀ x : K, f (algebraMap K L x) = ‖x‖)
    (hg : ∀ x : K, g (algebraMap K L x) = ‖x‖) : f = g := by
  have h := algebraNorm_eq (toAlgebraNorm f hf) (toAlgebraNorm g hg)
    (MulRingNorm.isPowMul (MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f))
    (MulRingNorm.isPowMul (MulRingNorm.mulRingNormEquivAbsoluteValue.invFun g))
  ext x
  rw [← toAlgebraNorm_apply f hf, ← toAlgebraNorm_apply g hg, h]

/-- **Complete non-archimedean fields are henselian.** The spectral norm provides the
extension. -/
theorem isHenselianValuedField_of_isUltrametricDist [IsUltrametricDist K] :
    IsHenselianValuedField K := by
  intro L _ _ _
  refine ⟨MulRingNorm.toAbsoluteValue (spectralMulAlgNorm K L).toMulRingNorm, ?_, ?_⟩
  · intro x
    exact spectralNorm_extends x
  · intro w hw
    exact absoluteValue_eq w _ hw (fun x => spectralNorm_extends x)

/-- **Complete fields isometrically embedded in `ℂ` are henselian.** An embedding of an
algebraic extension into `ℂ` provides the extension. -/
theorem isHenselianValuedField_of_isometry (φ : K →+* ℂ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) :
    IsHenselianValuedField K := by
  intro L _ _ _
  let : Algebra K ℂ := φ.toAlgebra
  let σ : L →ₐ[K] ℂ := IsAlgClosed.lift
  let w : AbsoluteValue L ℝ :=
    { toFun := fun y => ‖σ y‖
      map_mul' := fun a b => by simp only [map_mul, norm_mul]
      nonneg' := fun _ => norm_nonneg _
      eq_zero' := fun y => by
        rw [norm_eq_zero]
        exact map_eq_zero_iff σ σ.toRingHom.injective
      add_le' := fun a b => by
        simp only [map_add]
        exact norm_add_le _ _ }
  have hw : ∀ x : K, w (algebraMap K L x) = ‖x‖ := by
    intro x
    change ‖σ (algebraMap K L x)‖ = ‖x‖
    rw [σ.commutes]
    exact hφ x
  exact ⟨w, hw, fun w' hw' => absoluteValue_eq w' w hw' hw⟩

end CompleteHenselian

end Langlands.AlgebraicGeometry.PointTopology
