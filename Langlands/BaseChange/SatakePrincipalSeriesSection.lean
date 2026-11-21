import Langlands.BaseChange.UnramifiedHecke
import Langlands.Representation.Unramified.PrincipalSeriesHecke
import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof

/-! The Satake character as integration against the normalized spherical section. -/

noncomputable section

namespace Langlands.BaseChange

open Filter MeasureTheory Langlands.Correspondence Langlands.GeneralLinear
open Langlands.Unramified Langlands.Unramified.SphericalExistence

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {r : ℕ} (z : Fin (r + 1) → ℂˣ)

private theorem exists_normalized_principalSeries_vector :
    ∃ v : fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r),
      evalAt F z 1 v.val = sphericalTensor r := by
  obtain ⟨v, hv, hvK⟩ := exists_fixed_smoothFunction ((borelShape r).parabolic F.Carrier)
    (borelInducing F z) (sphericalOpenSubgroup F r) (exists_borel_mul_spherical F)
    (sphericalTensor r) (borelInducing_sphericalTensor F z)
  exact ⟨⟨v, hvK⟩, hv⟩

private def normalizedPrincipalSeriesVector :
    fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r) :=
  (exists_normalized_principalSeries_vector F z).choose

private theorem eval_normalizedPrincipalSeriesVector_one :
    evalAt F z 1 (normalizedPrincipalSeriesVector F z).val = sphericalTensor r :=
  (exists_normalized_principalSeries_vector F z).choose_spec

private def scalarEvalAt (g : GeneralLinear (r + 1) F.Carrier) :
    Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier) (borelInducing F z) →ₗ[ℂ] ℂ :=
  (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra ℂ (Fin (borelShape r).length) ℂ)).comp
    (evalAt F z g)

/-- The scalar section of the ordered normalized principal series whose value at
the identity is one and which is fixed by the standard compact subgroup on the right. -/
def sphericalPrincipalSeriesSection (g : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  scalarEvalAt F z g (normalizedPrincipalSeriesVector F z).val

@[simp] theorem sphericalPrincipalSeriesSection_one :
    sphericalPrincipalSeriesSection F z 1 = 1 := by
  simp only [sphericalPrincipalSeriesSection, scalarEvalAt, LinearMap.comp_apply,
    eval_normalizedPrincipalSeriesVector_one, sphericalTensor, PiTensorProduct.lift.tprod,
    MultilinearMap.mkPiAlgebra_apply, Finset.prod_const_one]

theorem sphericalPrincipalSeriesSection_rightInvariant (g : GeneralLinear (r + 1) F.Carrier)
    (k : sphericalOpenSubgroup F r) :
    sphericalPrincipalSeriesSection F z (g * k.val) =
      sphericalPrincipalSeriesSection F z g := by
  let v := normalizedPrincipalSeriesVector F z
  have hk : principalSeriesOfTuple F z k.val v.val = v.val := v.property k
  have he := congrArg (scalarEvalAt F z g) hk
  simpa only [scalarEvalAt, LinearMap.comp_apply, evalAt_apply, eval_principalSeriesOfTuple,
    sphericalPrincipalSeriesSection, v] using he

theorem isLocallyConstant_sphericalPrincipalSeriesSection :
    IsLocallyConstant (sphericalPrincipalSeriesSection F z) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hcont : Continuous (fun y : GeneralLinear (r + 1) F.Carrier => g⁻¹ * y) :=
    continuous_const.mul continuous_id
  have hK : {y | g⁻¹ * y ∈ sphericalOpenSubgroup F r} ∈ nhds g :=
    ((sphericalOpenSubgroup F r).isOpen.preimage hcont).mem_nhds (by simp)
  filter_upwards [hK] with y hy
  simpa only [mul_inv_cancel_left] using
    sphericalPrincipalSeriesSection_rightInvariant F z g ⟨g⁻¹ * y, hy⟩

/-- On the upper Borel, the section is the inducing character times the
normalized positive half modulus. -/
theorem sphericalPrincipalSeriesSection_borel (b : (borelShape r).parabolic F.Carrier) :
    sphericalPrincipalSeriesSection F z b.val =
      (F.canonicalTopologicalData.parabolicHalfModulus (borelShape r) b : ℂ) *
        ∏ i : Fin (r + 1), (character F (z i)
          (GeneralLinear.determinant ((borelShape r).leviProjection F.Carrier b i)) : ℂ) := by
  let v := normalizedPrincipalSeriesVector F z
  have hv := F.canonicalTopologicalData.normalizedProductInduced_covariant (borelShape r)
    (blockCharacters F z) v.val b 1
  rw [mul_one] at hv
  have hv₁ : Induction.eval _ _ v.val 1 = sphericalTensor r :=
    eval_normalizedPrincipalSeriesVector_one F z
  rw [hv₁] at hv
  unfold sphericalPrincipalSeriesSection scalarEvalAt
  rw [LinearMap.comp_apply, evalAt_apply]
  change PiTensorProduct.lift _ (Induction.eval _ _ v.val b.val) = _
  rw [hv, map_smul, sphericalTensor, BlockShape.blockTensor_tprod,
    PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply, smul_eq_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  change ((character F (z i)
      (GeneralLinear.determinant ((borelShape r).leviProjection F.Carrier b i)) : ℂ) * 1) = _
  exact mul_one _

private theorem sphericalAlgHom_eq_of_standard {A : Type*} [Ring A] [Algebra ℂ A]
    (C D : SphericalHeckeAlgebra F r →ₐ[ℂ] A)
    (hStd : ∀ i, C (standardHeckeElement F r i) = D (standardHeckeElement F r i))
    (f : SphericalHeckeAlgebra F r) : C f = D f := by
  have hGen : Set.EqOn C D (Algebra.adjoin ℂ (Set.range (standardHeckeElement F r))) := by
    rw [AlgHom.eqOn_adjoin_iff]
    rintro _ ⟨i, rfl⟩
    exact hStd i
  obtain ⟨n, hn⟩ := sphericalHeckeGeneration p F r f
  let T := standardHeckeElement F r (Fin.last (r + 1))
  have hT : C T = D T := hStd _
  have hTf : C (T ^ n * f) = D (T ^ n * f) := hGen hn
  rw [map_mul C, map_mul D, map_pow C, map_pow D, hT] at hTf
  have hUnit : IsUnit (D T ^ n) := (((standardHeckeElement_last_isUnit F r).map D).pow n)
  exact hUnit.mul_right_injective hTf

set_option maxHeartbeats 600000 in
private theorem principalSeries_cornerAction_eq
    (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ) (hω : IsSatakeCharacter F r (Eigenvalues.ofTuple z) ω)
    (f : SphericalHeckeAlgebra F r) :
    Hecke.cornerAction (sphericalHaar F r) (principalSeriesOfTuple F z)
        (isSmooth_principalSeriesOfTuple F z) (sphericalOpenSubgroup F r)
        (sphericalOpenSubgroup_isCompact F r) f = algebraMap ℂ _ (ω f) := by
  let C := Hecke.cornerAction (sphericalHaar F r) (principalSeriesOfTuple F z)
    (isSmooth_principalSeriesOfTuple F z) (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r)
  let D := (Algebra.ofId ℂ (Module.End ℂ
    (fixedVectors (principalSeriesOfTuple F z) (sphericalOpenSubgroup F r).toSubgroup))).comp ω
  change C f = D f
  have hStd (i : Fin (r + 2)) : C (standardHeckeElement F r i) = D (standardHeckeElement F r i) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (C (standardHeckeElement F r i) v).val = ω (standardHeckeElement F r i) • v.val
    rw [hω i]
    exact (standardHecke_cornerAction_eq_sum F (principalSeriesOfTuple F z)
      (isSmooth_principalSeriesOfTuple F z) i v).trans (principalSeries_sum_labelledRep F z i v)
  exact sphericalAlgHom_eq_of_standard (r := r) (A := Module.End ℂ
    (fixedVectors (principalSeriesOfTuple F z) (sphericalOpenSubgroup F r).toSubgroup))
    F C D hStd f

/-- Evaluation of a spherical Hecke function at a Satake tuple is the
integral of the function against the normalized spherical section. -/
theorem satakeCharacter_eq_integral_sphericalPrincipalSeriesSection
    (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ) (hω : IsSatakeCharacter F r (Eigenvalues.ofTuple z) ω)
    (f : SphericalHeckeAlgebra F r) :
    ω f = ∫ g, f g * sphericalPrincipalSeriesSection F z g ∂(sphericalHaar F r) := by
  let v := normalizedPrincipalSeriesVector F z
  let f₀ := (Hecke.HeckeAlgebra.Corner.toBiInvariant (sphericalHaar F r)
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) f).val
  let ev (A : Module.End ℂ
      (fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r))) : ℂ :=
    scalarEvalAt F z 1 (A v).val
  have h := congrArg ev (principalSeries_cornerAction_eq F z ω hω f)
  change scalarEvalAt F z 1 (Hecke.integratedAction (sphericalHaar F r)
    (principalSeriesOfTuple F z) (isSmooth_principalSeriesOfTuple F z) f₀ v.val) =
      scalarEvalAt F z 1 (ω f • v.val) at h
  rw [map_smul, smul_eq_mul,
    show scalarEvalAt F z 1 v.val = 1 from sphericalPrincipalSeriesSection_one F z,
    mul_one, Hecke.integratedAction_dual] at h
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun g => by
    simp only [scalarEvalAt, LinearMap.comp_apply, evalAt_apply, eval_principalSeriesOfTuple,
      one_mul, sphericalPrincipalSeriesSection, v]
    rfl

theorem integrable_mul_sphericalPrincipalSeriesSection (f : SphericalHeckeAlgebra F r) :
    Integrable (fun g => f g * sphericalPrincipalSeriesSection F z g) (sphericalHaar F r) := by
  let f₀ := (Hecke.HeckeAlgebra.Corner.toBiInvariant (sphericalHaar F r)
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) f).val
  have hcont := f₀.continuous.mul (isLocallyConstant_sphericalPrincipalSeriesSection F z).continuous
  exact hcont.integrable_of_hasCompactSupport f₀.hasCompactSupport.mul_right

end Langlands.BaseChange
