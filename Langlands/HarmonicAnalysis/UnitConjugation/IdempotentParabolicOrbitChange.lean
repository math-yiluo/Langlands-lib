import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizerDescent
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicGroup
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Change of variables along the upper-corner conjugation

For an ambient-regular Levi element, the adjoint action on the upper corner is
invertible. Its pushforward of additive Haar measure is unchanged throughout the
Levi conjugacy class. This supplies the unipotent change of variables in orbital descent.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open Function MeasureTheory
open scoped NNReal

universe u v

section Algebra

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

private theorem cornerProjection_levi_mul (a b : Levi) (z : A) :
    cornerProjection F e ((a : A) * z * (b : A)) =
      (a : A) * cornerProjection F e z * (b : A) := by
  have ha := (mem_centralizer_singleton_iff F).1 a.property
  have hb : (b : A) * (1 - e) = (1 - e) * (b : A) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, (mem_centralizer_singleton_iff F).1 b.property]
  calc
    _ = (e * (a : A)) * z * ((b : A) * (1 - e)) := by
      simp only [cornerProjection_apply, mul_assoc]
    _ = ((a : A) * e) * z * ((1 - e) * (b : A)) := by rw [ha, hb]
    _ = _ := by simp only [cornerProjection_apply, mul_assoc]

private def leviMulLeftRight (a b : Levi) : Module.End F Upper where
  toFun z := ⟨(a : A) * (z : A) * (b : A), by
    obtain ⟨w, hw⟩ := z.property
    exact ⟨(a : A) * w * (b : A), by rw [cornerProjection_levi_mul, hw]⟩⟩
  map_add' z w := Subtype.ext (by
    change (a : A) * ((z : A) + (w : A)) * (b : A) =
      (a : A) * (z : A) * (b : A) + (a : A) * (w : A) * (b : A)
    rw [mul_add, add_mul])
  map_smul' c z := Subtype.ext (by
    change (a : A) * (c • (z : A)) * (b : A) = c • ((a : A) * (z : A) * (b : A))
    rw [mul_smul_comm, smul_mul_assoc])

/-- The adjoint action `Z ↦ Y Z - Z Y`, restricted to the upper corner. -/
def upperCornerAdjoint (y : Levi) : Module.End F Upper :=
  leviMulLeftRight F y 1 - leviMulLeftRight F 1 y

theorem upperCornerAdjoint_apply (y : Levi) (z : Upper) :
    (upperCornerAdjoint F y z : A) = (y : A) * (z : A) - (z : A) * (y : A) := by
  change (y : A) * (z : A) * 1 - 1 * (z : A) * (y : A) = _
  rw [mul_one, one_mul]

private theorem upperCorner_mem_offDiagonal (he : IsIdempotentElem e) {z : A} (hz : z ∈ Upper) :
    z ∈ offDiagonal F e := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨_, h₂, _, _, _, h₆, _, _⟩ := idempotent_mul_rules he
  simp only [mem_offDiagonal_iff, diagonalProjection_apply, cornerProjection_apply,
    mul_assoc, h₂, mul_zero, h₆, zero_mul, add_zero]

/-- An ambient-regular Levi element acts invertibly on the upper corner. -/
theorem upperCornerAdjoint_bijective_of_mem_regularSet [Infinite F] [FiniteDimensional F A]
    (he : IsIdempotentElem e) (x : Levi) (hx : (x : A) ∈ regularSet F A) :
    Bijective (upperCornerAdjoint F x) := by
  have hOff := (offDiagonalAdjoint_bijective_of_mem_regularSet he x hx).1
  have hInj : Injective (upperCornerAdjoint F x) := by
    intro z w hzw
    have h : offDiagonalAdjoint F e x ⟨(z : A), upperCorner_mem_offDiagonal F he z.property⟩ =
        offDiagonalAdjoint F e x ⟨(w : A), upperCorner_mem_offDiagonal F he w.property⟩ := by
      apply Subtype.ext
      simpa only [offDiagonalAdjoint_apply, upperCornerAdjoint_apply] using congrArg Subtype.val hzw
    exact Subtype.ext (congrArg (fun q : offDiagonal F e => q.val) (hOff h))
  exact ⟨hInj, LinearMap.injective_iff_surjective.mp hInj⟩

private theorem levi_mul_inv (m : Leviˣ) :
    (m.val : A) * ((m⁻¹ : Leviˣ).val : A) = 1 :=
  congrArg Subtype.val m.mul_inv

/-- Conjugation `Z ↦ m⁻¹ Z m` on the upper corner by a Levi unit. -/
def upperCornerConj (m : Leviˣ) : Upper ≃ₗ[F] Upper where
  __ := leviMulLeftRight F (m⁻¹ : Leviˣ).val m.val
  invFun := leviMulLeftRight F m.val (m⁻¹ : Leviˣ).val
  left_inv z := by
    apply Subtype.ext
    change (m.val : A) * (((m⁻¹ : Leviˣ).val : A) * (z : A) * (m.val : A)) *
      ((m⁻¹ : Leviˣ).val : A) = (z : A)
    calc
      _ = ((m.val : A) * ((m⁻¹ : Leviˣ).val : A)) * (z : A) *
          ((m.val : A) * ((m⁻¹ : Leviˣ).val : A)) := by noncomm_ring
      _ = _ := by rw [levi_mul_inv F m, one_mul, mul_one]
  right_inv z := by
    apply Subtype.ext
    change ((m⁻¹ : Leviˣ).val : A) * ((m.val : A) * (z : A) * ((m⁻¹ : Leviˣ).val : A)) *
      (m.val : A) = (z : A)
    have hm : ((m⁻¹ : Leviˣ).val : A) * (m.val : A) = 1 := congrArg Subtype.val m.inv_mul
    calc
      _ = (((m⁻¹ : Leviˣ).val : A) * (m.val : A)) * (z : A) *
          (((m⁻¹ : Leviˣ).val : A) * (m.val : A)) := by noncomm_ring
      _ = _ := by rw [hm, one_mul, mul_one]

theorem upperCornerAdjoint_conjugate (m : Leviˣ) (x : Levi) :
    (upperCornerAdjoint F ((m⁻¹ : Leviˣ).val * x * m.val) : Upper → Upper) =
      (upperCornerConj F m) ∘ (upperCornerAdjoint F x) ∘ (upperCornerConj F m).symm := by
  funext z
  apply Subtype.ext
  let a : A := (m.val : A)
  let b : A := ((m⁻¹ : Leviˣ).val : A)
  have hm : b * a = 1 := congrArg Subtype.val m.inv_mul
  rw [Function.comp_apply, Function.comp_apply, upperCornerAdjoint_apply]
  change b * (x : A) * a * (z : A) - (z : A) * (b * (x : A) * a) =
    b * (upperCornerAdjoint F x ((upperCornerConj F m).symm z) : A) * a
  rw [upperCornerAdjoint_apply]
  change _ = b * ((x : A) * (a * (z : A) * b) - (a * (z : A) * b) * (x : A)) * a
  symm
  calc
    _ = (b * (x : A) * a) * (z : A) * (b * a) -
        (b * a) * (z : A) * (b * (x : A) * a) := by noncomm_ring
    _ = _ := by rw [hm, mul_one, one_mul]

end Algebra

section Analytic

variable (F : Type u) [NontriviallyNormedField F] [ProperSpace F]
  {A : Type v} [NormedRing A] [NormedAlgebra F A] [FiniteDimensional F A]
  [MeasurableSpace A] [BorelSpace A] (e : A)

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

/-- Along the Levi conjugacy class of an ambient-regular element, one additive Haar
measure on the upper corner gives the affine change of variables for conjugation by `1+Z`. -/
def IdempotentParabolicOrbitChangeStatement : Prop :=
  ∀ (he : IsIdempotentElem e) (x : Levi), (x : A) ∈ regularSet F A →
    ∀ (μ : Measure Upper) [μ.IsAddHaarMeasure],
      ∃ ν : Measure Upper, ν.IsAddHaarMeasure ∧ ∀ m : Leviˣ,
        let y := (m⁻¹ : Leviˣ).val * x * m.val
        μ.map (upperCornerAdjoint F y) = ν ∧
        ∀ f : A → ℂ, Measurable f →
          (∫ z : Upper, f ((((upperCornerUnit F he z)⁻¹ : Aˣ) : A) *
            (y : A) * (upperCornerUnit F he z : A)) ∂μ) =
            ∫ z : Upper, f ((y : A) + (z : A)) ∂ν

theorem idempotentParabolicOrbitChange : IdempotentParabolicOrbitChangeStatement F e := by
  intro he x hx μ _
  have : ProperSpace Upper := FiniteDimensional.proper F Upper
  let L := LinearMap.toContinuousLinearMap (upperCornerAdjoint F x)
  let ν := μ.map L
  let E := (LinearEquiv.ofBijective (upperCornerAdjoint F x)
    (upperCornerAdjoint_bijective_of_mem_regularSet F he x hx)).toContinuousLinearEquiv
  have : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  let c := Measure.addHaarScalarFactor ν μ
  have hc : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  refine ⟨ν, inferInstance, fun m => ?_⟩
  let y : Levi := (m⁻¹ : Leviˣ).val * x * m.val
  let C := (upperCornerConj F m).toContinuousLinearEquiv
  have hC : Measurable C := C.continuous.measurable
  have hCi : Measurable C.symm := C.symm.continuous.measurable
  have hL : Measurable L := L.continuous.measurable
  have : (μ.map C.symm).IsAddHaarMeasure := C.symm.isAddHaarMeasure_map μ
  have hCiScale := Measure.isAddLeftInvariant_eq_smul (μ.map C.symm) μ
  have hmap : μ.map (upperCornerAdjoint F y) = ν := by
    calc
      _ = ((μ.map C.symm).map L).map C := by
        rw [Measure.map_map hL hCi, Measure.map_map hC (hL.comp hCi)]
        exact congrArg (Measure.map · μ) (upperCornerAdjoint_conjugate F m x)
      _ = (c • μ.map C.symm).map C := by
        congr 1
        rw [hCiScale, Measure.map_smul _ hL.aemeasurable,
          show μ.map L = ν from rfl, hc, smul_comm]
      _ = c • μ := by
        have hInv : (C : Upper → Upper) ∘ C.symm = id := funext C.apply_symm_apply
        rw [Measure.map_smul _ hC.aemeasurable, Measure.map_map hC hCi, hInv, Measure.map_id]
      _ = ν := hc.symm
  refine ⟨hmap, fun f hf => ?_⟩
  let G : Upper → ℂ := fun z => f ((y : A) + (z : A))
  have hG : Measurable G := hf.comp (continuous_const.add continuous_subtype_val).measurable
  have hY : Measurable (upperCornerAdjoint F y) :=
    (LinearMap.toContinuousLinearMap (upperCornerAdjoint F y)).continuous.measurable
  calc
    _ = ∫ z : Upper, G (upperCornerAdjoint F y z) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        simp only [G, y, upperCornerUnit_inv_conj, upperCornerAdjoint_apply])
    _ = _ := by
      rw [← hmap]
      exact (integral_map hY.aemeasurable hG.aestronglyMeasurable).symm

end Analytic

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
