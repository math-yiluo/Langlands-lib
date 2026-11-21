import Langlands.Global.RankinSelberg.RealGodementOpenCellCovariance
import Langlands.Group.GL.UpperBruhatCoordinatesProof

/-! # A right Haar measure of the real upper triangular group -/

noncomputable section

open MeasureTheory Measure Set Topology TopologicalSpace Langlands.GeneralLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBorelRightHaar

open UpperBruhatCoordinates

variable {r : ℕ}
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "T" => Fin (r + 1) → ℝˣ
local notation "D" => Iwasawa.diagonalUnits (m := r + 1) (F := ℝ)

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩
local instance : MeasurableSpace (ℝˣ) := borel _
local instance : BorelSpace (ℝˣ) := ⟨rfl⟩
local instance : LocallyCompactSpace (ℝˣ) := by
  have hrange : range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
    ext x
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  have hopen : IsOpen (range (Units.val : ℝˣ → ℝ)) := hrange ▸ isOpen_compl_singleton
  exact (IsOpenEmbedding.mk Units.isEmbedding_val₀ hopen).locallyCompactSpace
local instance : SecondCountableTopology (ℝˣ) :=
  (show IsEmbedding (Units.val : ℝˣ → ℝ) from
    Units.isEmbedding_val₀).isInducing.secondCountableTopology
local instance : SecondCountableTopology U :=
  (upperEntryCoordinates (r + 1) (K := ℝ)).secondCountableTopology
local instance : LocallyCompactSpace U :=
  (upperEntryCoordinates (r + 1) (K := ℝ)).isClosedEmbedding.locallyCompactSpace

/-- Torus and unipotent coordinates in the order `(d,u) ↦ u d`. -/
def torusUnipotentHomeomorph : (T × U) ≃ₜ B :=
  (Homeomorph.prodComm T U).trans (torusSplit (Equiv.refl (Fin (r + 1))))

theorem torusUnipotentHomeomorph_val (z : T × U) :
    (torusUnipotentHomeomorph z).val = z.2.val * D z.1 := rfl

local instance : SecondCountableTopology B :=
  (torusUnipotentHomeomorph (r := r)).symm.secondCountableTopology

private def conjugateUnipotent (d : T) (u : U) : U :=
  ⟨D d * u.val * D d⁻¹, by
    apply (mem_upperUnipotent_iff _ _ _).mpr
    constructor
    · intro i j hij
      change ((D d * u.val * D d⁻¹).val) i j = 0
      simp only [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
        u.property.1 hij, mul_zero, zero_mul]
    · intro i
      change ((D d * u.val * D d⁻¹).val) i i = 1
      simp only [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
        u.property.2 i, mul_one, Pi.inv_apply, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ (d i).ne_zero]⟩

private theorem continuous_conjugateUnipotent :
    Continuous (fun z : T × U => conjugateUnipotent z.1 z.2) := by
  have hD := continuous_diagonalUnits (r + 1) (K := ℝ)
  exact (((hD.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
    (hD.comp continuous_fst.inv)).subtype_mk _

private def torusHaar : Measure T := Measure.haar
private instance : IsHaarMeasure (torusHaar (r := r)) :=
  inferInstanceAs (IsHaarMeasure (Measure.haar (G := T)))
private def unipotentHaar : Measure U := RealGodement.upperStepHaar r 1
private instance : IsHaarMeasure (unipotentHaar (r := r)) := RealGodement.upperStepHaar_isHaar r 1
private instance : IsMulRightInvariant (unipotentHaar (r := r)) :=
  RealGodement.upperStepHaar_isMulRightInvariant r 1

/-- The product of torus Haar and upper-entry Haar in right Borel coordinates. -/
def rightBorelMeasure (r : ℕ) : Measure (upperTriangularSubgroup (r + 1) ℝ) :=
  ((torusHaar (r := r)).prod (unipotentHaar (r := r))).map (torusUnipotentHomeomorph (r := r))

instance rightBorelMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (rightBorelMeasure r) :=
  IsFiniteMeasureOnCompacts.map (torusHaar.prod unipotentHaar) (torusUnipotentHomeomorph (r := r))

instance rightBorelMeasure_isOpenPosMeasure : IsOpenPosMeasure (rightBorelMeasure r) := by
  let e := torusUnipotentHomeomorph (r := r)
  exact e.continuous.isOpenPosMeasure_map e.surjective

instance rightBorelMeasure_isMulRightInvariant : IsMulRightInvariant (rightBorelMeasure r) := by
  let e := torusUnipotentHomeomorph (r := r)
  refine ⟨fun b₀ => ?_⟩
  obtain ⟨⟨d₀, u₀⟩, rfl⟩ := e.surjective b₀
  let Q (d : T) (u : U) := u * conjugateUnipotent d u₀
  let R (z : T × U) : T × U := (z.1 * d₀, Q z.1 z.2)
  have hm : Measurable (Function.uncurry Q) :=
    (continuous_snd.mul (continuous_conjugateUnipotent.comp
      (continuous_fst.prodMk continuous_const))).measurable
  have hp : MeasurePreserving R (torusHaar.prod unipotentHaar) (torusHaar.prod unipotentHaar) :=
    MeasurePreserving.skew_product (measurePreserving_mul_right torusHaar d₀) hm
      (Filter.Eventually.of_forall fun d => map_mul_right_eq_self unipotentHaar (conjugateUnipotent d u₀))
  have hcomp : (fun b => b * e (d₀, u₀)) ∘ e = e ∘ R := by
    funext z
    apply Subtype.ext
    simp only [Function.comp_apply, e, Subgroup.coe_mul, torusUnipotentHomeomorph_val, R, Q]
    change (z.2.val * D z.1) * (u₀.val * D d₀) =
      (z.2.val * (D z.1 * u₀.val * D z.1⁻¹)) * D (z.1 * d₀)
    rw [map_mul, map_inv]
    group
  change Measure.map (fun b => b * e (d₀, u₀)) (Measure.map e _) = Measure.map e _
  rw [Measure.map_map (measurable_mul_const _) e.continuous.measurable, hcomp,
    ← Measure.map_map e.continuous.measurable hp.measurable, hp.map_eq]

/-- The inclusion of the upper unipotent group in the upper triangular group. -/
def unipotentInBorel : U →* B := upperUnipotentInUpperTriangular _ _

theorem map_left_unipotent_rightBorelMeasure (u₀ : U) :
    Measure.map (unipotentInBorel u₀ * ·) (rightBorelMeasure r) = rightBorelMeasure r := by
  let e := torusUnipotentHomeomorph (r := r)
  let L (z : T × U) : T × U := (z.1, u₀ * z.2)
  have hp : MeasurePreserving L (torusHaar.prod unipotentHaar) (torusHaar.prod unipotentHaar) :=
    (MeasurePreserving.id torusHaar).prod (measurePreserving_mul_left unipotentHaar u₀)
  have hcomp : (unipotentInBorel u₀ * ·) ∘ e = e ∘ L := by
    funext z
    apply Subtype.ext
    change u₀.val * (e z).val = (e (z.1, u₀ * z.2)).val
    simp only [e, torusUnipotentHomeomorph_val, Subgroup.coe_mul, mul_assoc]
  change Measure.map (unipotentInBorel u₀ * ·) (Measure.map e _) = Measure.map e _
  rw [Measure.map_map (measurable_const_mul _) e.continuous.measurable, hcomp,
    ← Measure.map_map e.continuous.measurable hp.measurable, hp.map_eq]

/-- The real upper triangular group has a right Haar measure invariant by
left upper unipotent translation. -/
def RealBorelRightHaarStatement : Prop :=
  ∀ r : ℕ, IsFiniteMeasureOnCompacts (rightBorelMeasure r) ∧
    IsOpenPosMeasure (rightBorelMeasure r) ∧ IsMulRightInvariant (rightBorelMeasure r) ∧
    ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ,
      Measure.map (unipotentInBorel u * ·) (rightBorelMeasure r) = rightBorelMeasure r

theorem realBorelRightHaar : RealBorelRightHaarStatement :=
  fun _ => ⟨inferInstance, inferInstance, inferInstance, map_left_unipotent_rightBorelMeasure⟩

end Langlands.Global.RankinSelbergGlobal.RealBorelRightHaar
