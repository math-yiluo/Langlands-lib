import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Analysis.Local.QuotientMass

/-!
# A right-invariant measure on the unipotent quotient of the mirabolic group

The Levi embedding and the projection identify the left quotient of the
mirabolic group `P_n` by its upper unipotent subgroup with the left quotient of
`GL_n` by its upper unipotent subgroup. Transporting the published quotient
measure `RankinSelberg.unipotentQuotientHaar` gives a measure on the mirabolic
quotient that is finite on compact sets, right invariant under `P_n`, and gives
positive finite mass to the orbit of every compact open subgroup. In rank zero
the quotient is a point and the Dirac measure is used.
-/

noncomputable section

namespace Langlands.Whittaker

open MeasureTheory MeasureTheory.Measure GeneralLinear GeneralLinear.Mirabolic QuotientIntegration
open scoped ENNReal

universe uF

namespace MirabolicQuotient

section Homeomorph

variable {F : Type uF} [Field F] {n : ℕ}

theorem projection_mem_upperUnipotent {u : mirabolic n F}
    (hu : u ∈ Mirabolic.upperUnipotent n F) :
    projection u ∈ GeneralLinear.upperUnipotent n F := by
  constructor
  · intro i j hij
    exact hu.1 (Fin.castSucc_lt_castSucc_iff.mpr hij)
  · intro i
    exact hu.2 i.castSucc

theorem levi_mem_upperUnipotent {a : Langlands.GeneralLinear n F}
    (ha : a ∈ GeneralLinear.upperUnipotent n F) :
    levi a ∈ Mirabolic.upperUnipotent n F := by
  constructor
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      change (levi a).val.val (Fin.last n) j = 0
      rw [levi_bottom]
      exact ite_eq_right (Fin.ne_last_of_lt hij)
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
      | cast j =>
        change (levi a).val.val i.castSucc j.castSucc = 0
        rw [levi_first]
        exact ha.1 (Fin.castSucc_lt_castSucc_iff.mp hij)
  · intro i
    induction i using Fin.lastCases with
    | last =>
      change (levi a).val.val (Fin.last n) (Fin.last n) = 1
      rw [levi_bottom]
      exact ite_eq_left rfl
    | cast i =>
      change (levi a).val.val i.castSucc i.castSucc = 1
      rw [levi_first]
      exact ha.2 i

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- The quotient map induced by the projection `P_n → GL_n`. -/
def toGL : LeftQuotient (Mirabolic.upperUnipotent n F) →
    LeftQuotient (GeneralLinear.upperUnipotent n F) :=
  Quotient.map' projection fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact projection_mem_upperUnipotent h

/-- The quotient map induced by the Levi embedding `GL_n → P_n`. -/
def ofGL : LeftQuotient (GeneralLinear.upperUnipotent n F) →
    LeftQuotient (Mirabolic.upperUnipotent n F) :=
  Quotient.map' levi fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact levi_mem_upperUnipotent h

/-- The unipotent quotients of `P_n` and `GL_n` are homeomorphic. -/
def quotientHomeomorph : LeftQuotient (Mirabolic.upperUnipotent n F) ≃ₜ
    LeftQuotient (GeneralLinear.upperUnipotent n F) where
  toFun := toGL
  invFun := ofGL
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      have he : g * (levi (projection g))⁻¹ = (radicalElement (lastColumn g)).val :=
        calc g * (levi (projection g))⁻¹ = (radicalElement (lastColumn g)).val *
              levi (projection g) * (levi (projection g))⁻¹ := by
              rw [← eq_radicalElement_mul_levi g]
          _ = _ := mul_inv_cancel_right _ _
      rw [he]
      exact radical_le_upperUnipotent (radicalElement _).property
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h a => exact congrArg (Quotient.mk _) (projection_levi a)
  continuous_toFun := continuous_projection.quotient_map' _
  continuous_invFun := continuous_levi.quotient_map' _

theorem quotientHomeomorph_rightTranslate (g : mirabolic n F)
    (q : LeftQuotient (Mirabolic.upperUnipotent n F)) :
    quotientHomeomorph (rightTranslate _ g q) =
      rightTranslate _ (projection g) (quotientHomeomorph q) := by
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (Quotient.mk _) (map_mul projection x g)

theorem rightTranslate_quotientHomeomorph_symm (g : mirabolic n F)
    (q : LeftQuotient (GeneralLinear.upperUnipotent n F)) :
    rightTranslate _ g (quotientHomeomorph.symm q) =
      quotientHomeomorph.symm (rightTranslate _ (projection g) q) := by
  apply quotientHomeomorph.injective
  rw [quotientHomeomorph_rightTranslate, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end Homeomorph

section Measure

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private instance rankZero_subsingleton :
    Subsingleton (LeftQuotient (Mirabolic.upperUnipotent 0 F)) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun x y => congrArg _ (Subsingleton.elim x y)⟩

/-- In rank zero the quotient is a point, and the Dirac measure has the required properties. -/
theorem exists_measure_zero
    [MeasurableSpace (LeftQuotient (Mirabolic.upperUnipotent 0 F))]
    [BorelSpace (LeftQuotient (Mirabolic.upperUnipotent 0 F))] :
    ∃ ν : Measure (LeftQuotient (Mirabolic.upperUnipotent 0 F)), IsFiniteMeasureOnCompacts ν ∧
      (∀ g : mirabolic 0 F, MeasurePreserving (rightTranslate _ g) ν ν) ∧
      ∀ J : OpenSubgroup (mirabolic 0 F), IsCompact (J : Set (mirabolic 0 F)) →
        0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤ := by
  refine ⟨Measure.dirac (leftQuotientMap _ 1), inferInstance, fun g => ?_, fun J _ => ?_⟩
  · have h : ⇑(rightTranslate (Mirabolic.upperUnipotent 0 F) g) = id :=
      funext fun _ => Subsingleton.elim _ _
    rw [h]
    exact MeasurePreserving.id _
  · rw [Measure.dirac_apply_of_mem
      (show leftQuotientMap _ 1 ∈ compactOpenQuotientOrbit _ J from ⟨1, J.one_mem, rfl⟩)]
    exact ⟨zero_lt_one, ENNReal.one_lt_top⟩

end Measure

section Positive

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- In positive rank, transport of the unipotent quotient measure of `GL_(k+1)`. -/
theorem exists_measure_succ (k : ℕ)
    [MeasurableSpace (LeftQuotient (Mirabolic.upperUnipotent (k + 1) F))]
    [BorelSpace (LeftQuotient (Mirabolic.upperUnipotent (k + 1) F))] :
    ∃ ν : Measure (LeftQuotient (Mirabolic.upperUnipotent (k + 1) F)),
      IsFiniteMeasureOnCompacts ν ∧
      (∀ g : mirabolic (k + 1) F, MeasurePreserving (rightTranslate _ g) ν ν) ∧
      ∀ J : OpenSubgroup (mirabolic (k + 1) F), IsCompact (J : Set (mirabolic (k + 1) F)) →
        0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤ := by
  let : MeasurableSpace (GeneralLinear.upperUnipotent (k + 1) F) := borel _
  have : BorelSpace (GeneralLinear.upperUnipotent (k + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (Matrix.GeneralLinearGroup (Fin (k + 1)) F) := borel _
  have : BorelSpace (Matrix.GeneralLinearGroup (Fin (k + 1)) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient (GeneralLinear.upperUnipotent (k + 1) F)) := borel _
  have : BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent (k + 1) F)) := ⟨rfl⟩
  have hμ := RankinSelberg.unipotentQuotientHaar_isCompatible F k
  let μ := RankinSelberg.unipotentQuotientHaar F k
  let e := (quotientHomeomorph (n := k + 1) (F := F)).symm
  refine ⟨μ.map e, IsFiniteMeasureOnCompacts.map μ e, fun g => ?_, fun J hJ => ?_⟩
  · refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
    have hcomm : (rightTranslate (Mirabolic.upperUnipotent (k + 1) F) g) ∘ e =
        e ∘ rightTranslate (GeneralLinear.upperUnipotent (k + 1) F) (projection g) :=
      funext fun q => rightTranslate_quotientHomeomorph_symm g q
    rw [Measure.map_map (rightTranslate _ g).continuous.measurable e.continuous.measurable, hcomm,
      ← Measure.map_map e.continuous.measurable (rightTranslate _ _).continuous.measurable,
      (hμ.right_invariant (projection g)).map_eq]
  · have hm :=
      (isOpen_compactOpenQuotientOrbit (Mirabolic.upperUnipotent (k + 1) F) J).measurableSet
    rw [Measure.map_apply e.continuous.measurable hm]
    have hpre : e ⁻¹' compactOpenQuotientOrbit _ J = e.symm '' compactOpenQuotientOrbit _ J :=
      (congrFun e.image_symm _).symm
    rw [hpre]
    exact hμ.measure_pos_lt_top
      ((isCompact_compactOpenQuotientOrbit _ J hJ).image e.symm.continuous)
      (e.symm.isOpenMap _ (isOpen_compactOpenQuotientOrbit _ J))
      ((compactOpenQuotientOrbit_nonempty _ J).image _)

/-- Every rank has a measure on the unipotent quotient of the mirabolic group that is
finite on compact sets, right invariant, and positive and finite on compact open orbits. -/
theorem exists_measure (n : ℕ)
    [MeasurableSpace (LeftQuotient (Mirabolic.upperUnipotent n F))]
    [BorelSpace (LeftQuotient (Mirabolic.upperUnipotent n F))] :
    ∃ ν : Measure (LeftQuotient (Mirabolic.upperUnipotent n F)), IsFiniteMeasureOnCompacts ν ∧
      (∀ g : mirabolic n F, MeasurePreserving (rightTranslate _ g) ν ν) ∧
      ∀ J : OpenSubgroup (mirabolic n F), IsCompact (J : Set (mirabolic n F)) →
        0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤ := by
  cases n with
  | zero => exact exists_measure_zero
  | succ k => exact exists_measure_succ k

end Positive

end MirabolicQuotient

end Langlands.Whittaker
