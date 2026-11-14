import Langlands.Representation.Conductor.UnramifiedPrincipalSeries
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers

/-!
# Rank-one blocks for ordered unramified principal series

The inducing character with uniformizer value `w` is realized on a lifted
complex line over an arbitrary nonarchimedean local field.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedRankOneBlocks

open CategoryTheory GeneralLinear UnramifiedPrincipalSeries

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The field data used by the all-field normalized induction and twist API. -/
abbrev fieldData :
    (AllFieldBZ.LocalFieldPackage.ofField F).TopologicalData :=
  LocalFieldData.ofInstances F

private theorem rankOneLine_smooth (w : ℂˣ) :
    IsSmooth (FiniteRepresentation.characterLine.{uF, uF}
      ((character hϖ w).comp (determinant (n := 1)))).representation := by
  let χ := (character hϖ w).comp (determinant (n := 1))
  have hopen : IsOpen (χ.ker : Set (GeneralLinear 1 F)) :=
    (isOpen_ker_character hϖ w).preimage
      (determinantContinuous (n := 1) (R := F)).continuous
  intro v
  refine ⟨⟨χ.ker, hopen⟩, ?_⟩
  intro g
  change (χ g.val : ℂ) • v = v
  rw [show χ g.val = 1 from g.property, Units.val_one, one_smul]

/-- The actual smooth rank-one character object with carrier `ULift ℂ`. -/
def rankOneObject (w : ℂˣ) :
    SmoothRep.{0, uF, uF} ℂ (GeneralLinear 1 F) :=
  SmoothRep.of
    (FiniteRepresentation.characterLine.{uF, uF}
      ((character hϖ w).comp (determinant (n := 1)))).representation
    (rankOneLine_smooth hϖ w)

/-- The rank-one unramified character, as an irreducible supercuspidal object. -/
def rankOneBlock (w : ℂˣ) :
    SupercuspidalRep.{uF, uF} (F := F) (n := 1) := by
  letI : Module.Finite ℂ (rankOneObject hϖ w) := by
    change Module.Finite ℂ (ULift.{uF} ℂ)
    infer_instance
  refine ⟨rankOneObject hϖ w,
    FiniteRepresentation.characterLine_isIrreducible _, ?_⟩
  refine ⟨⟨rankOneLine_smooth hϖ w, fun _ => inferInstance⟩, ?_⟩
  intro B hB g
  exfalso
  apply hB
  apply top_unique
  intro a _
  rw [B.mem_parabolic_iff]
  intro i j x y hij
  have hi := i.isLt
  have hj := j.isLt
  have hlen := B.length_le
  omega

@[simp]
theorem rankOneBlock_apply (w : ℂˣ) (g : GeneralLinear 1 F) (v : ULift.{uF} ℂ) :
    (rankOneBlock hϖ w).obj.representation g v =
      (character hϖ w (determinant g) : ℂ) • v := rfl

include hϖ in
/-- The normalized absolute value of the supplied uniformizer is less than one. -/
theorem normalizedAbs_uniformizer_lt_one :
    (fieldData (F := F)).normalizedAbs (ϖ : F) < 1 := by
  let T := fieldData (F := F)
  change T.normalizedAbs (ϖ : F) < 1
  apply lt_of_not_ge
  intro h
  have hv : T.discreteValuation (1 : F) ≤ T.discreteValuation (ϖ : F) :=
    (T.normalizedAbs_le_iff_of_ne_zero one_ne_zero ϖ.ne_zero).mp
      (by simpa only [T.normalizedAbs_one] using h)
  have hlt : T.discreteValuation (ϖ : F) < T.discreteValuation (1 : F) := by
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
        (ValuativeRel.valuation F (ϖ : F)) <
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
        (ValuativeRel.valuation F 1)
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono
      (by simpa only [map_one] using hϖ.1)
  exact (not_le_of_gt hlt) hv

/-- In weakly increasing norm order, a later character is not the `|det|` twist
of an earlier character. -/
theorem rankOneBlock_class_ne_twist {w w' : ℂˣ}
    (h : ‖(w : ℂ)‖ ≤ ‖(w' : ℂ)‖) :
    (rankOneBlock hϖ w').isoClass ≠
      (fieldData (F := F)).supercuspidalClassRealPowerTwist 1 1
        (rankOneBlock hϖ w).isoClass := by
  let T := fieldData (F := F)
  intro hc
  let At := SupercuspidalRep.twist (F := F) (n := 1) (T.determinantPowerCharacter 1 1)
    (T.isOpen_ker_determinantPowerCharacter 1 1)
    (T.ker_determinant_le_ker_determinantPowerCharacter 1 1)
    (rankOneBlock hϖ w)
  change (rankOneBlock hϖ w').isoClass = At.isoClass at hc
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff (rankOneBlock hϖ w') At).mp hc
  let E₀ := SmoothRep.equivOfIso
    ((supercuspidalProperty (F := F) (n := 1)).ι.mapIso e)
  let E : ULift.{uF} ℂ ≃ₗ[ℂ] ULift.{uF} ℂ := E₀.toLinearEquiv
  let v : ULift.{uF} ℂ := ⟨1⟩
  have hEv : E v ≠ 0 := by
    intro hz
    have hv : v = 0 := E.injective (by simpa only [map_zero] using hz)
    exact one_ne_zero (congrArg ULift.down hv)
  have he := Representation.IntertwiningMap.isIntertwining
    (rankOneBlock hϖ w').obj.representation At.obj.representation
    E₀.toIntertwiningMap (scalar (n := 1) ϖ) v
  change E ((character hϖ w' (determinant (scalar (n := 1) ϖ)) : ℂ) • v) =
    (T.determinantPowerCharacter 1 1 (scalar (n := 1) ϖ) : ℂ) •
      ((character hϖ w (determinant (scalar (n := 1) ϖ)) : ℂ) • E v) at he
  rw [map_smul, smul_smul] at he
  have hscalar := smul_left_injective ℂ hEv he
  have hdet : determinant (scalar (n := 1) ϖ) = ϖ := by
    change Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 1) ϖ) = ϖ
    simp only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]
  rw [hdet, character_uniformizer, character_uniformizer] at hscalar
  have hν : (T.determinantPowerCharacter 1 1 (scalar (n := 1) ϖ) : ℂ) =
      (T.normalizedAbs (ϖ : F) : ℂ) := by
    rw [coe_realPowerCharacter]
    change ((T.normalizedAbs (determinant (scalar (n := 1) ϖ) : F) ^ (1 : ℝ) : ℝ) : ℂ) = _
    rw [hdet, Real.rpow_one]
  rw [hν] at hscalar
  have hnorm : ‖(w' : ℂ)‖ = T.normalizedAbs (ϖ : F) * ‖(w : ℂ)‖ := by
    rw [hscalar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (T.normalizedAbs_nonneg (ϖ : F))]
  have hlt : T.normalizedAbs (ϖ : F) * ‖(w : ℂ)‖ < ‖(w : ℂ)‖ :=
    mul_lt_of_lt_one_left (norm_pos_iff.mpr w.ne_zero)
      (normalizedAbs_uniformizer_lt_one hϖ)
  exact (not_lt_of_ge h) (hnorm.trans_lt hlt)

/-- The sigma-indexed non-twist condition used in Bernstein–Zelevinsky 4.11. -/
theorem rankOneBlock_twist_ne {w w' : ℂˣ}
    (h : ‖(w : ℂ)‖ ≤ ‖(w' : ℂ)‖) :
    (⟨1, (rankOneBlock hϖ w').isoClass⟩ :
      Σ d, SupercuspidalClass.{uF, uF} (F := F) (n := d)) ≠
    ⟨1, (fieldData (F := F)).supercuspidalClassRealPowerTwist 1 1
      (rankOneBlock hϖ w).isoClass⟩ := by
  intro hEq
  exact rankOneBlock_class_ne_twist hϖ h (eq_of_heq (Sigma.mk.inj hEq).2)

end Langlands.Conductor.OrderedUnramifiedRankOneBlocks
