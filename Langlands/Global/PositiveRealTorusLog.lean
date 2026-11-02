import Langlands.Global.AdelicCharacterLog
import Langlands.Global.PositiveRealTorusEmbedding

/-! # Logarithmic coordinates of actual positive split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- The general adelic character norm agrees with actual torus character evaluation. -/
theorem characterNorm_eq_absoluteValue_characterValue (χ : characterLattice T)
    (a : AdelicGroupPoints F T.toGrp) :
    characterNorm F T.toGrp χ.toMul a =
      IdeleAbsoluteValue.full F (Lie.characterValue χ a) := rfl

/-- Logarithmic evaluation uses the normalized torus character norm. -/
theorem characterLog_eq_log_characterValue (χ : characterLattice T)
    (a : AdelicGroupPoints F T.toGrp) :
    characterLog F T.toGrp a χ =
      Real.log ((IdeleAbsoluteValue.full F (Lie.characterValue χ a) : ℝ≥0) : ℝ) := rfl

variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The actual character lattice in the supplied finite splitting. -/
def characterCoordinates : characterLattice T ≃+ (I → ℤ) where
  toFun := characterExponents F I T e
  invFun m := Additive.ofMul
    (e.hom ≫ ((splitTorus.characterLatticeEquiv F I).symm m).toMul)
  left_inv χ := by
    change Additive.ofMul (e.hom ≫
      ((splitTorus.characterLatticeEquiv F I).symm
        ((splitTorus.characterLatticeEquiv F I)
          (Additive.ofMul (e.inv ≫ χ.toMul)))).toMul) = χ
    rw [AddEquiv.symm_apply_apply]
    change Additive.ofMul (e.hom ≫ e.inv ≫ χ.toMul) = χ
    rw [e.hom_inv_id_assoc]
    rfl
  right_inv m := by
    change (splitTorus.characterLatticeEquiv F I)
      (Additive.ofMul (e.inv ≫
        (e.hom ≫ ((splitTorus.characterLatticeEquiv F I).symm m).toMul))) = m
    rw [e.inv_hom_id_assoc]
    exact AddEquiv.apply_symm_apply _ _
  map_add' χ ψ := by
    exact (congrArg (splitTorus.characterLatticeEquiv F I)
      ((characterRestrict e.inv).map_add χ ψ)).trans
        ((splitTorus.characterLatticeEquiv F I).map_add _ _)

omit [NumberField F] in
@[simp] theorem characterCoordinates_apply (χ : characterLattice T) :
    characterCoordinates F T I e χ = characterExponents F I T e χ := rfl

open Classical in
omit [NumberField F] in
/-- A coordinate vector corresponds to the genuine coordinate character. -/
theorem characterCoordinates_symm_single (i : I) :
    (characterCoordinates F T I e).symm (Pi.single i 1) =
      coordinateCharacter F I T e i := by
  classical
  change Additive.ofMul (e.hom ≫
    ((splitTorus.characterLatticeEquiv F I).symm (Pi.single i 1)).toMul) = _
  rw [splitTorus.characterLatticeEquiv_symm_eq]
  simp [coordinateCharacter]

omit [NumberField F] in
/-- Every actual character is the finite sum of its coordinate characters. -/
theorem character_eq_sum_coordinateCharacter (χ : characterLattice T) :
    χ = ∑ i, characterExponents F I T e χ i • coordinateCharacter F I T e i := by
  classical
  calc
    χ = (characterCoordinates F T I e).symm
        (∑ i, characterExponents F I T e χ i • Pi.single i (1 : ℤ)) := by
      have hs : (∑ i, characterExponents F I T e χ i • Pi.single i (1 : ℤ)) =
          characterCoordinates F T I e χ := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hs]
      exact ((characterCoordinates F T I e).symm_apply_apply χ).symm
    _ = _ := by
      rw [map_sum]
      simp only [map_zsmul, characterCoordinates_symm_single]

/-- Logarithmic evaluation on the scalar torus retains the number-field degree. -/
theorem characterLog_full (χ : characterLattice T) (x : I → ℝ≥0ˣ) :
    characterLog F T.toGrp (full F I T e x) χ =
      (Module.finrank ℚ F : ℝ) *
        Real.log ((positiveCharacter F I T e χ x : ℝ≥0) : ℝ) := by
  rw [characterLog_eq_log_characterValue,
    absoluteValue_characterValue_full]
  simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow]

/-- The normalized logarithm is the degree times the actual exponent dot product. -/
theorem characterLog_full_eq_sum (χ : characterLattice T) (x : I → ℝ≥0ˣ) :
    characterLog F T.toGrp (full F I T e x) χ =
      (Module.finrank ℚ F : ℝ) *
        ∑ i, (characterExponents F I T e χ i : ℝ) * Real.log ((x i : ℝ≥0) : ℝ) := by
  rw [characterLog_full]
  congr 1
  change Real.log (((∏ i, x i ^ characterExponents F I T e χ i : ℝ≥0ˣ) : ℝ≥0) : ℝ) = _
  simp only [Units.coe_prod, NNReal.coe_prod, Units.val_zpow_eq_zpow_val,
    NNReal.coe_zpow]
  rw [Real.log_prod (fun i _ => zpow_ne_zero _ (by exact_mod_cast (x i).ne_zero))]
  simp only [Real.log_zpow]

open Classical in
omit [NumberField F] in
@[simp] theorem characterExponents_coordinateCharacter (i : I) :
    characterExponents F I T e (coordinateCharacter F I T e i) = Pi.single i 1 := by
  rw [← characterCoordinates_apply, ← characterCoordinates_symm_single,
    AddEquiv.apply_symm_apply]

/-- Coordinates on the real dual are evaluations at actual coordinate characters. -/
def dualCoordinates : RealCharacterDual F T.toGrp →ₗ[ℝ] (I → ℝ) where
  toFun ℓ i := ℓ (coordinateCharacter F I T e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The real dual functional given by a finite vector and the actual character exponents. -/
def dualFromCoordinates (v : I → ℝ) : RealCharacterDual F T.toGrp where
  toFun χ := ∑ i, (characterExponents F I T e χ i : ℝ) * v i
  map_zero' := by
    change (∑ i, ((characterCoordinates F T I e 0 i : ℤ) : ℝ) * v i) = 0
    simp only [map_zero, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
  map_add' χ ψ := by
    change (∑ i, ((characterCoordinates F T I e (χ + ψ) i : ℤ) : ℝ) * v i) = _
    simp only [map_add, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib,
      characterCoordinates_apply]

/-- Finite real coordinates identify the entire dual, with no rank assumption on an ambient group. -/
def dualCoordinatesEquiv : RealCharacterDual F T.toGrp ≃ₗ[ℝ] (I → ℝ) where
  toLinearMap := dualCoordinates F T I e
  invFun := dualFromCoordinates F T I e
  left_inv ℓ := by
    apply AddMonoidHom.ext
    intro χ
    let l : characterLattice T →+ ℝ := ℓ
    change (∑ i, (characterExponents F I T e χ i : ℝ) *
      l (coordinateCharacter F I T e i)) = l χ
    conv_rhs => rw [character_eq_sum_coordinateCharacter F T I e χ]
    have hs := map_sum l
      (fun i => characterExponents F I T e χ i • coordinateCharacter F I T e i) Finset.univ
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hs.symm
    have hz := AddMonoidHom.map_zsmul l
      (characterExponents F I T e χ i) (coordinateCharacter F I T e i)
    simpa only [zsmul_eq_mul] using hz.symm
  right_inv v := by
    classical
    funext i
    change (∑ j, (characterExponents F I T e (coordinateCharacter F I T e i) j : ℝ) *
      v j) = v i
    rw [characterExponents_coordinateCharacter]
    simp [Pi.single_apply]

omit [NumberField F] in
theorem continuous_dualCoordinates : Continuous (dualCoordinates F T I e) :=
  continuous_pi fun i => continuous_dualEval F T.toGrp (coordinateCharacter F I T e i)

omit [NumberField F] in
theorem continuous_dualFromCoordinates : Continuous (dualFromCoordinates F T I e) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro χ
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

/-- The pointwise topology on the actual split-torus dual is its finite real-coordinate topology. -/
def dualCoordinatesContinuousEquiv : RealCharacterDual F T.toGrp ≃L[ℝ] (I → ℝ) where
  toLinearEquiv := dualCoordinatesEquiv F T I e
  continuous_toFun := continuous_dualCoordinates F T I e
  continuous_invFun := continuous_dualFromCoordinates F T I e

/-- Each coordinate character reads off the normalized scalar logarithm. -/
theorem characterLog_full_coordinateCharacter (x : I → ℝ≥0ˣ) (i : I) :
    characterLog F T.toGrp (full F I T e x) (coordinateCharacter F I T e i) =
      (Module.finrank ℚ F : ℝ) * Real.log ((x i : ℝ≥0) : ℝ) := by
  classical
  rw [characterLog_full_eq_sum, characterExponents_coordinateCharacter]
  simp [Pi.single_apply]

/-- The real exponential, including its inverse, as a positive unit. -/
def expUnit (r : ℝ) : ℝ≥0ˣ where
  val := ⟨Real.exp r, (Real.exp_pos r).le⟩
  inv := ⟨Real.exp (-r), (Real.exp_pos (-r)).le⟩
  val_inv := by
    apply NNReal.eq
    change Real.exp r * Real.exp (-r) = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  inv_val := by
    apply NNReal.eq
    change Real.exp (-r) * Real.exp r = 1
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

@[simp] theorem coe_expUnit (r : ℝ) :
    ((expUnit r : ℝ≥0) : ℝ) = Real.exp r := rfl

@[simp] theorem log_expUnit (r : ℝ) :
    Real.log ((expUnit r : ℝ≥0) : ℝ) = r :=
  Real.log_exp r

@[simp] theorem expUnit_log (x : ℝ≥0ˣ) :
    expUnit (Real.log ((x : ℝ≥0) : ℝ)) = x := by
  apply Units.ext
  apply NNReal.eq
  exact Real.exp_log (by exact_mod_cast (pos_iff_ne_zero.mpr x.ne_zero))

theorem continuous_expUnit : Continuous expUnit :=
  Units.continuous_iff.mpr
    ⟨Real.continuous_exp.subtype_mk _,
      (Real.continuous_exp.comp continuous_neg).subtype_mk _⟩

/-- Number-field degree is positive, so the normalization can be inverted. -/
theorem degree_pos : 0 < (Module.finrank ℚ F : ℝ) := by
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))

/-- The inverse parameters use the actual normalized logarithm divided by field degree. -/
def logParameters (ℓ : RealCharacterDual F T.toGrp) : I → ℝ≥0ˣ :=
  fun i => expUnit (ℓ (coordinateCharacter F I T e i) / (Module.finrank ℚ F : ℝ))

theorem continuous_logParameters : Continuous (logParameters F T I e) :=
  continuous_pi fun i => continuous_expUnit.comp
    ((continuous_dualEval F T.toGrp (coordinateCharacter F I T e i)).div_const _)

/-- Exponentiating the normalized coordinate logs recovers the original scalar parameters. -/
theorem logParameters_characterLog_full (x : I → ℝ≥0ˣ) :
    logParameters F T I e (characterLog F T.toGrp (full F I T e x)) = x := by
  funext i
  change expUnit (characterLog F T.toGrp (full F I T e x)
    (coordinateCharacter F I T e i) / (Module.finrank ℚ F : ℝ)) = x i
  rw [characterLog_full_coordinateCharacter,
    mul_div_cancel_left₀ _ (ne_of_gt (degree_pos F)), expUnit_log]

/-- Every real character functional is the log of the explicit positive scalar point. -/
theorem characterLog_full_logParameters (ℓ : RealCharacterDual F T.toGrp) :
    characterLog F T.toGrp (full F I T e (logParameters F T I e ℓ)) = ℓ := by
  apply (dualCoordinatesEquiv F T I e).injective
  funext i
  change characterLog F T.toGrp (full F I T e (logParameters F T I e ℓ))
    (coordinateCharacter F I T e i) = ℓ (coordinateCharacter F I T e i)
  rw [characterLog_full_coordinateCharacter]
  change (Module.finrank ℚ F : ℝ) *
    Real.log ((expUnit (ℓ (coordinateCharacter F I T e i) /
      (Module.finrank ℚ F : ℝ)) : ℝ≥0) : ℝ) = _
  rw [log_expUnit, mul_div_cancel₀ _ (ne_of_gt (degree_pos F))]

/-- The explicit exponential inverse lands in the actual intrinsic subgroup. -/
def positiveExp (ℓ : RealCharacterDual F T.toGrp) : intrinsicSubgroup F T :=
  ⟨full F I T e (logParameters F T I e ℓ),
    (subgroup_eq_intrinsicSubgroup F I T e).le ⟨_, rfl⟩⟩

theorem continuous_positiveExp : Continuous (positiveExp F T I e) :=
  ((continuousFull F I T e).continuous.comp
    (continuous_logParameters F T I e)).subtype_mk _

/-- On the actual intrinsic positive subgroup, the normalized log is a topological group
isomorphism onto the entire real character dual. -/
def positiveLogEquiv :
    intrinsicSubgroup F T ≃ₜ* Multiplicative (RealCharacterDual F T.toGrp) where
  toFun a := Multiplicative.ofAdd (characterLog F T.toGrp a.val)
  invFun ℓ := positiveExp F T I e ℓ.toAdd
  left_inv a := by
    have ha : a.val ∈ subgroup F I T e := by
      rw [subgroup_eq_intrinsicSubgroup]
      exact a.property
    obtain ⟨x, hx⟩ := (mem_subgroup_iff F I T e a.val).mp ha
    apply Subtype.ext
    change full F I T e (logParameters F T I e (characterLog F T.toGrp a.val)) = a.val
    rw [← hx, logParameters_characterLog_full]
  right_inv ℓ := characterLog_full_logParameters F T I e ℓ.toAdd
  map_mul' a b := characterLog_mul F T.toGrp a.val b.val
  continuous_toFun := (continuous_characterLog F T.toGrp).comp continuous_subtype_val
  continuous_invFun := continuous_positiveExp F T I e

@[simp] theorem positiveLogEquiv_apply (a : intrinsicSubgroup F T) :
    (positiveLogEquiv F T I e a).toAdd = characterLog F T.toGrp a.val := rfl

end Langlands.Global.PositiveRealTorus
