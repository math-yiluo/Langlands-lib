import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.GroupSchemeAmbient
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.PositiveRealIdeles
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Determinant slices of the actual general-linear rational quotient -/

noncomputable section

universe uF

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj InnerProductSpace NNReal

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global
open ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

/-- The existing matrix group scheme, used only to reuse the rational quotient. -/
abbrev matrixGroupScheme := Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance glIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance glSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The actual principal rational quotient of the general linear group. -/
abbrev Quotient := AdelicGroupPoints.RationalQuotient F (matrixGroupScheme F n)

/-- The actual determinant norm on the group-scheme adelic points. -/
def groupDeterminantNorm : AdelicGroupPoints F (matrixGroupScheme F n) →ₜ* ℝ≥0ˣ :=
  (AdelicBlockDeterminantCharacter.determinantNorm F n).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (GeneralLinearGroupPoints.adelicHomeomorph F n))

@[simp]
theorem groupDeterminantNorm_rational (q : RationalGroupPoints F (matrixGroupScheme F n)) :
    groupDeterminantNorm F n (AdelicGroupPoints.rational F (matrixGroupScheme F n) q) = 1 := by
  change AdelicBlockDeterminantCharacter.determinantNorm F n
    (GeneralLinearGroupPoints.adelicHomeomorph F n
      (AdelicGroupPoints.rational F (matrixGroupScheme F n) q)) = 1
  rw [GeneralLinearGroupPoints.adelicHomeomorph_rational,
    AdelicBlockDeterminantCharacter.determinantNorm_rational]

/-- Product formula descent of the determinant norm to the rational quotient. -/
def quotientDeterminantNorm : C(Quotient F n, ℝ≥0ˣ) where
  toFun := LeftCosetSpace.lift (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n))
    (groupDeterminantNorm F n) (by
      rintro ⟨γ, ⟨q, rfl⟩⟩ x
      rw [map_mul, groupDeterminantNorm_rational, one_mul])
  continuous_toFun := LeftCosetSpace.continuous_lift _ _ _
    (groupDeterminantNorm F n).continuous

@[simp]
theorem quotientDeterminantNorm_mk (x : AdelicGroupPoints F (matrixGroupScheme F n)) :
    quotientDeterminantNorm F n
      (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) x) =
        groupDeterminantNorm F n x := rfl

/-- An open band is convenient for proving faithfulness from full Haar support. -/
def band : Set (Quotient F n) :=
  {q | 1 < (quotientDeterminantNorm F n q : ℝ≥0) ∧
    (quotientDeterminantNorm F n q : ℝ≥0) < 2}

theorem isOpen_band : IsOpen (band F n) :=
  isOpen_Ioo.preimage
    (Units.continuous_val.comp (quotientDeterminantNorm F n).continuous)

theorem measurableSet_band : MeasurableSet (band F n) :=
  (isOpen_band F n).measurableSet

@[simp]
theorem quotientDeterminantNorm_rightTranslate
    (g : AdelicGroupPoints F (matrixGroupScheme F n)) (q : Quotient F n) :
    quotientDeterminantNorm F n
      (LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) g q) =
        quotientDeterminantNorm F n q * groupDeterminantNorm F n g := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective
    (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) q
  exact map_mul (groupDeterminantNorm F n) x g

theorem preimage_band_rightTranslate
    (g : AdelicGroupPoints F (matrixGroupScheme F n)) (hg : groupDeterminantNorm F n g = 1) :
    LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) g ⁻¹'
      band F n = band F n := by
  ext q
  simp only [Set.mem_preimage, band, Set.mem_ofPred_eq,
    quotientDeterminantNorm_rightTranslate, hg, mul_one]

/-- Restriction of an invariant quotient measure remains invariant under norm-one elements. -/
theorem measurePreserving_band
    (measure : Measure (Quotient F n)) (g : AdelicGroupPoints F (matrixGroupScheme F n))
    (hg : groupDeterminantNorm F n g = 1)
    (hmeasure : MeasurePreserving
      (LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) g) measure measure) :
    MeasurePreserving
      (LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) g)
      (measure.restrict (band F n)) (measure.restrict (band F n)) := by
  simpa only [preimage_band_rightTranslate F n g hg] using
    hmeasure.restrict_preimage (measurableSet_band F n)

/-- Scalar ideles can prescribe every positive determinant norm in positive rank. -/
theorem exists_scalar_determinantNorm (hn : n ≠ 0) (t : ℝ≥0ˣ) :
    ∃ z : Ideles F,
      AdelicBlockDeterminantCharacter.determinantNorm F n (AdelicGL.scalar F n z) = t := by
  let k := Module.finrank ℚ F * n
  have hk : k ≠ 0 := Nat.mul_ne_zero (ne_of_gt (Module.finrank_pos)) hn
  let a : ℝ≥0 := (t : ℝ≥0) ^ ((k : ℝ)⁻¹)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact ne_of_gt (NNReal.rpow_pos (pos_iff_ne_zero.mpr (Units.ne_zero t)))
  let u : ℝ≥0ˣ := Units.mk0 a ha
  refine ⟨PositiveRealIdeles.full F u, ?_⟩
  rw [AdelicBlockDeterminantCharacter.determinantNorm_scalar,
    PositiveRealIdeles.absoluteValue_full, ← pow_mul]
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow (t : ℝ≥0) hk

/-- Every right translation has a central scalar correction of norm one. -/
theorem exists_normalized_rightTranslate (hn : n ≠ 0) (g : AdelicGL F n) :
    ∃ z : Ideles F,
      AdelicBlockDeterminantCharacter.determinantNorm F n
        (AdelicGL.scalar F n z * g) = 1 := by
  obtain ⟨z, hz⟩ := exists_scalar_determinantNorm F n hn
    (AdelicBlockDeterminantCharacter.determinantNorm F n g)⁻¹
  exact ⟨z, by rw [map_mul, hz, inv_mul_cancel]⟩

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance spaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The original realized vector, descended without changing its underlying function. -/
def toQuotient : S.Space →ₗ[ℂ] C(Quotient F n, ℂ) :=
  (GroupSchemeFunctions.continuousQuotientLinearEquiv F (matrixGroupScheme F n)).symm.toLinearMap.comp
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm.toLinearMap.comp
      S.toContinuous)

@[simp]
theorem toQuotient_mk (f : S.Space) (x : AdelicGroupPoints F (matrixGroupScheme F n)) :
    toQuotient F n S f
      (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) x) =
        evaluate F n (S.toContinuous f) (GeneralLinearGroupPoints.adelicHomeomorph F n x) :=
  rfl

theorem toQuotient_injective : Function.Injective (toQuotient F n S) :=
  (GroupSchemeFunctions.continuousQuotientLinearEquiv F (matrixGroupScheme F n)).symm.injective.comp
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm.injective.comp
      S.toContinuous_injective)

end Langlands.Automorphic.OperatorDeterminantSlice
