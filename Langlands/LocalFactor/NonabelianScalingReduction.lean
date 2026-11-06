import Langlands.LocalFactor.NonabelianRankOneScaling
import Langlands.LocalFactor.NonabelianDeterminantTransfer
import Langlands.LocalFactor.NonabelianTraceScaling
import Langlands.LocalFactor.NonabelianUniquenessStatement

/-! # Reduction of additive-character scaling to degree-zero generation -/

noncomputable section

set_option maxHeartbeats 800000

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private def scalingValueHom (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    Virtual.{uF, uV} F E →+ Additive ℂˣ where
  toFun x := Additive.ofMul (ε E ψ μ x)
  map_zero' := value_zero hε E ψ μ
  map_add' x y := hε E ψ μ x y

/-- The determinant and integer-degree correction is multiplicative on the
actual exact virtual group. -/
def correctedScalingValueHom (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (c : ℂˣ) (w : weilSubgroup F E) :
    Virtual.{uF, uV} F E →+ Additive ℂˣ where
  toFun x := Additive.ofMul
    (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E) x w *
      c ^ (-degree F E x) * ε E ψ μ x)
  map_zero' := by
    apply Additive.toMul.injective
    change
      ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E)
          (0 : Virtual.{uF, uV} F E) w *
        c ^ (-degree F E (0 : Virtual.{uF, uV} F E)) * ε E ψ μ 0 = 1
    simp [value_zero hε]
  map_add' x y := by
    apply Additive.toMul.injective
    change
      ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E) (x + y) w *
          c ^ (-degree F E (x + y)) * ε E ψ μ (x + y) =
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E) x w *
          c ^ (-degree F E x) * ε E ψ μ x) *
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E) y w *
          c ^ (-degree F E y) * ε E ψ μ y)
    rw [ExactGrothendieckGroup.determinantCharacter_add_apply, map_add,
      neg_add, zpow_add, hε E ψ μ x y]
    ac_rfl

private def absoluteValueUnit (E : Extension F) (a : E.fieldˣ) : ℂˣ :=
  Units.mk0 ((fieldData F E).normalizedAbs (a : E.field) : ℂ)
    (by exact_mod_cast (ne_of_gt ((fieldData F E).normalizedAbs_pos a.ne_zero)))

private theorem scaling_on_weil_characterClass {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hε : RankOneRelation F e ε)
    (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      ε E (ψ.scale a) μ (ExactGrothendieckGroup.characterClass χ) =
        ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E)
            (ExactGrothendieckGroup.characterClass χ) w *
          absoluteValueUnit F E a ^ (-CommonClosure.degree.{uF, uV} F E (ExactGrothendieckGroup.characterClass χ)) *
          ε E ψ μ (ExactGrothendieckGroup.characterClass χ) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ μ a w ha
  let c : (weilSubgroup F E →ₜ* ℂˣ) ≃ FieldCharacter F E :=
    LocalClassField.abelianizationLiftEquiv.trans
      (LocalClassField.characterTransport (e E))
  let η := c χ
  have hχ : weilCharacter F e E η = χ := c.symm_apply_apply χ
  have hclass : characterClass.{uF, uV} F e E η =
      ExactGrothendieckGroup.characterClass χ := by
    unfold characterClass
    rw [hχ]
  have hscale := additiveCharacterScaling_characterClass F hε E η ψ μ a w ha
  rw [hclass] at hscale
  apply Units.ext
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, absoluteValueUnit,
    Units.val_mk0] using hscale

private theorem scalingHaarMeasure_nonempty (E : Extension F) :
    Nonempty (HaarMeasure F E) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let := (fieldData F E).fieldT2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts E.field) := inferInstance
  exact ⟨HarmonicAnalysis.normalizedAdditiveHaar E.field K⟩

/-- The full actual virtual scaling law follows from common-closure degree-zero
generation and the genuine Gallagher determinant formula. -/
theorem additiveCharacterScaling_of_commonClosureDegreeZeroGeneration
    (hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F)
    (hgal : Inductive.GallagherDeterminantStatement.{0, uF, max uF uV})
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (E : Extension F) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      ∀ x : Virtual.{uF, uV} F E,
      (ε E (ψ.scale a) μ x : ℂ) =
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x w : ℂ) *
          ((fieldData F E).normalizedAbs (a : E.field) : ℂ) ^ (-degree F E x) *
          (ε E ψ μ x : ℂ) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ μ a w ha x
  let A := (scalingValueHom F ε hε.2.1 E (ψ.scale a) μ).toIntLinearMap
  let B := (correctedScalingValueHom F ε hε.2.1 E ψ μ
    (absoluteValueUnit F E a) w).toIntLinearMap
  have hchar (χ : weilSubgroup F E →ₜ* ℂˣ) :
      A (ExactGrothendieckGroup.characterClass χ) =
        B (ExactGrothendieckGroup.characterClass χ) :=
    congrArg Additive.ofMul (scaling_on_weil_characterClass F hε.2.2.2.2 E χ ψ μ a w ha)
  have hgens : ∀ y ∈ characterDifferenceInductionGenerators.{uF, uV} F E,
      A y = B y := by
    rintro y ⟨L, h, χ, χ', rfl⟩
    let := (fieldData F L).topology
    let := (fieldData F L).valuativeRel
    let := (fieldData F L).localField
    obtain ⟨μL⟩ := scalingHaarMeasure_nonempty F L
    let z : DegreeZero.{uF, uV} F L :=
      ⟨ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ', by
        change degree F L _ = 0
        rw [map_sub, ExactGrothendieckGroup.degree_characterClass,
          ExactGrothendieckGroup.degree_characterClass, sub_self]⟩
    let aL := E.unitsInclusion L h a
    obtain ⟨v, hv⟩ := exists_reciprocityUnits_eq F e L aL
    have hvw : reciprocityUnits F e L v =
        E.unitsInclusion L h (reciprocityUnits F e E w) := by
      rw [ha]
      exact hv
    let ψL := traceCharacter F E L h ψ
    let AL := scalingValueHom F ε hε.2.1 L (ψL.scale aL) μL
    let BL := correctedScalingValueHom F ε hε.2.1 L ψL μL
      (absoluteValueUnit F L aL) v
    have hz : AL z.val = BL z.val := by
      change AL (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ') =
        BL (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ')
      rw [map_sub, map_sub]
      congr 1
      · exact congrArg Additive.ofMul
          (scaling_on_weil_characterClass F hε.2.2.2.2 L χ ψL μL aL v hv)
      · exact congrArg Additive.ofMul
          (scaling_on_weil_characterClass F hε.2.2.2.2 L χ' ψL μL aL v hv)
    have hzUnits := congrArg Additive.toMul hz
    change ε L (ψL.scale aL) μL z.val =
      ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F L) z.val v *
        absoluteValueUnit F L aL ^ (-degree F L z.val) * ε L ψL μL z.val at hzUnits
    have hz0 : degree F L z.val = 0 := z.property
    rw [hz0, neg_zero, zpow_zero, mul_one] at hzUnits
    have hdet := determinant_induce_degreeZero_reciprocity F hgal e hε.1 E L h z w v hvw
    change Additive.ofMul (ε E (ψ.scale a) μ (induce F E L h z.val)) =
      Additive.ofMul
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
            (induce F E L h z.val) w *
          absoluteValueUnit F E a ^ (-degree F E (induce F E L h z.val)) *
          ε E ψ μ (induce F E L h z.val))
    apply congrArg Additive.ofMul
    rw [hε.2.2.2.1 E L h (ψ.scale a) μ μL z,
      hε.2.2.2.1 E L h ψ μ μL z, traceCharacter_scale, degree_induce, hz0,
      mul_zero, neg_zero, zpow_zero, mul_one, hdet]
    exact hzUnits
  have hker : DegreeZero.{uF, uV} F E ≤ LinearMap.ker (A - B) := by
    rw [← hgen E]
    apply Submodule.span_le.mpr
    intro y hy
    change A y - B y = 0
    exact sub_eq_zero.mpr (hgens y hy)
  let t : Virtual.{uF, uV} F E :=
    ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ)
  let y := x - degree F E x • t
  have hyt : y ∈ DegreeZero.{uF, uV} F E := by
    change degree F E (x - degree F E x • t) = 0
    simp [t]
  have hy : A y = B y := sub_eq_zero.mp (hker hyt)
  have ht : A t = B t := hchar 1
  have hdecomp : y + degree F E x • t = x := sub_add_cancel _ _
  have hx : A x = B x := by
    calc
      A x = A (y + degree F E x • t) := congrArg A hdecomp.symm
      _ = A y + degree F E x • A t := by rw [map_add, map_smul]
      _ = B y + degree F E x • B t := by rw [hy, ht]
      _ = B (y + degree F E x • t) := by rw [map_add, map_smul]
      _ = B x := congrArg B hdecomp
  have hxUnits := congrArg Additive.toMul hx
  change ε E (ψ.scale a) μ x =
    ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x w *
      absoluteValueUnit F E a ^ (-degree F E x) * ε E ψ μ x at hxUnits
  have hxComplex := congrArg (fun u : ℂˣ => (u : ℂ)) hxUnits
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, absoluteValueUnit,
    Units.val_mk0] using hxComplex

/-- The uniform reduction has exactly the unchanged scaling statement as its
conclusion, retaining both prerequisite statements explicitly. -/
theorem additiveCharacterScaling_of_generation_gallagher
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV})
    (hgal : Inductive.GallagherDeterminantStatement.{0, uF, max uF uV}) :
    AdditiveCharacterScalingStatement.{uF, uV} := by
  intro p hp F e ε hε E
  exact additiveCharacterScaling_of_commonClosureDegreeZeroGeneration
    F (hgen p F) hgal hε E

end Langlands.LocalFactor.NonabelianSystem
