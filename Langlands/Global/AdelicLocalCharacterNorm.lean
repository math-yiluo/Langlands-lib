import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.IntegralFiniteAdeles

/-! # Normalized character norms on the actual local point groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]

namespace placeCompletion

/-- Each actual completion is locally compact in its existing topology. -/
instance locallyCompactSpace : (i : Place F) → LocallyCompactSpace (placeCompletion F i)
  | .inl w => inferInstanceAs (LocallyCompactSpace w.Completion)
  | .inr v =>
    (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem)

end placeCompletion

/-- The normalized completion norm, with exponent two at a complex place. -/
def placeNormValue : (i : Place F) → (placeCompletion F i)ˣ →* ℝ≥0
  | .inl w =>
    show w.Completionˣ →* ℝ≥0 from
    { toFun x := ‖(x.val : w.Completion)‖₊ ^ w.mult
      map_one' := by simp
      map_mul' x y := by simp only [Units.val_mul, nnnorm_mul, mul_pow] }
  | .inr v =>
    show (FiniteCompletion F v)ˣ →* ℝ≥0 from
    { toFun x := ‖(x.val : FiniteCompletion F v)‖₊
      map_one' := by simp
      map_mul' x y := by simp only [Units.val_mul, nnnorm_mul] }

private theorem continuous_placeNormValue :
    (i : Place F) → Continuous (placeNormValue F i)
  | .inl w =>
    show Continuous (fun x : w.Completionˣ => ‖x.val‖₊ ^ w.mult) from
      (continuous_nnnorm.comp Units.continuous_val).pow w.mult
  | .inr v =>
    show Continuous (fun x : (FiniteCompletion F v)ˣ => ‖x.val‖₊) from
      continuous_nnnorm.comp Units.continuous_val

/-- The continuous normalized absolute value on the units of an actual completion. -/
def placeNorm (i : Place F) : (placeCompletion F i)ˣ →ₜ* ℝ≥0ˣ where
  toMonoidHom := (placeNormValue F i).toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_placeNormValue F i, (continuous_placeNormValue F i).comp continuous_inv⟩

@[simp] theorem coe_placeNorm_inl (w : InfinitePlace F) (x : w.Completionˣ) :
    ((placeNorm F (.inl w) x : ℝ≥0) : ℝ) =
      ‖(x.val : w.Completion)‖ ^ w.mult := rfl

@[simp] theorem coe_placeNorm_inr (v : FinitePlace F) (x : (FiniteCompletion F v)ˣ) :
    ((placeNorm F (.inr v) x : ℝ≥0) : ℝ) =
      ‖(x.val : FiniteCompletion F v)‖ := rfl

variable (G : GroupScheme (Spec (CommRingCat.of F)))

namespace PlaceGroupPoints

/-- Local finite-type affine points retain their locally compact evaluation topology. -/
instance locallyCompactSpace [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (i : Place F) : LocallyCompactSpace (PlaceGroupPoints F G i) :=
  G.affinePointsLocallyCompactSpace (placeCompletion F i)

/-- The Borel sigma algebra of the existing local point topology. -/
instance measurableSpace (i : Place F) : MeasurableSpace (PlaceGroupPoints F G i) :=
  borel (PlaceGroupPoints F G i)

instance borelSpace (i : Place F) : BorelSpace (PlaceGroupPoints F G i) := ⟨rfl⟩

end PlaceGroupPoints

namespace AdelicGroupPoints

/-- The normalized norm of an actual rational algebraic character at one place. -/
def localCharacterNorm (χ : AlgebraicCharacter F G) (i : Place F) :
    PlaceGroupPoints F G i →ₜ* ℝ≥0ˣ :=
  (placeNorm F i).comp
    { toMonoidHom := characterUnits F G χ (placeCompletion F i)
      continuous_toFun := continuous_characterUnits F G χ (placeCompletion F i) }

/-- Local evaluation of a rational character is the corresponding idele coordinate. -/
theorem characterUnits_atPlace (χ : AlgebraicCharacter F G) (i : Place F)
    (g : AdelicGroupPoints F G) :
    characterUnits F G χ (placeCompletion F i) (atPlace F G i g) =
      Units.map (adeleProjection F i).toRingHom.toMonoidHom (character F G χ g) :=
  characterUnits_naturality F G χ (CommAlgCat.ofHom (adeleProjection F i)) g

@[simp] theorem coe_localCharacterNorm_atInfinitePlace (χ : AlgebraicCharacter F G)
    (w : InfinitePlace F) (g : AdelicGroupPoints F G) :
    ((localCharacterNorm F G χ (.inl w) (atPlace F G (.inl w) g) : ℝ≥0) : ℝ) =
      ‖(character F G χ g).val.1 w‖ ^ w.mult := by
  change (((placeNorm F (.inl w)
    (characterUnits F G χ (placeCompletion F (.inl w))
      (atPlace F G (.inl w) g))) : ℝ≥0) : ℝ) = _
  rw [characterUnits_atPlace]
  rfl

@[simp] theorem coe_localCharacterNorm_atFinitePlace (χ : AlgebraicCharacter F G)
    (v : FinitePlace F) (g : AdelicGroupPoints F G) :
    ((localCharacterNorm F G χ (.inr v) (atPlace F G (.inr v) g) : ℝ≥0) : ℝ) =
      ‖(character F G χ g).val.2 v‖ := by
  change (((placeNorm F (.inr v)
    (characterUnits F G χ (placeCompletion F (.inr v))
      (atPlace F G (.inr v) g))) : ℝ≥0) : ℝ) = _
  rw [characterUnits_atPlace]
  rfl

/-- The existing adelic character norm is the product of these actual local norms. -/
theorem coe_characterNorm_eq_prod_localCharacterNorm (χ : AlgebraicCharacter F G)
    (g : AdelicGroupPoints F G) :
    ((characterNorm F G χ g : ℝ≥0) : ℝ) =
      (∏ w : InfinitePlace F,
        ((localCharacterNorm F G χ (.inl w) (atPlace F G (.inl w) g) : ℝ≥0) : ℝ)) *
      ∏ᶠ v : FinitePlace F,
        ((localCharacterNorm F G χ (.inr v) (atPlace F G (.inr v) g) : ℝ≥0) : ℝ) := by
  simp only [coe_localCharacterNorm_atInfinitePlace, coe_localCharacterNorm_atFinitePlace]
  exact IdeleAbsoluteValue.coe_full F (character F G χ g)

end AdelicGroupPoints

end Langlands.Global
