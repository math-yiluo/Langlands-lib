import Langlands.Automorphic.GeneralLinearConstantTermComparison

/-! # Actual standard-block vanishing functions and the original GL cuspidal space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.GeneralLinearBlockUnipotent

/-- The positive two-block splits used in the original general-linear cuspidality definition. -/
def generalLinearStandardMaximalBlockIndex (n : ℕ) :=
  {ab : ℕ × ℕ // ab.1 + ab.2 = n ∧ 0 < ab.1 ∧ 0 < ab.2}

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance cuspidalComparisonGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance standardBlockQuotientMeasurableSpace
    (i : generalLinearStandardMaximalBlockIndex n) :
    MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F GLG
      (subgroup F i.property.1)) :=
  borel _

variable [CompactSpace (AdeleQuotient F)]

/-- Convergent vanishing on the actual rational quotients for precisely the original
positive standard maximal two-block family, with the original normalized measures. -/
def generalLinearStandardBlockVanishingSubrepresentation :
    Subrepresentation (continuousRightAction F GLG) :=
  familyVanishingConstantTermSubrepresentation F GLG
    (fun i : generalLinearStandardMaximalBlockIndex n => subgroup F i.property.1)
    (fun i => rationalQuotientMeasure F i.property.1)

/-- Actual standard-block vanishing is exactly the original matrix cuspidality predicate. -/
theorem mem_generalLinearStandardBlockVanishingSubrepresentation_iff
    (f : ContinuousRationalFunctions F GLG) :
    f ∈ generalLinearStandardBlockVanishingSubrepresentation F n ↔
      Langlands.Automorphic.IsCuspidal F n (continuousGeneralLinearEquiv F n f) := by
  unfold generalLinearStandardBlockVanishingSubrepresentation
  rw [mem_familyVanishingConstantTermSubrepresentation]
  change (∀ i : generalLinearStandardMaximalBlockIndex n,
    HasVanishingConstantTerm F GLG (subgroup F i.property.1)
      (rationalQuotientMeasure F i.property.1) f) ↔ _
  constructor
  · intro hf a b h ha hb g
    exact (hasVanishingConstantTerm_generalLinearBlock_iff F h f).mp
      (hf ⟨(a, b), h, ha, hb⟩) g
  · intro hf i
    apply (hasVanishingConstantTerm_generalLinearBlock_iff F i.property.1 f).mpr
    exact hf i.val.1 i.val.2 i.property.1 i.property.2.1 i.property.2.2

/-- The actual continuous functions whose positive standard-block constant terms vanish. -/
abbrev GeneralLinearStandardBlockVanishingFunctions :=
  (generalLinearStandardBlockVanishingSubrepresentation F n).toSubmodule

/-- The original positive right action restricted to the actual vanishing subspace. -/
def generalLinearStandardBlockVanishingRightAction :
    Representation ℂ (AdelicGroupPoints F GLG)
      (GeneralLinearStandardBlockVanishingFunctions F n) :=
  (generalLinearStandardBlockVanishingSubrepresentation F n).toRepresentation

/-- The existing ambient function comparison restricts to a complex linear equivalence
with the original general-linear cuspidal subrepresentation. -/
def generalLinearCuspidalEquiv :
    GeneralLinearStandardBlockVanishingFunctions F n ≃ₗ[ℂ]
      (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (mem_generalLinearStandardBlockVanishingSubrepresentation_iff F n f.val).mp f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (mem_generalLinearStandardBlockVanishingSubrepresentation_iff F n _).mpr
    have hf : Langlands.Automorphic.IsCuspidal F n f.val := f.property
    simpa only [LinearEquiv.apply_symm_apply] using hf⟩
  left_inv f := by
    apply Subtype.ext
    exact (continuousGeneralLinearEquiv F n).left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact (continuousGeneralLinearEquiv F n).right_inv f.val
  map_add' f h := by
    apply Subtype.ext
    exact (continuousGeneralLinearEquiv F n).map_add f.val h.val
  map_smul' c f := by
    apply Subtype.ext
    exact (continuousGeneralLinearEquiv F n).map_smul c f.val

@[simp]
theorem generalLinearCuspidalEquiv_coe
    (f : GeneralLinearStandardBlockVanishingFunctions F n) :
    (generalLinearCuspidalEquiv F n f).val = continuousGeneralLinearEquiv F n f.val := rfl

@[simp]
theorem generalLinearCuspidalEquiv_symm_coe
    (f : (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule) :
    ((generalLinearCuspidalEquiv F n).symm f).val =
      (continuousGeneralLinearEquiv F n).symm f.val := rfl

/-- The restricted equivalence intertwines the exact positive right-translation actions. -/
theorem generalLinearCuspidalEquiv_rightAction
    (f : GeneralLinearStandardBlockVanishingFunctions F n) (g : AdelicGroupPoints F GLG) :
    generalLinearCuspidalEquiv F n
        (generalLinearStandardBlockVanishingRightAction F n g f) =
      (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) (generalLinearCuspidalEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- Ranks zero and one have no positive two-block splits, so this condition is vacuous. -/
theorem generalLinearStandardBlockVanishingSubrepresentation_eq_top_of_le_one (hn : n ≤ 1) :
    generalLinearStandardBlockVanishingSubrepresentation F n = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro f _
  change f ∈ generalLinearStandardBlockVanishingSubrepresentation F n
  rw [mem_generalLinearStandardBlockVanishingSubrepresentation_iff]
  intro a b h ha hb
  omega

end Langlands.Automorphic.GroupSchemeFunctions
