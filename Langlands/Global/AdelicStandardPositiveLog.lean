import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Global.AdelicLogSection
import Langlands.Global.AdelicWeylParameterEquivalence

/-! # Logarithmic coordinates of an actual positive split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "P" => fam.P J
local notation "A" => fam.A J
local notation "V" => RealCharacterDual F P
local notation "j" => (fam.a J ≫ fam.l J)

/-- The positive split component in the standard parabolic maps
isomorphically by the character logarithm onto its real character dual. -/
def StandardPositiveLogStatement : Prop :=
  FiniteDimensional ℝ V ∧
    ∃ e : fam.positiveSplitComponent J ≃* Multiplicative V,
      ∀ x, Multiplicative.toAdd (e x) = characterLog F P x.val

set_option maxHeartbeats 1700000 in
theorem standardPositiveLog : StandardPositiveLogStatement fam J := by
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have hinj := characterRestrict_splitComponent_injective r
  have hsurj := r.isCompatible.levi.characterRestrict_bijective.2
  have hrange : (characterRestrict j).range = (characterRestrict (fam.a J)).range := by
    ext χ
    change (∃ x, characterRestrict j x = χ) ↔ ∃ y, characterRestrict (fam.a J) y = χ
    simp only [characterRestrict_comp, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨characterRestrict (fam.l J) x, hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, rfl⟩
  let : (characterRestrict j).range.FiniteIndex := hrange.symm ▸
    r.isCompatible.splitComponent.finiteIndex_range_characterRestrict r.isCompatible.levi.isConnectedReductive
  obtain ⟨D, hD, ⟨e⟩⟩ := r.isCompatible.splitComponent.isCentralSplitTorus.1.1
  let : Fintype D := @Fintype.ofFinite D hD
  let coords := (realCharacterDualRestrictionEquiv F P (A).toGrp j hinj).symm.trans
    (dualCoordinatesContinuousEquiv F A D e)
  refine ⟨FiniteDimensional.of_injective coords.toLinearMap coords.injective, ?_⟩
  let S := logSection F P A j hinj D e
  let L := (characterLogHom F P).toMonoidHom.comp (fam.positiveSplitComponent J).subtype
  have hS (x : fam.positiveSplitComponent J) : S (L x) = x.val := by
    obtain ⟨a, ha, h⟩ := x.property
    let a₁ : intrinsicSubgroup F A := ⟨a, ha⟩
    have hP : positivePointMap F P A j a₁ = x.val := h
    change S (characterLogHom F P x.val) = x.val
    rw [← hP]
    exact logSection_characterLogHom_positivePointMap F P A j hinj D e a₁
  have hLinj : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    rw [← hS x, ← hS y, hxy]
  have hLsurj : Function.Surjective L := by
    intro y
    let a := (positiveAmbientLogEquiv F P A j hinj D e).symm y
    have ha : S y ∈ fam.positiveSplitComponent J := ⟨a.val, a.property, rfl⟩
    exact ⟨⟨S y, ha⟩, characterLogHom_logSection F P A j hinj D e y⟩
  exact ⟨MulEquiv.ofBijective L ⟨hLinj, hLsurj⟩, fun _ => rfl⟩

end Langlands.Global.StandardParabolicFamily
