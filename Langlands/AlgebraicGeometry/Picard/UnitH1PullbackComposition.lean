import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardComposition
import Langlands.AlgebraicGeometry.Picard.UnitH1Pullback
import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitNaturality

/-! # Intrinsic restriction and transported unit cohomology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

namespace Langlands.AlgebraicGeometry.Picard

open NilpotentUnitReduction UnitSheafPushforward SquareZeroUnitCohomology

namespace UnitH1Pullback

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion (j ≫ i)]
  (hi : IsNilpotent i.ker) (hji : IsNilpotent (j ≫ i).ker)

/-- Restriction from `Y` to `Z`, computed after pushing both unit sheaves to `X`. -/
def transportedRestrictionMap (n : ℕ) : unitCohomology Y n →+ unitCohomology Z n :=
  (nilpotentUnitsCohomologyPushforwardEquiv (j ≫ i) hji n).toAddMonoidHom.comp
    ((Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction j)) n).comp
        (nilpotentUnitsCohomologyPushforwardEquiv i hi n).symm.toAddMonoidHom)

lemma transportedRestrictionMap_squareZero (hi : i.ker ^ 2 = ⊥)
    (hji : (j ≫ i).ker ^ 2 = ⊥) (n : ℕ) :
    transportedRestrictionMap i j ⟨2, hi⟩ ⟨2, hji⟩ n =
      SquareZeroUnitNaturality.quotientUnitCohomologyMap i j hi hji n := rfl

/-- Ambient reduction followed by transported restriction is composite reduction. -/
lemma transportedRestrictionMap_cohomologyMap (n : ℕ) (x : unitCohomology X n) :
    transportedRestrictionMap i j hi hji n (cohomologyMap i hi n x) =
      cohomologyMap (j ≫ i) hji n x := by
  change (nilpotentUnitsCohomologyPushforwardEquiv (j ≫ i) hji n)
      (Sheaf.H.map (SquareZeroUnitNaturality.quotientUnitsMap i j) n
        ((nilpotentUnitsCohomologyPushforwardEquiv i hi n).symm
          ((nilpotentUnitsCohomologyPushforwardEquiv i hi n)
            (Sheaf.H.map (unitsReduction i) n x)))) =
    (nilpotentUnitsCohomologyPushforwardEquiv (j ≫ i) hji n)
      (Sheaf.H.map (unitsReduction (j ≫ i)) n x)
  rw [AddEquiv.symm_apply_apply, ← Sheaf.H.map_comp_apply,
    SquareZeroUnitNaturality.unitsReduction_comp]

variable [IsClosedImmersion j] (hj : IsNilpotent j.ker)

lemma nilpotentClosedImmersionTopIso_comp :
    nilpotentClosedImmersionTopIso j hj ≪≫ nilpotentClosedImmersionTopIso i hi =
      nilpotentClosedImmersionTopIso (j ≫ i) hji := by
  apply Iso.ext
  rfl

/-- Transporting through the common ambient space is intrinsic restriction. -/
lemma transportedRestrictionMap_eq_cohomologyMap (n : ℕ) :
    transportedRestrictionMap i j hi hji n = cohomologyMap j hj n := by
  ext y
  let a := (nilpotentUnitsCohomologyPushforwardEquiv i hi n).symm y
  have hc := cohomologyPushforwardEquiv_comp
    (nilpotentClosedImmersionTopIso j hj) (nilpotentClosedImmersionTopIso i hi)
    (unitsSheaf Z.presheaf Z.sheaf.property) n
    (Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction j)) n a)
  have hcongr (e e' : Z.toTopCat ≅ X.toTopCat) (h : e = e') :
      HEq (cohomologyPushforwardEquiv e (unitsSheaf Z.presheaf Z.sheaf.property) n)
        (cohomologyPushforwardEquiv e' (unitsSheaf Z.presheaf Z.sheaf.property) n) := by
    cases h
    rfl
  have heq := eq_of_heq (hcongr
    (nilpotentClosedImmersionTopIso j hj ≪≫ nilpotentClosedImmersionTopIso i hi)
    (nilpotentClosedImmersionTopIso (j ≫ i) hji)
    (nilpotentClosedImmersionTopIso_comp i j hi hji hj))
  rw [heq] at hc
  have hn := cohomologyPushforwardEquiv_naturality
    (nilpotentClosedImmersionTopIso i hi) (unitsReduction j) n a
  change (nilpotentUnitsCohomologyPushforwardEquiv (j ≫ i) hji n)
      (Sheaf.H.map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsReduction j)) n a) =
    (nilpotentUnitsCohomologyPushforwardEquiv j hj n)
      (Sheaf.H.map (unitsReduction j) n y)
  have ha : cohomologyPushforwardEquiv (nilpotentClosedImmersionTopIso i hi)
      (unitsSheaf Y.presheaf Y.sheaf.property) n a = y :=
    (nilpotentUnitsCohomologyPushforwardEquiv i hi n).apply_symm_apply y
  exact hc.symm.trans (congrArg (nilpotentUnitsCohomologyPushforwardEquiv j hj n)
    (hn.trans (congrArg (Sheaf.H.map (unitsReduction j) n) ha)))

/-- Intrinsic actual unit-cohomology restriction composes in every degree. -/
lemma cohomologyMap_comp (n : ℕ) :
    (cohomologyMap j hj n).comp (cohomologyMap i hi n) =
      cohomologyMap (j ≫ i) hji n := by
  ext x
  change cohomologyMap j hj n (cohomologyMap i hi n x) = _
  rw [← transportedRestrictionMap_eq_cohomologyMap i j hi hji hj n]
  exact transportedRestrictionMap_cohomologyMap i j hi hji n x

end UnitH1Pullback

namespace SquareZeroUnitNaturality

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion (j ≫ i)] [IsClosedImmersion j]
  (hi : i.ker ^ 2 = ⊥) (hji : (j ≫ i).ker ^ 2 = ⊥)
  (hj : IsNilpotent j.ker)

/-- The published transported quotient map is intrinsic restriction. -/
lemma quotientUnitCohomologyMap_eq_cohomologyMap (n : ℕ) :
    quotientUnitCohomologyMap i j hi hji n = UnitH1Pullback.cohomologyMap j hj n :=
  UnitH1Pullback.transportedRestrictionMap_eq_cohomologyMap i j ⟨2, hi⟩ ⟨2, hji⟩ hj n

/-- The actual boundary is natural for intrinsic restriction to the inner subscheme. -/
lemma boundaryMap_cohomologyMap (n : ℕ) (y : unitCohomology Y n) :
    boundaryMap (j ≫ i) hji n (UnitH1Pullback.cohomologyMap j hj n y) =
      idealCohomologyMap i j (n + 1) (boundaryMap i hi n y) := by
  rw [← quotientUnitCohomologyMap_eq_cohomologyMap i j hi hji hj n]
  exact boundaryMap_naturality i j hi hji n y

end SquareZeroUnitNaturality

end Langlands.AlgebraicGeometry.Picard
