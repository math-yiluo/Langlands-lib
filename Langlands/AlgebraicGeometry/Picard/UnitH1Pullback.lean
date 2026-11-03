import Langlands.Cohomology.AbelianSheafH1Pushforward
import Langlands.AlgebraicGeometry.Picard.UnitCechPullback
import Langlands.AlgebraicGeometry.Picard.UnitH1AddEquiv
import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitCohomology

/-! # Actual Picard pullback and unit cohomology for nilpotent immersions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

namespace UnitH1Pullback

open Langlands.Cohomology Cech AbelianSheafCechH1
open AbelianSheafH1Naturality AbelianSheafH1Pushforward
open UnitCechH1Comparison NilpotentUnitReduction UnitSheafPushforward

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker)

/-- Actual unit reduction in every degree for a nilpotent closed immersion. -/
def cohomologyMap (n : ℕ) :
    Sheaf.H.{u} (unitSheaf X) n →+ Sheaf.H.{u} (unitSheaf Y) n :=
  (nilpotentUnitsCohomologyPushforwardEquiv i hi n).toAddMonoidHom.comp
    (Sheaf.H.map (unitsReduction i) n)

/-- In the square-zero case this is the existing actual reduction map. -/
lemma cohomologyMap_squareZero (hi : i.ker ^ 2 = ⊥) (n : ℕ) :
    cohomologyMap i ⟨2, hi⟩ n = SquareZeroUnitCohomology.reductionMap i hi n := rfl

variable {ι : Type u} [Finite ι] (U : ι → X.Opens)

/-- The class of the pulled unit cocycle is actual unit reduction in H¹. -/
theorem classOfCocycle_pullback (hU : (⨆ a, U a) = ⊤)
    (z : cocycles (unitSheaf X).1 U) :
    classOfCocycle (fun a => i ⁻¹ᵁ U a) (i.iSup_preimage_eq_top hU)
        (UnitCechPullback.mapCocycles i U z) =
      cohomologyMap i hi 1 (classOfCocycle U hU z) := by
  change comparisonHom (unitSheaf Y) (fun a => i ⁻¹ᵁ U a) _
      (CechPullback.h1Equiv i.base (unitSheaf Y).1 U
        (mapHom U (unitsReduction i).hom (QuotientAddGroup.mk z))) = _
  exact (comparisonHom_pushforward (nilpotentClosedImmersionTopIso i hi)
    U (unitSheaf Y) hU.ge _).trans
      (congrArg (nilpotentUnitsCohomologyPushforwardEquiv i hi 1)
        (comparisonHom_naturality U (unitsReduction i) hU.ge _))

end UnitH1Pullback

namespace Group

open Langlands.Cohomology AbelianSheafCechH1 UnitCechH1Comparison
open NilpotentUnitReduction UnitSheafPushforward

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  (i : Y ⟶ X) [IsClosedImmersion i] (hi : IsNilpotent i.ker)

/-- Actual Picard pullback corresponds to actual unit reduction on cohomology. -/
theorem unitCohomologyClass_pullback (x : Group X) :
    unitCohomologyClass (pullback i x) =
      UnitH1Pullback.cohomologyMap i hi 1 (unitCohomologyClass x) := by
  let L := lineBundleRepresentative X x
  let D := L.finiteUnitPresentation
  let z : cocycles (unitSheaf X).1 D.cover.U := ⟨D.cochain, D.closed⟩
  have hx : (UnitCechLineBundle.lineBundle D.cover.U D.cover.iSup_eq_top
      z.1 z.2).classOf = x := by
    calc
      _ = L.classOf := (LineBundle.classOf_eq_iff _ _).mpr ⟨D.cochainIso.symm⟩
      _ = x := classOf_lineBundleRepresentative X x
  rw [← hx, UnitCechPullback.pullback_classOf]
  simp only [unitCohomologyClass_classOf]
  change (UnitCechLineBundle.lineBundle (fun a => i ⁻¹ᵁ D.cover.U a)
      (i.iSup_preimage_eq_top D.cover.iSup_eq_top)
      (UnitCechPullback.mapCocycles i D.cover.U z).1
      (UnitCechPullback.mapCocycles i D.cover.U z).2).unitCohomologyClass = _
  rw [LineBundle.unitCohomologyClass_glued, LineBundle.unitCohomologyClass_glued]
  exact UnitH1Pullback.classOfCocycle_pullback i hi D.cover.U D.cover.iSup_eq_top z

/-- Naturality of the published additive classifier for nilpotent closed immersions. -/
theorem unitCohomologyAddEquiv_pullback (x : Group X) :
    unitCohomologyAddEquiv Y (pullback i x) =
      UnitH1Pullback.cohomologyMap i hi 1 (unitCohomologyAddEquiv X x) :=
  unitCohomologyClass_pullback i hi x

/-- For a square-zero immersion, the existing reductionMap is actual Picard pullback. -/
theorem unitCohomologyClass_pullback_squareZero (hi : i.ker ^ 2 = ⊥) (x : Group X) :
    unitCohomologyClass (pullback i x) =
      SquareZeroUnitCohomology.reductionMap i hi 1 (unitCohomologyClass x) :=
  unitCohomologyClass_pullback i ⟨2, hi⟩ x

end Group

end Langlands.AlgebraicGeometry.Picard
