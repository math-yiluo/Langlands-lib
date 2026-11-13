import Langlands.Cohomology.AbelianSheafH1Pullback
import Langlands.AlgebraicGeometry.Picard.UnitCechPullback
import Langlands.AlgebraicGeometry.Picard.UnitH1AddEquiv
import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitCohomology

/-! # Actual Picard pullback and unit cohomology for arbitrary morphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard

namespace UnitH1MorphismPullback

open Langlands.Cohomology Cech AbelianSheafCechH1
open AbelianSheafH1Naturality AbelianSheafH1Pullback AbelianSheafCohomologyPullback
open UnitCechH1Comparison NilpotentUnitReduction UnitSheafPushforward

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- Actual unit cohomology pullback for an arbitrary scheme morphism. -/
def cohomologyMap (n : ℕ) :
    Sheaf.H.{u} (unitSheaf X) n →+ Sheaf.H.{u} (unitSheaf Y) n :=
  pushforwardMap i.base (unitsReduction i) n

variable {ι : Type u} [Finite ι] (U : ι → X.Opens)

/-- The class of the pulled unit cocycle is actual unit reduction in H¹. -/
theorem classOfCocycle_pullback (hU : (⨆ a, U a) = ⊤)
    (z : cocycles (unitSheaf X).1 U) :
    classOfCocycle (fun a => i ⁻¹ᵁ U a) (i.iSup_preimage_eq_top hU)
        (UnitCechPullback.mapCocycles i U z) =
      cohomologyMap i 1 (classOfCocycle U hU z) := by
  change comparisonHom (unitSheaf Y) (fun a => i ⁻¹ᵁ U a) _
      (CechPullback.h1Equiv i.base (unitSheaf Y).1 U
        (mapHom U (unitsReduction i).hom (QuotientAddGroup.mk z))) = _
  unfold cohomologyMap classOfCocycle
  exact comparisonHom_pullback i.base (A := unitSheaf X) (B := unitSheaf Y)
    (unitsReduction i) U hU.ge (QuotientAddGroup.mk z)

end UnitH1MorphismPullback

namespace Group

open Langlands.Cohomology AbelianSheafCechH1 UnitCechH1Comparison
open NilpotentUnitReduction UnitSheafPushforward

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  (i : Y ⟶ X)

/-- Actual Picard pullback corresponds to actual unit reduction on cohomology. -/
theorem unitCohomologyClass_pullback_morphism (x : Group X) :
    unitCohomologyClass (pullback i x) =
      UnitH1MorphismPullback.cohomologyMap i 1 (unitCohomologyClass x) := by
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
  exact UnitH1MorphismPullback.classOfCocycle_pullback i D.cover.U D.cover.iSup_eq_top z

/-- Naturality of the published additive classifier for arbitrary scheme morphisms. -/
theorem unitCohomologyAddEquiv_pullback_morphism (x : Group X) :
    unitCohomologyAddEquiv Y (pullback i x) =
      UnitH1MorphismPullback.cohomologyMap i 1 (unitCohomologyAddEquiv X x) :=
  unitCohomologyClass_pullback_morphism i x

end Group

end Langlands.AlgebraicGeometry.Picard
