import Langlands.Geometry.FormalGroup.CentralScalarKernel
import Langlands.Geometry.FormalGroup.AtlasOrderMorphism
import Langlands.Geometry.FormalGroup.OrderIso

/-! # Comparing order atlases by their actual coordinate series -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {M N : ModuleLaw O R σ}
variable {E : OrderAction D M} {G : OrderAction D N}

/-- Identical formal addition and order series give an actual order isomorphism. -/
def ofIdenticalCoordinates (hadd : M.groupLaw.addition = N.groupLaw.addition)
    (horder : ∀ d, (E.action d).toHom.toCoordinateMap = (G.action d).toHom.toCoordinateMap) :
    Iso E G :=
  ofModuleIso (ModuleLaw.Iso.ofIdenticalCoordinates hadd (fun a => by
    have h := horder (algebraMap O D a)
    rw [E.action_algebraMap_eq_scalarHom, G.action_algebraMap_eq_scalarHom] at h
    simpa only [scalarHom, ModuleLaw.Hom.smul_toHom, ModuleLaw.Hom.id_toHom,
      CommLaw.Hom.comp_id] using h)) (fun d => by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp (E.action d).toHom.toCoordinateMap =
      (G.action d).toHom.toCoordinateMap.comp CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, horder])

end Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Iso

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X Y : BasicAtlas O R σ}
variable (E : OrderAction D X) (G : OrderAction D Y) (h : X.opens = Y.opens)

/-- The order law on a principal chart over an actual test algebra. -/
abbrev testOrder {X : BasicAtlas O R σ} (E : OrderAction D X) (B : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) := (E.chart b).map (coefficientLift (O := O) b.val B hb)

private def identityChartHom
    (hadd : ∀ (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val)),
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val B hb)).groupLaw.addition =
        ((Y.chart b).map (coefficientLift (O := O) b.val B hb)).groupLaw.addition)
    (horder : ∀ (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val)) (d : D),
      ((testOrder E B (sourceChart h b) hb).action d).toHom.toCoordinateMap =
        ((testOrder G B b hb).action d).toHom.toCoordinateMap)
    (htransition : ∀ (B : CommAlgCat.{v} R) (b c : Y.opens)
      (hb : IsUnit (algebraMap R B b.val)) (hc : IsUnit (algebraMap R B c.val)),
      (X.transition B (sourceChart h b) (sourceChart h c) hb hc).hom.toHom.toCoordinateMap =
        (Y.transition B b c hb hc).hom.toHom.toCoordinateMap) : Hom E G h := by
  let q (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val)) :=
    ModuleLaw.OrderAction.Iso.ofIdenticalCoordinates (E := testOrder E B (sourceChart h b) hb)
      (G := testOrder G B b hb) (hadd B b hb) (horder B b hb)
  refine ⟨⟨fun B b hb => (q B b hb).hom.val, ?_, ?_⟩, ?_⟩
  · intro B C φ b hb hc
    exact CoordinateMap.map_id φ.hom.toRingHom
  · intro B b c hb hc
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (Y.transition B b c hb hc).hom.toHom.toCoordinateMap.comp CoordinateMap.id =
      CoordinateMap.id.comp (X.transition B (sourceChart h b) (sourceChart h c) hb hc).hom.toHom.toCoordinateMap
    rw [CoordinateMap.comp_id, CoordinateMap.id_comp, htransition]
  · intro B b hb d
    exact (q B b hb).hom.commutes d

/-- Matching addition, order and transition series on the same cover give a genuine
order-linear isomorphism of the two atlases. -/
def ofIdenticalChartCoordinates
    (hadd : ∀ (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val)),
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val B hb)).groupLaw.addition =
        ((Y.chart b).map (coefficientLift (O := O) b.val B hb)).groupLaw.addition)
    (horder : ∀ (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val)) (d : D),
      ((testOrder E B (sourceChart h b) hb).action d).toHom.toCoordinateMap =
        ((testOrder G B b hb).action d).toHom.toCoordinateMap)
    (htransition : ∀ (B : CommAlgCat.{v} R) (b c : Y.opens)
      (hb : IsUnit (algebraMap R B b.val)) (hc : IsUnit (algebraMap R B c.val)),
      (X.transition B (sourceChart h b) (sourceChart h c) hb hc).hom.toHom.toCoordinateMap =
        (Y.transition B b c hb hc).hom.toHom.toCoordinateMap) : Iso E G h where
  hom := identityChartHom E G h hadd horder htransition
  inv := identityChartHom G E h.symm
    (fun B b hb => (hadd B (sourceChart h.symm b) hb).symm)
    (fun B b hb d => (horder B (sourceChart h.symm b) hb d).symm)
    (fun B b c hb hc => (htransition B (sourceChart h.symm b) (sourceChart h.symm c) hb hc).symm)
  inv_hom := by
    apply Subtype.ext
    apply BasicAtlas.Hom.ext
    intro B b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    exact CoordinateMap.id_comp _
  hom_inv := by
    apply Subtype.ext
    apply BasicAtlas.Hom.ext
    intro B b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    exact CoordinateMap.id_comp _

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Iso
