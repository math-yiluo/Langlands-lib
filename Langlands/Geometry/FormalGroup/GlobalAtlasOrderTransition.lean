import Langlands.Geometry.FormalGroup.GlobalAtlasOrderAction
import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus

/-! # Actual global-chart normalization through order-linear transitions -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Passing from the global frame into one chart and then through its actual
transition gives the same rational map as passing into the other chart. -/
theorem globalOrderChartQuasi_transition (E : ModuleLaw.OrderAction D M)
    (s : Set R) (hs : Ideal.span s = ⊤)
    (B : CommAlgCat.{v} R) (a b : s)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
        (globalOrderChartIso E a.val B ha)).symm.trans
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((ofGlobalCoverOrderAction E s hs).transitionIso B a b ha hb)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        (globalOrderChartIso E b.val B hb)).symm := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  apply ModuleLaw.OrderAction.RationalHom.ext
  change ModuleLaw.RationalHom.comp
    (ModuleLaw.RationalHom.ofHom ((ofGlobalCover M s hs).transition B a b ha hb).hom)
    (ModuleLaw.RationalHom.ofHom (globalChartIso M a.val B ha).inv) =
      ModuleLaw.RationalHom.ofHom (globalChartIso M b.val B hb).inv
  have hi : ((ofGlobalCover M s hs).transition B a b ha hb).hom.comp
      (globalChartIso M a.val B ha).inv = (globalChartIso M b.val B hb).inv := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id = CoordinateMap.id
    simp only [CoordinateMap.id_comp]
  exact (ModuleLaw.RationalHom.ofHom_comp (F := F)
    ((ofGlobalCover M s hs).transition B a b ha hb).hom
    (globalChartIso M a.val B ha).inv).symm.trans
      (congrArg (ModuleLaw.RationalHom.ofHom (F := F)) hi)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
