import Langlands.AlgebraicGeometry.StrictLocalEtaleLimit
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocalization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Pointed local affine etale limits and localization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

/-- A local affine scheme presented as a pointed affine etale limit.
Henselianity and separable closedness are not required. -/
structure LocalEtaleLimit (S : Scheme.{u}) (s : S) where
  ring : Type u
  [commRing : CommRing ring]
  [localRing : IsLocalRing ring]
  index : Type u
  [category : Category.{u} index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ Scheme.{u}
  [affine : ∀ i, IsAffine (diagram.obj i)]
  structural : diagram ⟶ (Functor.const index).obj S
  [etale : ∀ i, Etale (structural.app i)]
  projection : (Functor.const index).obj (Spec (CommRingCat.of ring)) ⟶ diagram
  baseMap : Spec (CommRingCat.of ring) ⟶ S
  compatible : ∀ i, projection.app i ≫ structural.app i = baseMap
  isLimit : IsLimit (Cone.mk (Spec (CommRingCat.of ring)) projection)
  closedPoint_image : baseMap (IsLocalRing.closedPoint ring) = s

attribute [instance] LocalEtaleLimit.commRing LocalEtaleLimit.localRing
  LocalEtaleLimit.category LocalEtaleLimit.cofiltered LocalEtaleLimit.affine
  LocalEtaleLimit.etale

namespace StrictLocalEtaleLimit

/-- Forget the two strict-Henselian properties of a supplied presentation. -/
def toLocal {S : Scheme.{u}} {s : S} (L : StrictLocalEtaleLimit S s) : LocalEtaleLimit S s where
  ring := L.ring
  index := L.index
  diagram := L.diagram
  structural := L.structural
  projection := L.projection
  baseMap := L.baseMap
  compatible := L.compatible
  isLimit := L.isLimit
  closedPoint_image := L.closedPoint_image

end StrictLocalEtaleLimit

namespace LocalEtaleLimit

open UnramifiedFunctor.Charts

variable (R : Type u) [CommRing R] (p : PrimeSpectrum R)

private def locRings : DivIndex p.asIdeal.primeCompl ⥤ CommRingCat.{u} :=
  awayDiagram p.asIdeal.primeCompl ⋙ Under.forget (CommRingCat.of R)

private def locRingCocone : Cocone (locRings R p) :=
  (Under.forget (CommRingCat.of R)).mapCocone
    (awayCocone p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))

private def locRingIsColimit : IsColimit (locRingCocone R p) :=
  isColimitOfPreserves (Under.forget (CommRingCat.of R))
    (awayCoconeIsColimit p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))

private def locDiagram : (DivIndex p.asIdeal.primeCompl)ᵒᵖ ⥤ Scheme.{u} :=
  (locRings R p).op ⋙ Scheme.Spec

private def locCone : Cone (locDiagram R p) :=
  Scheme.Spec.mapCone (locRingCocone R p).op

private def locConeIsLimit : IsLimit (locCone R p) :=
  isLimitOfPreserves Scheme.Spec (locRingIsColimit R p).op

private def locStructural : locDiagram R p ⟶
    (Functor.const _).obj (Spec (CommRingCat.of R)) where
  app i := Spec.algebraMap R (Localization.Away i.unop.val)
  naturality := by
    intro i j a
    change Spec.map (CommRingCat.ofHom (awayMap (leOfHom a.unop))) ≫
      Spec.algebraMap R (Localization.Away j.unop.val) =
        Spec.algebraMap R (Localization.Away i.unop.val) ≫ 𝟙 _
    rw [Category.comp_id, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, awayMap_comp_algebraMap]

/-- The actual spectrum of the local ring at a prime is the pointed
cofiltered affine etale limit of basic affine opens through that prime. -/
def ofLocalization : LocalEtaleLimit (Spec (CommRingCat.of R)) p where
  ring := Localization.AtPrime p.asIdeal
  index := (DivIndex p.asIdeal.primeCompl)ᵒᵖ
  diagram := locDiagram R p
  affine := fun i => by
    change IsAffine (Spec (CommRingCat.of (Localization.Away i.unop.val)))
    infer_instance
  structural := locStructural R p
  etale := fun i => by
    change Etale (Spec.algebraMap R (Localization.Away i.unop.val))
    infer_instance
  projection := (locCone R p).π
  baseMap := Spec.algebraMap R (Localization.AtPrime p.asIdeal)
  compatible := by
    intro i
    change Spec.map (CommRingCat.ofHom
        (toLoc p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) i.unop)) ≫
      Spec.algebraMap R (Localization.Away i.unop.val) =
        Spec.algebraMap R (Localization.AtPrime p.asIdeal)
    rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    exact toLoc_algebraMap p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) i.unop r
  isLimit := locConeIsLimit R p
  closedPoint_image := by
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal

@[simp]
theorem ofLocalization_baseMap :
    (ofLocalization R p).baseMap = Spec.algebraMap R (Localization.AtPrime p.asIdeal) := rfl

end LocalEtaleLimit

end Langlands.AlgebraicGeometry
