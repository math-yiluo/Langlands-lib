import Langlands.Geometry.FormalGroup.FormalIdempotentTransport
import Langlands.Geometry.FormalGroup.GlobalAtlas

/-! # The formal atlas constructed from local presentations of a projector image -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {e : Hom M M}

namespace Hom.IdempotentImage

variable {a : R} {N : ModuleLaw O (Localization.Away a) τ}
variable (P : IdempotentImage (e.map (IsScalarTower.toAlgHom O R (Localization.Away a))) N)
variable (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a))

/-- The chart retraction over a test algebra lands in the original ambient law
extended directly from the base. -/
def overChartTest : IdempotentImage (e.map (IsScalarTower.toAlgHom O R A))
    (N.map (BasicAtlas.coefficientLift (O := O) a A ha)) :=
  (P.map (BasicAtlas.coefficientLift (O := O) a A ha)).transport
    (BasicAtlas.globalChartIso M a A ha) (by
      apply Hom.ext
      apply CommLaw.Hom.ext
      change CoordinateMap.id.comp ((e.toHom.toCoordinateMap.map
        (algebraMap R (Localization.Away a))).map
        (BasicAtlas.coefficientLift (O := O) a A ha).toRingHom) =
        (e.toHom.toCoordinateMap.map (algebraMap R A)).comp CoordinateMap.id
      rw [CoordinateMap.id_comp, CoordinateMap.comp_id, CoordinateMap.map_ringHom_comp,
        BasicAtlas.globalCoefficient_comp])

@[simp]
theorem overChartTest_inclusion_coordinates :
    (P.overChartTest A ha).inclusion.toHom.toCoordinateMap =
      P.inclusion.toHom.toCoordinateMap.map (BasicAtlas.coefficientLift (O := O) a A ha).toRingHom :=
  CoordinateMap.id_comp _

@[simp]
theorem overChartTest_projection_coordinates :
    (P.overChartTest A ha).projection.toHom.toCoordinateMap =
      P.projection.toHom.toCoordinateMap.map (BasicAtlas.coefficientLift (O := O) a A ha).toRingHom :=
  CoordinateMap.comp_id _

variable {N' : ModuleLaw O R τ} {P' : ModuleLaw O R υ}

/-- The comparison of two image charts is the source inclusion followed by the target projection. -/
theorem iso_hom (I : IdempotentImage e N') (J : IdempotentImage e P') :
    (I.iso J).hom = J.projection.comp I.inclusion := by
  change J.projection.comp ((Hom.id M).comp I.inclusion) = _
  rw [Hom.id_comp]

end Hom.IdempotentImage

/-- Local finite-coordinate presentations of the same actual formal projector. -/
structure IdempotentImageCover (e : Hom M M) (τ : Type) [Finite τ] where
  opens : Set R
  covers : Ideal.span opens = ⊤
  image : (a : opens) → Σ N : ModuleLaw O (Localization.Away a.val) τ,
    Hom.IdempotentImage (e.map (IsScalarTower.toAlgHom O R (Localization.Away a.val))) N

namespace IdempotentImageCover

variable (C : IdempotentImageCover e τ)

/-- The actual formal atlas, with transitions formed inside a common ambient law. -/
def atlas : BasicAtlas O R τ where
  opens := C.opens
  covers := C.covers
  chart a := (C.image a).1
  transition A a b ha hb := ((C.image a).2.overChartTest A ha).iso
    ((C.image b).2.overChartTest A hb)
  transition_self A a ha := by
    apply Iso.ext_hom
    exact ((C.image a).2.overChartTest A ha).restrictHom_id
  transition_cocycle A a b c ha hb hc := by
    let I := (C.image a).2.overChartTest A ha
    let J := (C.image b).2.overChartTest A hb
    let K := (C.image c).2.overChartTest A hc
    apply Iso.ext_hom
    change (J.restrictHom K (Hom.id _)).comp (I.restrictHom J (Hom.id _)) =
      I.restrictHom K (Hom.id _)
    rw [← I.restrictHom_comp J K _ _ (by simp), Hom.comp_id]
  transition_natural φ a b ha hb ha' hb' := by
    simp only [Hom.IdempotentImage.iso_hom, Hom.comp_toHom, CommLaw.Hom.comp_toCoordinateMap,
      Hom.IdempotentImage.overChartTest_projection_coordinates,
      Hom.IdempotentImage.overChartTest_inclusion_coordinates, CoordinateMap.map_comp,
      CoordinateMap.map_ringHom_comp]
    refine congrArg₂ CoordinateMap.comp ?_ ?_
    · exact congrArg (fun f : Localization.Away b.val →ₐ[O] _ =>
        (C.image b).2.projection.toHom.toCoordinateMap.map f.toRingHom)
        (BasicAtlas.coefficientLift_comp (O := O) b.val φ hb hb')
    · exact congrArg (fun f : Localization.Away a.val →ₐ[O] _ =>
        (C.image a).2.inclusion.toHom.toCoordinateMap.map f.toRingHom)
        (BasicAtlas.coefficientLift_comp (O := O) a.val φ ha ha')

end IdempotentImageCover

end Langlands.FormalGroup.ModuleLaw
