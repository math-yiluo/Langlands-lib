import Langlands.Geometry.FormalGroup.FormalIdempotentImageAtlas
import Langlands.Geometry.FormalGroup.AtlasMorphism

/-! # Integral maps between formal projector-image atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ σ' τ' υ' : Type}
variable [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ'] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {e : ModuleLaw.Hom M M} {d : ModuleLaw.Hom N N} {c : ModuleLaw.Hom P P}
variable (I : IdempotentImageCover e σ') (J : IdempotentImageCover d τ')
variable {h : I.atlas.opens = J.atlas.opens} (f : ModuleLaw.Hom M N) (hf : f.comp e = d.comp f)

include hf in
private theorem map_intertwines (A : CommAlgCat.{v} R) :
    (f.map (IsScalarTower.toAlgHom O R A)).comp (e.map (IsScalarTower.toAlgHom O R A)) =
      (d.map (IsScalarTower.toAlgHom O R A)).comp (f.map (IsScalarTower.toAlgHom O R A)) := by
  rw [← ModuleLaw.Hom.map_comp, ← ModuleLaw.Hom.map_comp, hf]

/-- An integral ambient map that intertwines the projectors restricts to a map of their
actual image atlases on a common principal cover. -/
def restrictHom : BasicAtlas.Hom I.atlas J.atlas h where
  hom A b hb := by
    let a := sourceChart (X := I.atlas) (Y := J.atlas) h b
    exact ((I.image a).2.overChartTest A hb).restrictHom
      ((J.image b).2.overChartTest A hb) (f.map (IsScalarTower.toAlgHom O R A))
  natural {A B} φ b ha hb := by
    dsimp only [ModuleLaw.Hom.IdempotentImage.restrictHom, ModuleLaw.Hom.comp_toHom,
      CommLaw.Hom.comp_toCoordinateMap]
    simp only [ModuleLaw.Hom.IdempotentImage.overChartTest_inclusion_coordinates,
      ModuleLaw.Hom.IdempotentImage.overChartTest_projection_coordinates, CoordinateMap.map_comp]
    have hc : φ.hom.toRingHom.comp (algebraMap R A) = algebraMap R B := RingHom.ext φ.hom.commutes
    have hJ : φ.hom.toRingHom.comp (coefficientLift (O := O) b.val A ha).toRingHom =
        (coefficientLift (O := O) b.val B hb).toRingHom :=
      congrArg AlgHom.toRingHom (coefficientLift_comp (O := O) b.val φ ha hb)
    let p := (J.image b).2.projection.toHom.toCoordinateMap
    let q := (I.image (sourceChart (X := I.atlas) (Y := J.atlas) h b)).2.inclusion.toHom.toCoordinateMap
    let α := (coefficientLift (O := O) b.val A ha).toRingHom
    let β := (coefficientLift (O := O) b.val B hb).toRingHom
    change ((p.map α).map φ.hom.toRingHom).comp
        (((f.toHom.toCoordinateMap.map (algebraMap R A)).map φ.hom.toRingHom).comp
          ((q.map α).map φ.hom.toRingHom)) =
      (p.map β).comp ((f.toHom.toCoordinateMap.map (algebraMap R B)).comp (q.map β))
    rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp,
      hc, show φ.hom.toRingHom.comp α = β from hJ]
  transition A b q hb hq := by
    let a := sourceChart (X := I.atlas) (Y := J.atlas) h b
    let a' := sourceChart (X := I.atlas) (Y := J.atlas) h q
    let L := (I.image a).2.overChartTest A hb
    let L' := (I.image a').2.overChartTest A hq
    let R₁ := (J.image b).2.overChartTest A hb
    let R₂ := (J.image q).2.overChartTest A hq
    let g := f.map (IsScalarTower.toAlgHom O R A)
    change (R₁.restrictHom R₂ (ModuleLaw.Hom.id _)).comp (L.restrictHom R₁ g) =
      (L'.restrictHom R₂ g).comp (L.restrictHom L' (ModuleLaw.Hom.id _))
    rw [← L.restrictHom_comp R₁ R₂ _ _ (map_intertwines f hf A),
      ← L.restrictHom_comp L' R₂ _ _ (by simp), ModuleLaw.Hom.id_comp, ModuleLaw.Hom.comp_id]

@[simp]
theorem restrictHom_onChart (A : CommAlgCat.{v} R) (b : J.atlas.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (I.restrictHom J (h := h) f hf).hom A b hb =
      ((I.image (sourceChart (X := I.atlas) (Y := J.atlas) h b)).2.overChartTest A hb).restrictHom
        ((J.image b).2.overChartTest A hb) (f.map (IsScalarTower.toAlgHom O R A)) := rfl

@[simp]
theorem restrictHom_id : I.restrictHom I (h := rfl) (ModuleLaw.Hom.id M) (by simp) =
    BasicAtlas.Hom.id I.atlas := by
  apply BasicAtlas.Hom.ext
  intro A b hb
  rw [restrictHom_onChart, ModuleLaw.Hom.map_id, ModuleLaw.Hom.IdempotentImage.restrictHom_id]
  rfl

/-- Restriction of integral ambient maps respects composition. -/
theorem restrictHom_comp (K : IdempotentImageCover c υ') {k : J.atlas.opens = K.atlas.opens}
    (g : ModuleLaw.Hom N P) (hg : g.comp d = c.comp g) :
    I.restrictHom K (h := h.trans k) (g.comp f) (by
      rw [ModuleLaw.Hom.comp_assoc, hf, ← ModuleLaw.Hom.comp_assoc, hg, ModuleLaw.Hom.comp_assoc]) =
    (J.restrictHom K (h := k) g hg).comp (I.restrictHom J (h := h) f hf) := by
  apply BasicAtlas.Hom.ext
  intro A b hb
  let a' := sourceChart (X := J.atlas) (Y := K.atlas) k b
  let a := sourceChart (X := I.atlas) (Y := J.atlas) h a'
  change ((I.image a).2.overChartTest A hb).restrictHom
      ((K.image b).2.overChartTest A hb) ((g.comp f).map (IsScalarTower.toAlgHom O R A)) =
    (((J.image a').2.overChartTest A hb).restrictHom
      ((K.image b).2.overChartTest A hb) (g.map (IsScalarTower.toAlgHom O R A))).comp
      (((I.image a).2.overChartTest A hb).restrictHom
        ((J.image a').2.overChartTest A hb) (f.map (IsScalarTower.toAlgHom O R A)))
  rw [ModuleLaw.Hom.map_comp]
  exact ModuleLaw.Hom.IdempotentImage.restrictHom_comp _ _ _ _ _ (map_intertwines f hf A)

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
