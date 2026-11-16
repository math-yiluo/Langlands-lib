import Langlands.GroupScheme.RelativeLevi.ParabolicLocalRepresentation
import Langlands.GroupScheme.RelativeLevi.ParabolicRepresentationBaseChange
import Langlands.GroupScheme.RelativeLevi.ParabolicFiniteTypesStatement

/-! # Smooth proper parabolic models on affine etale neighbourhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- An actual smooth proper scheme representing actual parabolic families. -/
structure SmoothProperModel (G : GroupScheme S) (hG : IsReductive G) where
  scheme : Over S
  represents : (parabolicPresheaf G hG).RepresentableBy scheme
  smooth : Smooth scheme.hom
  proper : IsProper scheme.hom

namespace SmoothProperModel

variable {hG : IsReductive G} (d : SmoothProperModel G hG)

/-- The same scheme represents restriction of the original presheaf along
the base slice, via the canonical direct/iterated pullback comparison. -/
def restrictedRepresentation {B : Scheme.{u}} {H : GroupScheme B}
    {hH : IsReductive H} (b : S ⟶ B)
    (d : SmoothProperModel ((GroupScheme.baseChange b).obj H) (hH.baseChange b)) :
    ((Over.map b).op ⋙ parabolicPresheaf H hH).RepresentableBy d.scheme :=
  d.represents.ofIso (parabolicPresheafBaseChangeIso b hH)

/-- An actual universal relative-parabolic inclusion on the representing scheme. -/
def universalFamily :
    Σ P : GroupScheme d.scheme.left,
      {j : P ⟶ (GroupScheme.baseChange d.scheme.hom).obj G //
        IsRelativeParabolicSubgroup j ∧ IsUniversal j} :=
  Classical.choice (by
    obtain ⟨P, j, hj, hu⟩ := exists_universal_of_representableBy hG d.represents
    exact ⟨⟨P, j, hj, hu⟩⟩)

/-- Supplied smooth proper parabolic models pull back along arbitrary base maps. -/
def baseChange (b : S' ⟶ S) :
    SmoothProperModel ((GroupScheme.baseChange b).obj G) (hG.baseChange b) where
  scheme := (Over.pullback b).obj d.scheme
  represents := representableByBaseChange b hG d.represents
  smooth := MorphismProperty.pullback_snd _ _ d.smooth
  proper := MorphismProperty.pullback_snd _ _ d.proper

end SmoothProperModel

/-- The actual finite quotient coproduct as a smooth proper parabolic model,
under the supplied uniform field-type condition. -/
def finiteAffineParabolicModel
    {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {I : Type u} [Finite I] {P : I → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ a, P a ⟶ G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a))
    (htypes : HasUniformParabolicFieldTypes j) : SmoothProperModel G hG where
  scheme := (finiteAffineParabolicQuotient hG j hj).val
  represents := finiteAffineParabolicRepresentation hG j hj htypes
  smooth := (finiteAffineParabolicQuotient hG j hj).property.1
  proper := (finiteAffineParabolicQuotient hG j hj).property.2

/-- An affine etale neighbourhood of a specified base point carrying an
actual smooth proper model of the pulled-back parabolic functor. -/
structure AffineEtaleModel (hG : IsReductive G) (s : S) where
  ring : Type u
  [commRing : CommRing ring]
  baseMap : Spec (CommRingCat.of ring) ⟶ S
  etale : Etale baseMap
  point : Spec (CommRingCat.of ring)
  point_over : baseMap.base point = s
  model : SmoothProperModel ((GroupScheme.baseChange baseMap).obj G)
    (hG.baseChange baseMap)

attribute [instance] AffineEtaleModel.commRing

/-- The published finite-type condition supplies an actual affine etale
neighbourhood with a smooth proper representing scheme at every point. -/
theorem nonempty_affineEtaleModel
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hG : IsReductive G) (s : S) : Nonempty (AffineEtaleModel hG s) := by
  obtain ⟨R, hR, f, hf, ⟨x, hx⟩, n, P, j, hj, htypes⟩ := hfin S G hG s
  let : CommRing R := hR
  let P' : ULift.{u} (Fin n) → GroupScheme (Spec (CommRingCat.of R)) :=
    fun a => P a.down
  let j' : ∀ a : ULift.{u} (Fin n), P' a ⟶ (GroupScheme.baseChange f).obj G :=
    fun a => j a.down
  have hj' (a : ULift.{u} (Fin n)) : IsRelativeParabolicSubgroup (j' a) := hj a.down
  have htypes' : HasUniformParabolicFieldTypes j' := by
    intro k _ z Q i hi
    obtain ⟨a, ha, hua⟩ := htypes k z Q i hi
    refine ⟨⟨a⟩, ha, ?_⟩
    intro b hb
    exact ULift.ext _ _ (hua b.down hb)
  exact ⟨⟨R, f, hf, x, hx,
    finiteAffineParabolicModel (hG.baseChange f) j' hj' htypes'⟩⟩

/-- Choose the actual local model supplied by the finite-type condition. -/
def affineEtaleModel
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hG : IsReductive G) (s : S) : AffineEtaleModel hG s :=
  Classical.choice (nonempty_affineEtaleModel hfin hG s)

/-- The chosen affine etale neighbourhoods cover the entire base scheme. -/
def affineEtaleModelCover
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hG : IsReductive G) : S.Cover (Scheme.precoverage @Etale) where
  I₀ := S
  X s := Spec (CommRingCat.of (affineEtaleModel hfin hG s).ring)
  f s := (affineEtaleModel hfin hG s).baseMap
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun s => ⟨s, (affineEtaleModel hfin hG s).point,
      (affineEtaleModel hfin hG s).point_over⟩,
      fun s => (affineEtaleModel hfin hG s).etale⟩

end Langlands.GroupScheme.ParabolicSubgroupModuli
