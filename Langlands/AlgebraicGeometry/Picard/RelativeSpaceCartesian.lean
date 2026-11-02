import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Cartesian relative spaces and points of their base changes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- A relative-space morphism lies in the base-change square of its base morphism. -/
lemma relativeProjection_isPullback {T U : Over S} (h : U ⟶ T) :
    IsPullback ((relativeSpace f).map h) ((relativeProjection f).app U)
      ((relativeProjection f).app T) h.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd T.hom f) (v₁₃ := f)
    (h₂₂ := T.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom f).flip
  · simpa [relativeSpace, Over.pullback, relativeProjection, pullback.lift_snd,
      Over.w h] using
      (IsPullback.of_hasPullback U.hom f).flip
  · simp [relativeSpace, Over.pullback, relativeProjection, pullback.lift_fst]

/-- Every base-change-stable morphism property passes to the actual relative-space map. -/
lemma relativeSpace_map_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {T U : Over S} (h : U ⟶ T) (hh : P h.left) :
    P ((relativeSpace f).map h) :=
  P.of_isPullback (relativeProjection_isPullback f h).flip hh

lemma relativeSpace_map_isAffineHom {T U : Over S} (h : U ⟶ T)
    [IsAffineHom h.left] : IsAffineHom ((relativeSpace f).map h) :=
  relativeSpace_map_property f @IsAffineHom h inferInstance

lemma relativeSpace_map_flat {T U : Over S} (h : U ⟶ T)
    [Flat h.left] : Flat ((relativeSpace f).map h) :=
  relativeSpace_map_property f @Flat h inferInstance

lemma relativeSpace_map_surjective {T U : Over S} (h : U ⟶ T)
    [Surjective h.left] : Surjective ((relativeSpace f).map h) :=
  relativeSpace_map_property f @Surjective h inferInstance

lemma relativeSpace_map_quasiCompact {T U : Over S} (h : U ⟶ T)
    [QuasiCompact h.left] : QuasiCompact ((relativeSpace f).map h) :=
  relativeSpace_map_property f @QuasiCompact h inferInstance

/-- A map to the fixed family gives a section of its base change to its own domain. -/
def relativePointSection {T : Over S} {V : Scheme.{u}}
    (a : V ⟶ (relativeSpace f).obj T) :
    V ⟶ (relativeSpace f).obj
      (Over.mk (a ≫ (relativeProjection f).app T ≫ T.hom)) :=
  pullback.lift (𝟙 V) (a ≫ pullback.snd T.hom f) (by
    change (𝟙 V) ≫ (a ≫ pullback.fst T.hom f ≫ T.hom) =
      (a ≫ pullback.snd T.hom f) ≫ f
    simp only [Category.id_comp, Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma relativePointSection_projection {T : Over S} {V : Scheme.{u}}
    (a : V ⟶ (relativeSpace f).obj T) :
    relativePointSection f a ≫
      (relativeProjection f).app
        (Over.mk (a ≫ (relativeProjection f).app T ≫ T.hom)) = 𝟙 V :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativePointSection_snd {T : Over S} {V : Scheme.{u}}
    (a : V ⟶ (relativeSpace f).obj T) :
    relativePointSection f a ≫
      pullback.snd (a ≫ (relativeProjection f).app T ≫ T.hom) f =
        a ≫ pullback.snd T.hom f :=
  pullback.lift_snd _ _ _

/-- Pulling back along the base map recovers the original arbitrary total-space map. -/
@[reassoc]
lemma relativePointSection_map {T : Over S} {V : Scheme.{u}}
    (a : V ⟶ (relativeSpace f).obj T) :
    relativePointSection f a ≫
      (relativeSpace f).map
        (Over.homMk (a ≫ (relativeProjection f).app T) :
          Over.mk (a ≫ (relativeProjection f).app T ≫ T.hom) ⟶ T) = a := by
  apply pullback.hom_ext
  · change relativePointSection f a ≫
        (relativeSpace f).map _ ≫ (relativeProjection f).app T =
      a ≫ (relativeProjection f).app T
    rw [(relativeProjection f).naturality, ← Category.assoc,
      relativePointSection_projection, Category.id_comp]
    rfl
  · change relativePointSection f a ≫
        (relativeSpace f).map _ ≫ pullback.snd T.hom f = a ≫ pullback.snd T.hom f
    simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
      pullback.lift_snd]
    exact relativePointSection_snd f a

end Langlands.AlgebraicGeometry.Picard
