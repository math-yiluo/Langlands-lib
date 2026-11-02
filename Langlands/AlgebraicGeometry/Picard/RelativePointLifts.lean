import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian

/-! # Point lifts for relative spaces -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The base of the relative space associated to an arbitrary total-space map. -/
abbrev pointBase {T : Over S} {V : Scheme.{u}}
    (r : V ⟶ (relativeSpace f).obj T) : Over S :=
  Over.mk (r ≫ (relativeProjection f).app T ≫ T.hom)

/-- The base map determined by a lift of a total-space map. -/
def pointLift {T U : Over S} (h : U ⟶ T) {V : Scheme.{u}}
    (r : V ⟶ (relativeSpace f).obj T)
    (a : V ⟶ (relativeSpace f).obj U) (ha : a ≫ (relativeSpace f).map h = r) :
    pointBase f r ⟶ U :=
  Over.homMk (a ≫ (relativeProjection f).app U) (by
    change (a ≫ (relativeProjection f).app U) ≫ U.hom =
      r ≫ (relativeProjection f).app T ≫ T.hom
    calc
      _ = a ≫ (relativeProjection f).app U ≫ h.left ≫ T.hom := by
        rw [Over.w h, Category.assoc]
      _ = (a ≫ (relativeSpace f).map h) ≫ (relativeProjection f).app T ≫ T.hom := by
        simpa only [Category.assoc, Over.forget_map] using
          congrArg (fun z ↦ a ≫ z ≫ T.hom) ((relativeProjection f).naturality h).symm
      _ = _ := by rw [ha])

/-- The point section recovers any lift of the chosen total-space map. -/
@[reassoc]
lemma pointLift_section {T U : Over S} (h : U ⟶ T) {V : Scheme.{u}}
    (r : V ⟶ (relativeSpace f).obj T)
    (a : V ⟶ (relativeSpace f).obj U) (ha : a ≫ (relativeSpace f).map h = r) :
    relativePointSection f r ≫ (relativeSpace f).map (pointLift f h r a ha) = a := by
  apply pullback.hom_ext
  · change relativePointSection f r ≫
      (relativeSpace f).map (pointLift f h r a ha) ≫ (relativeProjection f).app U =
        a ≫ (relativeProjection f).app U
    rw [(relativeProjection f).naturality, ← Category.assoc,
      relativePointSection_projection, Category.id_comp]
    rfl
  · rw [Category.assoc, relativeSpace_map_snd]
    calc
      _ = r ≫ pullback.snd T.hom f := relativePointSection_snd f r
      _ = _ := by rw [← ha, Category.assoc, relativeSpace_map_snd]

/-- The two base lifts have the same composite whenever their total-space lifts do. -/
lemma pointLift_comp {T U : Over S} (h : U ⟶ T) {V : Scheme.{u}}
    (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r)
    (hb : b ≫ (relativeSpace f).map h = r) :
    pointLift f h r a ha ≫ h = pointLift f h r b hb ≫ h := by
  apply (Over.forget S).map_injective
  change (a ≫ (relativeProjection f).app U) ≫ h.left =
    (b ≫ (relativeProjection f).app U) ≫ h.left
  have hn : (relativeProjection f).app U ≫ h.left =
      (relativeSpace f).map h ≫ (relativeProjection f).app T :=
    ((relativeProjection f).naturality h).symm
  rw [Category.assoc, Category.assoc, hn, ← Category.assoc, ← Category.assoc, ha, hb]

/-- Precomposition on the base attached to an arbitrary point. -/
def pointBaseMap {T : Over S} {V W : Scheme.{u}} (k : W ⟶ V)
    (r : V ⟶ (relativeSpace f).obj T) :
    pointBase f (k ≫ r) ⟶ pointBase f r :=
  Over.homMk k (by simp only [pointBase, Over.mk_hom, Category.assoc])

/-- Base lifts commute with precomposition. -/
lemma pointLift_precomp {T U : Over S} (h : U ⟶ T) {V W : Scheme.{u}} (k : W ⟶ V)
    (r : V ⟶ (relativeSpace f).obj T)
    (a : V ⟶ (relativeSpace f).obj U) (ha : a ≫ (relativeSpace f).map h = r)
    (hka : (k ≫ a) ≫ (relativeSpace f).map h = k ≫ r) :
    pointBaseMap f k r ≫ pointLift f h r a ha =
      pointLift f h (k ≫ r) (k ≫ a) hka := by
  apply (Over.forget S).map_injective
  change k ≫ (a ≫ (relativeProjection f).app U) =
    (k ≫ a) ≫ (relativeProjection f).app U
  exact (Category.assoc _ _ _).symm

/-- The point sections commute with precomposition on their domains. -/
lemma pointSection_precomp {T : Over S} {V W : Scheme.{u}} (k : W ⟶ V)
    (r : V ⟶ (relativeSpace f).obj T) :
    relativePointSection f (k ≫ r) ≫ (relativeSpace f).map (pointBaseMap f k r) =
      k ≫ relativePointSection f r := by
  apply pullback.hom_ext
  · change relativePointSection f (k ≫ r) ≫
      (relativeSpace f).map (pointBaseMap f k r) ≫
        (relativeProjection f).app (pointBase f r) =
      k ≫ relativePointSection f r ≫ (relativeProjection f).app (pointBase f r)
    rw [(relativeProjection f).naturality, ← Category.assoc,
      relativePointSection_projection, Category.id_comp,
      relativePointSection_projection, Category.comp_id]
    rfl
  · rw [Category.assoc, relativeSpace_map_snd]
    calc
      _ = (k ≫ r) ≫ pullback.snd T.hom f := relativePointSection_snd f (k ≫ r)
      _ = k ≫ (r ≫ pullback.snd T.hom f) := Category.assoc _ _ _
      _ = _ := by
        rw [Category.assoc]
        exact congrArg (fun z ↦ k ≫ z) (relativePointSection_snd f r).symm

end Langlands.AlgebraicGeometry.Picard
