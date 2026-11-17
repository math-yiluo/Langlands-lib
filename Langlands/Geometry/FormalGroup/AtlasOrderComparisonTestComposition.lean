import Langlands.Geometry.FormalGroup.AtlasOrderComparisonTestBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeComposition
import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus

/-! # Actual test-comparison naturality for successive coefficient extension -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The complete extended test-comparison series retains any specified original finer chart. -/
theorem testIso_baseChange_hom_coordinates (c : Comparison E E') (S : CommAlgCat.{v} R)
    (C : CommAlgCat.{v} S) (b : c.right.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S C b.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictTest S C) a.val))
    (x : X.baseOpens S) (y : Y.baseOpens S)
    (hx : IsUnit (algebraMap S C x.val)) (hy : IsUnit (algebraMap S C y.val)) :
    ((c.baseChange S).testIso C b hb x y hx hy).hom.val.toHom.toCoordinateMap =
      (c.testIso (restrictTest S C) a ha (X.baseSource S x) (Y.baseSource S y)
        (X.baseSource_unit S C x hx) (Y.baseSource_unit S C y hy)).hom.val.toHom.toCoordinateMap := by
  have h := congrArg (fun z => z.hom.val.toHom.toCoordinateMap)
    (c.testIso_baseChange_eq_original S C b hb a ha x y hx hy)
  change ((c.baseChange S).testIso C b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    (CoordinateMap.id.comp
      (c.testIso (restrictTest S C) a ha (X.baseSource S x) (Y.baseSource S y)
        (X.baseSource_unit S C x hx) (Y.baseSource_unit S C y hy)).hom.val.toHom.toCoordinateMap).comp
          CoordinateMap.id at h
  simpa only [CoordinateMap.id_comp, CoordinateMap.comp_id] using h

/-- The actual test comparison intertwines changes of its two outer original charts. -/
theorem testIso_transition (c : Comparison E E') (A : CommAlgCat.{v} R)
    (a : c.right.opens) (ha : IsUnit (algebraMap R A a.val))
    (x₁ x₂ : X.opens) (y₁ y₂ : Y.opens)
    (hx₁ : IsUnit (algebraMap R A x₁.val)) (hx₂ : IsUnit (algebraMap R A x₂.val))
    (hy₁ : IsUnit (algebraMap R A y₁.val)) (hy₂ : IsUnit (algebraMap R A y₂.val)) :
    (c.testIso A a ha x₁ y₁ hx₁ hy₁).trans (E'.transitionIso A y₁ y₂ hy₁ hy₂) =
      (E.transitionIso A x₁ x₂ hx₁ hx₂).trans (c.testIso A a ha x₂ y₂ hx₂ hy₂) := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (Y.transition A y₁ y₂ hy₁ hy₂).hom.toHom.toCoordinateMap.comp
      (c.testIso A a ha x₁ y₁ hx₁ hy₁).hom.val.toHom.toCoordinateMap =
    (c.testIso A a ha x₂ y₂ hx₂ hy₂).hom.val.toHom.toCoordinateMap.comp
      (X.transition A x₁ x₂ hx₁ hx₂).hom.toHom.toCoordinateMap
  rw [testIso_hom_coordinates, testIso_hom_coordinates]
  let s := c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a)
  have hs : IsUnit (algebraMap R A s.val) := c.left.source_unit A _ ha
  have hX := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A x₁ x₂ s hx₁ hx₂ hs)
  have hY := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (Y.transition_cocycle A (c.right.source a) y₁ y₂ (c.right.source_unit A a ha) hy₁ hy₂)
  change (X.transition A x₂ s _ _).hom.toHom.toCoordinateMap.comp
      (X.transition A x₁ x₂ _ _).hom.toHom.toCoordinateMap =
    (X.transition A x₁ s _ _).hom.toHom.toCoordinateMap at hX
  change (Y.transition A y₁ y₂ _ _).hom.toHom.toCoordinateMap.comp
      (Y.transition A (c.right.source a) y₁ _ _).hom.toHom.toCoordinateMap =
    (Y.transition A (c.right.source a) y₂ _ _).hom.toHom.toCoordinateMap at hY
  simp only [CoordinateMap.comp_assoc]
  rw [hX, ← CoordinateMap.comp_assoc, hY]

set_option backward.isDefEq.respectTransparency false in
/-- The actual successive-coefficient comparison intertwines the two specified test comparisons. -/
theorem testIso_baseComp (c : Comparison E E') (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) (C : CommAlgCat.{v} T)
    (b : ((c.baseChange S).baseChange T).right.opens)
    (hb : IsUnit (algebraMap T C b.val))
    (d : (c.baseChange (restrictTest S T)).right.opens)
    (hd : IsUnit (algebraMap T C d.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictTest (restrictTest S T) C) a.val))
    (x : X.baseOpens (restrictTest S T)) (y : Y.baseOpens (restrictTest S T))
    (hx : IsUnit (algebraMap T C x.val)) (hy : IsUnit (algebraMap T C y.val)) :
    (((c.baseChange S).baseChange T).testIso C b hb
      (sourceChart (X.baseCompOpens_eq S T) x) (sourceChart (Y.baseCompOpens_eq S T) y)
      hx hy).trans ((E'.baseCompIso S T).onChart C y hy) =
      ((E.baseCompIso S T).onChart C x hx).trans
        ((c.baseChange (restrictTest S T)).testIso C d hd x y hx hy) := by
  let B := restrictTest T C
  let A := restrictTest (restrictTest S T) C
  let m := (c.baseChange S).right.atlas.baseSource T b
  have hm : IsUnit (algebraMap S B m.val) :=
    (c.baseChange S).right.atlas.baseSource_unit T C b hb
  let xx := sourceChart (X.baseCompOpens_eq S T) x
  let yy := sourceChart (Y.baseCompOpens_eq S T) y
  have hn := (c.baseChange S).testIso_baseChange_hom_coordinates T C b hb m hm xx yy hx hy
  have hi := c.testIso_baseChange_hom_coordinates S B m hm a ha
    ((X.baseChange S).baseSource T xx) ((Y.baseChange S).baseSource T yy)
    ((X.baseChange S).baseSource_unit T C xx hx) ((Y.baseChange S).baseSource_unit T C yy hy)
  have hd' := c.testIso_baseChange_hom_coordinates (restrictTest S T) C d hd a ha x y hx hy
  have ht := congrArg (fun z => z.hom.val.toHom.toCoordinateMap)
    (c.testIso_transition A a ha
      (X.baseCompIterSource S T x) (X.baseSource (restrictTest S T) x)
      (Y.baseCompIterSource S T y) (Y.baseSource (restrictTest S T) y)
      (X.baseCompIter_unit S T C x hx) (X.baseSource_unit (restrictTest S T) C x hx)
      (Y.baseCompIter_unit S T C y hy) (Y.baseSource_unit (restrictTest S T) C y hy))
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (Y.baseCompChartIso S T C y hy).hom.toHom.toCoordinateMap.comp
      (((c.baseChange S).baseChange T).testIso C b hb xx yy hx hy).hom.val.toHom.toCoordinateMap =
    ((c.baseChange (restrictTest S T)).testIso C d hd x y hx hy).hom.val.toHom.toCoordinateMap.comp
      (X.baseCompChartIso S T C x hx).hom.toHom.toCoordinateMap
  rw [X.baseCompChartIso_coordinates, Y.baseCompChartIso_coordinates, hn, hi, hd']
  exact ht

variable [IsDomain O] {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]

/-- The four actual rationalized test maps with their successive-coefficient naturality equation. -/
def baseCompTestSquare (c : Comparison E E') (S : CommAlgCat.{v} R)
    (T : CommAlgCat.{v} S) (C : CommAlgCat.{v} T)
    (b : ((c.baseChange S).baseChange T).right.opens)
    (hb : IsUnit (algebraMap T C b.val))
    (d : (c.baseChange (restrictTest S T)).right.opens)
    (hd : IsUnit (algebraMap T C d.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictTest (restrictTest S T) C) a.val))
    (x : X.baseOpens (restrictTest S T)) (y : Y.baseOpens (restrictTest S T))
    (hx : IsUnit (algebraMap T C x.val)) (hy : IsUnit (algebraMap T C y.val)) :=
  let n := ((c.baseChange S).baseChange T).testIso C b hb
    (sourceChart (X.baseCompOpens_eq S T) x) (sourceChart (Y.baseCompOpens_eq S T) y) hx hy
  let r := (E'.baseCompIso S T).onChart C y hy
  let l := (E.baseCompIso S T).onChart C x hx
  let d' := (c.baseChange (restrictTest S T)).testIso C d hd x y hx hy
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F) n)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F) r)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F) l)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F) d') (by
      apply ModuleLaw.OrderAction.QuasiIsogeny.ext
      apply ModuleLaw.OrderAction.RationalHom.ext
      have h := congrArg (fun z => z.hom.val)
        (c.testIso_baseComp S T C b hb d hd a ha x y hx hy)
      exact (ModuleLaw.RationalHom.ofHom_comp (F := F) r.hom.val n.hom.val).symm.trans
        ((congrArg (fun z => ModuleLaw.RationalHom.ofHom (F := F) z) h).trans
          (ModuleLaw.RationalHom.ofHom_comp (F := F) d'.hom.val l.hom.val)))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison
