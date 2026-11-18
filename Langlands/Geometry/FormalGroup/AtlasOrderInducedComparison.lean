import Langlands.Geometry.FormalGroup.AtlasOrderCoefficientUnit

/-! # Refined comparisons induced by actual same-cover atlas isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restrict both actual maps of a same-cover isomorphism to the supplied finer cover. -/
def ofIso (f : Iso E E' h) (q : CoverRefinement X) : Comparison E E' where
  left := q
  right := q.retarget Y h
  sameCover := rfl
  coordinateIso := f.restrict q

/-- The complete formal test comparisons are those of a specified actual atlas isomorphism. -/
def InducedBy (c : Comparison E E') (f : Iso E E' h) : Prop :=
  ∀ (A : CommAlgCat.{v} R) (b : c.right.opens)
    (hb : IsUnit (algebraMap R A b.val)) (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)),
    c.testIso A b hb x y hx hy =
      (E.transitionIso A x (sourceChart h y) hx hy).trans (f.onChart A y hy)

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an actual atlas isomorphism retains its complete formal test maps. -/
theorem inducedBy_ofIso (f : Iso E E' h) (q : CoverRefinement X) :
    (ofIso f q).InducedBy f := by
  intro A b hb x y hx hy
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change ((ofIso f q).testIso A b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    (f.hom.val.hom A y hy).toHom.toCoordinateMap.comp
      (X.transition A x (sourceChart h y) hx hy).hom.toHom.toCoordinateMap
  rw [testIso_hom_coordinates]
  simp only [ofIso, Iso.restrict, Hom.restrict, BasicAtlas.Hom.restrict_coordinates]
  let a := sourceChart (X := Y) (Y := X) h.symm (q.source b)
  have ha : IsUnit (algebraMap R A a.val) := q.source_unit A b hb
  have ht := congrArg (fun z => z.toHom.toCoordinateMap)
    (f.hom.val.transition A a y ha hy)
  have hc := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A x (q.source b) (sourceChart h y) hx
      (q.source_unit A b hb) hy)
  change (Y.transition A a y ha hy).hom.toHom.toCoordinateMap.comp
    (f.hom.val.hom A a ha).toHom.toCoordinateMap =
      (f.hom.val.hom A y hy).toHom.toCoordinateMap.comp
        (X.transition A (q.source b) (sourceChart h y) (q.source_unit A b hb) hy).hom.toHom.toCoordinateMap at ht
  change (X.transition A (q.source b) (sourceChart h y) _ _).hom.toHom.toCoordinateMap.comp
    (X.transition A x (q.source b) _ _).hom.toHom.toCoordinateMap =
      (X.transition A x (sourceChart h y) _ _).hom.toHom.toCoordinateMap at hc
  change ((Y.transition A a y ha hy).hom.toHom.toCoordinateMap.comp
      (f.hom.val.hom A a ha).toHom.toCoordinateMap).comp
        (X.transition A x (q.source b) hx (q.source_unit A b hb)).hom.toHom.toCoordinateMap = _
  rw [ht, CoordinateMap.comp_assoc, hc]

set_option backward.isDefEq.respectTransparency false in
/-- Actual coefficient extension retains the specified inducing formal atlas isomorphism. -/
theorem InducedBy.baseChange {c : Comparison E E'} {f : Iso E E' h}
    (hc : c.InducedBy f) (S : CommAlgCat.{v} R) :
    (c.baseChange S).InducedBy (f.baseChange S) := by
  intro C b hb x y hx hy
  let a := c.right.atlas.baseSource S b
  have ha : IsUnit (algebraMap R (restrictTest S C) a.val) :=
    c.right.atlas.baseSource_unit S C b hb
  have ht := congrArg (fun z => z.hom.val.toHom.toCoordinateMap)
    (hc (restrictTest S C) a ha (X.baseSource S x) (Y.baseSource S y)
      (X.baseSource_unit S C x hx) (Y.baseSource_unit S C y hy))
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change ((c.baseChange S).testIso C b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    ((f.hom.val.baseChange S).hom C y hy).toHom.toCoordinateMap.comp
      ((X.baseChange S).transition C x (sourceChart (baseOpens_eq S h) y) hx hy).hom.toHom.toCoordinateMap
  rw [c.testIso_baseChange_hom_coordinates S C b hb a ha,
    BasicAtlas.Hom.baseChange_coordinates]
  change ((c.testIso (restrictTest S C) a ha (X.baseSource S x) (Y.baseSource S y)
    (X.baseSource_unit S C x hx) (Y.baseSource_unit S C y hy)).hom.val.toHom.toCoordinateMap) =
      (f.hom.val.hom (restrictTest S C) (Y.baseSource S y)
        (Y.baseSource_unit S C y hy)).toHom.toCoordinateMap.comp
          (X.baseTransition S C x (sourceChart (baseOpens_eq S h) y) hx hy).hom.toHom.toCoordinateMap
  rw [X.baseTransition_coordinates]
  have he := X.testTransition_coordinates_eq (restrictTest S C)
    (X.baseSource S x) (sourceChart h (Y.baseSource S y))
    (X.baseSource S x) (X.baseSource S (sourceChart (baseOpens_eq S h) y))
    (X.baseSource_unit S C x hx) (Y.baseSource_unit S C y hy)
    (X.baseSource_unit S C x hx)
    (X.baseSource_unit S C (sourceChart (baseOpens_eq S h) y) hy)
    rfl (baseSource_sourceChart S h y).symm
  exact ht.trans (congrArg (fun z =>
    (f.hom.val.hom (restrictTest S C) (Y.baseSource S y)
      (Y.baseSource_unit S C y hy)).toHom.toCoordinateMap.comp z) he)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison
