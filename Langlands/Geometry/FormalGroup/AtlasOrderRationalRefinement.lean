import Langlands.Geometry.FormalGroup.AtlasRationalRefinement
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism
import Langlands.Geometry.FormalGroup.AtlasOrderRefinementMorphism

/-! # Refinement of rational formal atlas maps commuting with the full order -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace RationalHom

/-- Actual coefficient-chart conjugation preserves full-order commutation. -/
theorem restrict_mem (f : RationalHom F E E' h) (q : CoverRefinement X) :
    BasicAtlas.RationalHom.restrict (Y := Y) (h := h) q f.val ∈
      rationalHomSubmodule F (q.orderAction E) ((q.retarget Y h).orderAction E')
        (q.opens_eq_retarget (Y := Y) (h := h)) := by
  intro A b hb a
  change q.opens at b
  have hc := ((ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
    ((q.retarget Y h).orderChartIso E' A b hb).inv).comp
      ((f.onChart A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).comp
        (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
          (q.orderChartIso E A b hb).hom))).commutes a
  have he := BasicAtlas.RationalHom.onChart_restrict f.val q A b hb
  exact (congrArg (fun t => ModuleLaw.RationalHom.comp t
    (ModuleLaw.RationalHom.ofHom
      ((((q.orderAction E).chart
        (sourceChart (q.opens_eq_retarget (Y := Y) (h := h)) b)).map
          (coefficientLift (O := O) b.val A hb)).action a))) he).trans
    (hc.trans (congrArg (fun t => ModuleLaw.RationalHom.comp
      (ModuleLaw.RationalHom.ofHom
        (((((q.retarget Y h).orderAction E').chart b).map
          (coefficientLift (O := O) b.val A hb)).action a)) t) he.symm))

/-- Restrict the ambient global tensor map, retaining full-order chart commutation. -/
def restrict (q : CoverRefinement X) :
    RationalHom F E E' h →ₗ[F]
      RationalHom F (q.orderAction E) ((q.retarget Y h).orderAction E')
        (q.opens_eq_retarget (Y := Y) (h := h)) where
  toFun f := ⟨BasicAtlas.RationalHom.restrict (Y := Y) (h := h) q f.val, restrict_mem f q⟩
  map_add' f g := by
    apply ext
    exact (BasicAtlas.RationalHom.restrict (F := F) (Y := Y) (h := h) q).map_add f.val g.val
  map_smul' c f := by
    apply ext
    exact (BasicAtlas.RationalHom.restrict (F := F) (Y := Y) (h := h) q).map_smul c f.val

@[simp]
theorem restrict_val (q : CoverRefinement X) (f : RationalHom F E E' h) :
    (restrict (E' := E') (h := h) q f).val =
      BasicAtlas.RationalHom.restrict (Y := Y) (h := h) q f.val := rfl

/-- Restriction agrees with rationalization of actual integral order-linear maps. -/
@[simp]
theorem restrict_ofHom (q : CoverRefinement X) (f : Hom E E' h) :
    restrict (E' := E') (h := h) q (ofHom (F := F) f) =
      ofHom (F := F) (E := q.orderAction E)
        (E' := (q.retarget Y h).orderAction E')
        (h := q.opens_eq_retarget (Y := Y) (h := h)) (f.restrict q) := by
  apply ext
  exact BasicAtlas.RationalHom.restrict_ofHom q f.val

/-- The actual rational formal identity restricts to the identity. -/
@[simp]
theorem restrict_id (E : OrderAction D X) (q : CoverRefinement X) :
    restrict (E' := E) (h := rfl) q (id (F := F) E) = id (q.orderAction E) := by
  apply ext
  exact BasicAtlas.RationalHom.restrict_id q

/-- Restriction preserves composition with the same intermediate retargeted cover. -/
@[simp]
theorem restrict_comp (g : RationalHom F E' E'' k) (f : RationalHom F E E' h)
    (q : CoverRefinement X) :
    restrict (E' := E'') (h := h.trans k) q (g.comp f) =
      (restrict (E' := E'') (h := k) (q.retarget Y h) g).comp
        (restrict (E' := E') (h := h) q f) := by
  apply ext
  exact BasicAtlas.RationalHom.restrict_comp g.val f.val q

/-- Restriction respects the composition ring of full-order rational endomorphisms. -/
def restrictRingHom (E : OrderAction D X) (q : CoverRefinement X) :
    RationalHom F E E rfl →+* RationalHom F (q.orderAction E) (q.orderAction E) rfl where
  toFun := restrict (E' := E) (h := rfl) q
  map_zero' := (restrict (E' := E) (h := rfl) q).map_zero
  map_add' := (restrict (E' := E) (h := rfl) q).map_add
  map_one' := restrict_id E q
  map_mul' := fun g f => restrict_comp g f q

/-- The chart equation holds inside the actual full-order coordinate centralizer. -/
theorem onChart_restrict (f : RationalHom F E E' h) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (restrict (E' := E') (h := h) q f).onChart A b hb =
      (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
        ((q.retarget Y h).orderChartIso E' A b hb).inv).comp
          ((f.onChart A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).comp
            (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
              (q.orderChartIso E A b hb).hom)) := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact BasicAtlas.RationalHom.onChart_restrict f.val q A b hb

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Restrict both full-order rational maps and retain the two actual inverse laws. -/
def restrict (f : QuasiIsogeny F E E' h) (q : CoverRefinement X) :
    QuasiIsogeny F (q.orderAction E) ((q.retarget Y h).orderAction E')
      (q.opens_eq_retarget (Y := Y) (h := h)) where
  hom := RationalHom.restrict (E' := E') (h := h) q f.hom
  inv := RationalHom.restrict (E' := E) (h := h.symm) (q.retarget Y h) f.inv
  inv_hom := by
    apply RationalHom.ext
    exact (f.toAtlasQuasiIsogeny.restrict q).inv_hom
  hom_inv := by
    apply RationalHom.ext
    exact (f.toAtlasQuasiIsogeny.restrict q).hom_inv

@[simp]
theorem restrict_hom (f : QuasiIsogeny F E E' h) (q : CoverRefinement X) :
    (f.restrict q).hom = RationalHom.restrict (E' := E') (h := h) q f.hom := rfl

@[simp]
theorem restrict_inv (f : QuasiIsogeny F E E' h) (q : CoverRefinement X) :
    (f.restrict q).inv =
      RationalHom.restrict (E' := E) (h := h.symm) (q.retarget Y h) f.inv := rfl

/-- Forgetting the full order gives exactly the existing ambient restriction. -/
@[simp]
theorem toAtlas_restrict (f : QuasiIsogeny F E E' h) (q : CoverRefinement X) :
    (f.restrict q).toAtlasQuasiIsogeny = f.toAtlasQuasiIsogeny.restrict q := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  rfl

@[simp]
theorem restrict_refl (E : OrderAction D X) (q : CoverRefinement X) :
    (refl (F := F) E).restrict q = refl (q.orderAction E) := by
  apply ext_hom
  exact RationalHom.restrict_id E q

@[simp]
theorem restrict_symm (f : QuasiIsogeny F E E' h) (q : CoverRefinement X) :
    f.symm.restrict (q.retarget Y h) = (f.restrict q).symm := by
  apply ext_hom
  rfl

@[simp]
theorem restrict_trans (f : QuasiIsogeny F E E' h) (g : QuasiIsogeny F E' E'' k)
    (q : CoverRefinement X) :
    (f.trans g).restrict q =
      (f.restrict q).trans (g.restrict (q.retarget Y h)) := by
  apply ext_hom
  exact RationalHom.restrict_comp g.hom f.hom q

@[simp]
theorem restrict_ofIso (f : Iso E E' h) (q : CoverRefinement X) :
    (ofIso (F := F) f).restrict q = ofIso (f.restrict q) := by
  apply ext_hom
  exact RationalHom.restrict_ofHom q f.hom

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
