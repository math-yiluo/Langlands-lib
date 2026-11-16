import Langlands.Geometry.FormalGroup.AtlasOrderRefinementCoherence
import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus

/-! # Actual rational coherence of direct and successive formal refinement -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw

namespace OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : OrderAction D M} {E' : OrderAction D N} {E'' : OrderAction D P}

/-- An actual factorization determines this composite with the inverse total map. -/
theorem symm_trans_of_trans_eq (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E' E'')
    (h : QuasiIsogeny F E E'') (e : f.trans g = h) : h.symm.trans f = g.symm := by
  calc
    h.symm.trans f = (f.trans g).symm.trans f :=
      congrArg (fun k => k.symm.trans f) e.symm
    _ = (g.symm.trans f.symm).trans f := rfl
    _ = g.symm.trans (f.symm.trans f) := trans_assoc _ _ _
    _ = g.symm := by rw [symm_trans_self, trans_refl]

end OrderAction.QuasiIsogeny

namespace BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Evaluate the specified direct-to-successive actual order-linear formal comparison. -/
def orderCompQuasi (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (r : CoverRefinement q.atlas) (B : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny F
      (((q.comp r).orderChart E b).map (coefficientLift (O := O) b.val B hb))
      ((r.orderChart (q.orderAction E) b).map (coefficientLift (O := O) b.val B hb)) :=
  (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F) (q.orderCompIso E r)).onChart B b hb

/-- The specified comparison followed by successive chart identifications equals the direct one. -/
theorem orderCompQuasi_chart (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (r : CoverRefinement q.atlas) (B : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    ((q.orderCompQuasi (F := F) E r B b hb).trans
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        (r.orderChartIso (q.orderAction E) B b hb))).trans
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        (q.orderChartIso E B (r.source b) (r.source_unit B b hb))) =
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso ((q.comp r).orderChartIso E B b hb) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  apply ModuleLaw.OrderAction.RationalHom.ext
  let cc := (q.compIso r).hom.hom B b hb
  let rr := (r.chartIso B b hb).hom
  let qq := (q.chartIso B (r.source b) (r.source_unit B b hb)).hom
  let dd := ((q.comp r).chartIso B b hb).hom
  have hi : qq.comp (rr.comp cc) = dd := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      (CoordinateMap.id.comp ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id)) =
        CoordinateMap.id
    simp only [CoordinateMap.id_comp]
  have h₁ := ModuleLaw.RationalHom.ofHom_comp (F := F) rr cc
  have h₂ := ModuleLaw.RationalHom.ofHom_comp (F := F) qq (rr.comp cc)
  exact (congrArg (fun k => ModuleLaw.RationalHom.comp
    (ModuleLaw.RationalHom.ofHom (F := F) qq) k) h₁.symm).trans
      (h₂.symm.trans (congrArg (ModuleLaw.RationalHom.ofHom (F := F)) hi))

end BasicAtlas.CoverRefinement

end Langlands.FormalGroup.ModuleLaw
