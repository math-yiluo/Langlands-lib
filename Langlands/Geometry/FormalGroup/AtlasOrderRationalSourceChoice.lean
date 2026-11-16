import Langlands.Geometry.FormalGroup.AtlasOrderRefinementCoherence
import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus

/-! # Actual rational comparison of different source-chart selections -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw

namespace OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
  {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {E : OrderAction D M} {E' : OrderAction D N}
  {E'' : OrderAction D P} {E''' : OrderAction D Q}

/-- Cancel the actual inverse pair in two pasted rational routes. -/
theorem trans_symm_trans (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E'' E')
    (h : QuasiIsogeny F E' E''') :
    (f.trans g.symm).trans (g.trans h) = f.trans h := by
  calc
    (f.trans g.symm).trans (g.trans h) =
        ((f.trans g.symm).trans g).trans h := (trans_assoc _ _ _).symm
    _ = (f.trans (g.symm.trans g)).trans h :=
      congrArg (fun k => k.trans h) (trans_assoc f g.symm g)
    _ = f.trans h := by rw [symm_trans_self, trans_refl]

end OrderAction.QuasiIsogeny

namespace BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Compare actual refined charts through their selected original transition. -/
def orderSourceQuasi (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (r : CoverRefinement X) (h : q.opens = r.opens)
    (B : CommAlgCat.{v} R) (b : r.opens) (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny F
      ((q.orderChart E (sourceChart (X := q.atlas) (Y := r.atlas) h b)).map
        (coefficientLift (O := O) b.val B hb))
      ((r.orderChart E b).map (coefficientLift (O := O) b.val B hb)) :=
  (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    (q.orderChartIso E B (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        (E.transitionIso B
          (q.source (sourceChart (X := q.atlas) (Y := r.atlas) h b)) (r.source b)
          (q.source_unit B (sourceChart (X := q.atlas) (Y := r.atlas) h b) hb)
          (r.source_unit B b hb))).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (r.orderChartIso E B b hb)).symm)

/-- This route is precisely evaluation of the specified actual source-choice atlas isomorphism. -/
theorem orderSourceQuasi_eq_onChart (q : CoverRefinement X) (E : BasicAtlas.OrderAction D X)
    (r : CoverRefinement X) (h : q.opens = r.opens)
    (B : CommAlgCat.{v} R) (b : r.opens) (hb : IsUnit (algebraMap R B b.val)) :
    q.orderSourceQuasi (F := F) E r h B b hb =
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
        (q.orderSourceIso E r h)).onChart B b hb := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  apply ModuleLaw.OrderAction.RationalHom.ext
  let a := sourceChart (X := q.atlas) (Y := r.atlas) h b
  let tq := (q.chartIso B a hb).hom
  let tr := (r.chartIso B b hb).inv
  let tt := (X.transition B (q.source a) (r.source b)
    (q.source_unit B a hb) (r.source_unit B b hb)).hom
  have h₁ := ModuleLaw.RationalHom.ofHom_comp (F := F) tr tt
  have h₂ := ModuleLaw.RationalHom.ofHom_comp (F := F) (tr.comp tt) tq
  exact (congrArg (fun k => ModuleLaw.RationalHom.comp k
    (ModuleLaw.RationalHom.ofHom (F := F) tq)) h₁.symm).trans h₂.symm

end BasicAtlas.CoverRefinement

end Langlands.FormalGroup.ModuleLaw
