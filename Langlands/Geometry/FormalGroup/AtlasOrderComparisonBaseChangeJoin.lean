import Langlands.Geometry.FormalGroup.AtlasOrderComparisonInverse

/-! # Source changes and joins through coefficient extension -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- Extending the actual source-change maps commutes with refinement correction. -/
theorem CoverRefinement.orderSourceIso_baseChange
    (q r : CoverRefinement X) (E : OrderAction D X)
    (h : q.opens = r.opens) (S : CommAlgCat.{v} R) :
    (q.orderBaseChangeIso E S).trans
        ((q.baseChange S).orderSourceIso (E.baseChange S) (r.baseChange S)
          (baseOpens_eq S h)) =
      ((q.orderSourceIso E r h).baseChange S).trans (r.orderBaseChangeIso E S) := by
  apply OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  dsimp only [OrderAction.Iso.trans, OrderAction.Hom.comp, BasicAtlas.Hom.comp,
    ModuleLaw.Hom.comp, CommLaw.Hom.comp,
    CoverRefinement.orderSourceIso, CoverRefinement.orderSourceHom, CoverRefinement.sourceHom,
    CoverRefinement.orderBaseChangeIso, CoverRefinement.orderBaseChangeHom,
    CoverRefinement.baseChangeHom, OrderAction.Iso.baseChange, OrderAction.Hom.baseChange]
  simp only [CoverRefinement.sourceChartIso_coordinates,
    CoverRefinement.baseChangeChartIso_coordinates, BasicAtlas.Hom.baseChange_coordinates]
  dsimp only [BasicAtlas.baseChange, CoverRefinement.baseChange, CoverRefinement.atlas]
  simp only [BasicAtlas.baseTransition_coordinates]
  let A := BasicAtlas.restrictTest S B
  let a := sourceChart (X := q.atlas.baseChange S) (Y := r.atlas.baseChange S)
    (baseOpens_eq S h) b
  let qo := q.baseOriginalSource S a
  let qs := q.baseSelectedSource S a
  let ro := r.baseOriginalSource S b
  let rs := r.baseSelectedSource S b
  have hqo : IsUnit (algebraMap R A qo.val) := q.baseOriginal_unit S B a hb
  have hqs : IsUnit (algebraMap R A qs.val) := q.baseSelected_unit S B a hb
  have hro : IsUnit (algebraMap R A ro.val) := r.baseOriginal_unit S B b hb
  have hrs : IsUnit (algebraMap R A rs.val) := r.baseSelected_unit S B b hb
  let qa := q.source (sourceChart (X := q.atlas) (Y := r.atlas) h
    (r.atlas.baseSource S b))
  have hqa : IsUnit (algebraMap R A qa.val) := q.source_unit A _
    (r.atlas.baseSource_unit S B b hb)
  change (X.transition A qs rs hqs hrs).hom.toHom.toCoordinateMap.comp
      (X.transition A qo qs hqo hqs).hom.toHom.toCoordinateMap =
    (X.transition A ro rs hro hrs).hom.toHom.toCoordinateMap.comp
      (X.transition A qa ro hqa hro).hom.toHom.toCoordinateMap
  have hL := congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A qo qs rs hqo hqs hrs)
  have hR := congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A qa ro rs hqa hro hrs)
  have he : qo = qa := congrArg q.source (baseSource_sourceChart S h b)
  exact hL.trans ((X.testTransition_coordinates_eq A qo rs qa rs hqo hrs hqa hrs he rfl).trans hR.symm)

namespace OrderAction

/-- Coefficient extension preserves composition of whole formal isomorphisms. -/
theorem Iso.baseChange_trans {h : X.opens = Y.opens} {k : Y.opens = Z.opens}
    (f : Iso E E' h) (g : Iso E' E'' k) (S : CommAlgCat.{v} R) :
    (f.trans g).baseChange S = (f.baseChange S).trans (g.baseChange S) := by
  apply Iso.ext_hom
  exact Hom.baseChange_comp g.hom f.hom S

set_option backward.isDefEq.respectTransparency false in
/-- Extending a specified join retains exactly its actual middle source transition. -/
theorem Comparison.baseChange_join (f : Comparison E E') (g : Comparison E' E'')
    (h : f.right.opens = g.left.opens) (S : CommAlgCat.{v} R) :
    (f.join g h).baseChange S =
      (f.baseChange S).join (g.baseChange S) (baseOpens_eq S h) := by
  unfold Comparison.baseChange Comparison.join
  congr 1
  apply Iso.ext_hom
  have hs := congrArg (fun i => i.hom)
    (f.right.orderSourceIso_baseChange g.left E' h S)
  dsimp only [Iso.trans] at hs
  simp only [Iso.baseChange_trans]
  dsimp only [Iso.trans, Iso.symm]
  simp only [Hom.comp_assoc] at hs ⊢
  rw [← Hom.comp_assoc _ (f.right.orderBaseChangeIso E' S).hom, hs]
  simp only [Hom.comp_assoc]
  rw [← Hom.comp_assoc _ (g.left.orderBaseChangeIso E' S).hom,
    (g.left.orderBaseChangeIso E' S).inv_hom, Hom.id_comp]

end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
