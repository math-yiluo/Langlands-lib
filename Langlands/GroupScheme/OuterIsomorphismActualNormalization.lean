import Langlands.GroupScheme.OuterIsomorphismNormalization
import Langlands.GroupScheme.LocalGroupIsoBaseChangeNaturality
import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.AutomorphicAction.LocallyInnerTransport

/-! # Actual-isomorphism normalization and outer quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H)

/-- The actual isomorphism classified by a point of the supplied representer. -/
def isoOfPoint {T : Over S} (p : T ⟶ I.parameter) :
    (baseChange T.hom).obj G ≅ (baseChange T.hom).obj H :=
  (I.baseChangeIsoEquiv T).symm p

/-- The actual isomorphism is recovered from the universal local family. -/
theorem isoOfPoint_eq {T : Over S} (p : T ⟶ I.parameter) :
    I.isoOfPoint p = (I.universalIso.refine p).toBaseChangeIso := rfl

/-- Classification respects every refinement with its specified base-map equality. -/
theorem isoOfPoint_comp {T W : Over S} (t : W ⟶ T) (p : T ⟶ I.parameter) :
    I.isoOfPoint (t ≫ p) =
      Descent.pullIso t.left (Over.w t) (Over.w t) (I.isoOfPoint p) := by
  rw [isoOfPoint_eq, isoOfPoint_eq]
  have h : I.universalIso.refine (t ≫ p) = (I.universalIso.refine p).refine t := by
    apply LocalGroupIso.ext_toFun
    intro V b g
    simp only [LocalGroupIso.refine_toFun, Category.assoc]
  rw [h, LocalGroupIso.toBaseChangeIso_refine]

variable (a : AutomorphicAction A G)

/-- The action on the representing scheme is actual inverse precomposition. -/
theorem isoOfPoint_action {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter) :
    I.isoOfPoint (lift d p ≫ I.actionHom a) =
      (a.baseChange T.hom).basePointIso
        ((baseChangeBasePointsEquiv T.hom A).symm d⁻¹) ≪≫ I.isoOfPoint p := by
  rw [isoOfPoint_eq, isoOfPoint_eq]
  have h : I.universalIso.refine (lift d p ≫ I.actionHom a) =
      (I.universalIso.refine p).twist a d⁻¹ := by
    apply LocalGroupIso.ext_toFun
    intro W t g
    change I.universalIso.toFun (t ≫ (lift d p ≫ I.actionHom a)) g =
      I.universalIso.toFun (t ≫ p) (a.act (t ≫ d⁻¹) g)
    rw [← Category.assoc, comp_lift, I.actionHom_eval, GrpObj.comp_inv]
  rw [h, LocalGroupIso.toBaseChangeIso_twist]

/-- A normalization of actual isomorphisms, natural under every refinement,
depending only on the fppf-local inner class and preserving that class. -/
structure ActualNormalization where
  normalize : ∀ (T : Over S),
    ((baseChange T.hom).obj G ≅ (baseChange T.hom).obj H) →
      ((baseChange T.hom).obj G ≅ (baseChange T.hom).obj H)
  naturality : ∀ {T W : Over S} (t : W ⟶ T)
    (e : (baseChange T.hom).obj G ≅ (baseChange T.hom).obj H),
    normalize W (Descent.pullIso t.left (Over.w t) (Over.w t) e) =
      Descent.pullIso t.left (Over.w t) (Over.w t) (normalize T e)
  invariant : ∀ (T : Over S)
    (e d : (baseChange T.hom).obj G ≅ (baseChange T.hom).obj H),
    IsFppfInnerEquivalent e d → normalize T e = normalize T d
  inner : ∀ (T : Over S)
    (e : (baseChange T.hom).obj G ≅ (baseChange T.hom).obj H),
    IsFppfInnerEquivalent e (normalize T e)

namespace ActualNormalization

variable {I a} (n : ActualNormalization (G := G) (H := H))
  {q : G ⟶ A} (hq : IsRelativeAdjointQuotient q)

/-- Normalize a represented point by normalizing its actual isomorphism. -/
def normalizePoint {T : Over S} (p : T ⟶ I.parameter) : T ⟶ I.parameter :=
  I.baseChangeIsoEquiv T (n.normalize T (I.isoOfPoint p))

theorem isoOfPoint_normalizePoint {T : Over S} (p : T ⟶ I.parameter) :
    I.isoOfPoint (n.normalizePoint p) = n.normalize T (I.isoOfPoint p) :=
  (I.baseChangeIsoEquiv T).symm_apply_apply _

theorem normalizePoint_naturality {T W : Over S} (t : W ⟶ T)
    (p : T ⟶ I.parameter) :
    n.normalizePoint (t ≫ p) = t ≫ n.normalizePoint p := by
  apply (I.baseChangeIsoEquiv W).symm.injective
  change I.isoOfPoint (n.normalizePoint (t ≫ p)) =
    I.isoOfPoint (t ≫ n.normalizePoint p)
  rw [n.isoOfPoint_normalizePoint, I.isoOfPoint_comp, n.naturality,
    I.isoOfPoint_comp, n.isoOfPoint_normalizePoint]

/-- Actual inverse precomposition does not change the normalization. -/
theorem normalizePoint_invariant {T : Over S} (d : T ⟶ A.X)
    (p : T ⟶ I.parameter) :
    n.normalizePoint (lift d p ≫ I.actionHom hq.innerAction) =
      n.normalizePoint p := by
  apply (I.baseChangeIsoEquiv T).symm.injective
  change I.isoOfPoint (n.normalizePoint _) = I.isoOfPoint (n.normalizePoint p)
  rw [n.isoOfPoint_normalizePoint, n.isoOfPoint_normalizePoint]
  apply n.invariant T
  rw [I.isoOfPoint_action, hq.innerAction_baseChange]
  change IsFppfLocallyInner (_ ≪≫ I.isoOfPoint p ≪≫ (I.isoOfPoint p).symm)
  simp only [Iso.self_symm_id, Iso.trans_refl]
  exact IsFppfLocallyInner.of_adjointPoint _
    (hq.baseChange T.hom).isQuotient _ (hq.baseChange T.hom).innerAction_restrict _ rfl

/-- The full-centre quotient supplies a unique acting point on the same test. -/
theorem normalizePoint_decomposition {T : Over S} (p : T ⟶ I.parameter) :
    ∃! d : T ⟶ A.X,
      lift d (n.normalizePoint p) ≫ I.actionHom hq.innerAction = p := by
  let E := I.isoOfPoint p
  let N := n.normalize T E
  let aT := (hq.baseChange T.hom).innerAction
  obtain ⟨x, hx, huniq⟩ := (n.inner T E).existsUnique_adjointPoint _
    (hq.baseChange T.hom).isQuotient aT (hq.baseChange T.hom).innerAction_restrict
  let d : T ⟶ A.X := (baseChangeBasePointsEquiv T.hom A x)⁻¹
  have he (z : T ⟶ A.X) :
      (lift z (n.normalizePoint p) ≫ I.actionHom hq.innerAction = p) ↔
        aT.basePointIso ((baseChangeBasePointsEquiv T.hom A).symm z⁻¹) =
          E ≪≫ N.symm := by
    rw [← (I.baseChangeIsoEquiv T).symm.injective.eq_iff]
    change I.isoOfPoint (lift z (n.normalizePoint p) ≫ I.actionHom hq.innerAction) =
      I.isoOfPoint p ↔ _
    rw [I.isoOfPoint_action, n.isoOfPoint_normalizePoint,
      hq.innerAction_baseChange]
    change aT.basePointIso _ ≪≫ N = E ↔ _
    constructor
    · intro h
      simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using
        congrArg (fun k => k ≪≫ N.symm) h
    · intro h
      simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using
        congrArg (fun k => k ≪≫ N) h
  refine ⟨d, (he d).mpr ?_, ?_⟩
  · simpa only [d, inv_inv, MulEquiv.symm_apply_apply] using hx
  · intro z hz
    have hz' := huniq _ ((he z).mp hz)
    have h := congrArg (baseChangeBasePointsEquiv T.hom A) hz'
    simpa only [MulEquiv.apply_symm_apply, inv_inv, d] using
      congrArg Inv.inv h

/-- Full-centre inner action turns actual natural normalization into the
point normalization required by the equalizer construction. -/
def pointNormalization : I.PointNormalization hq.innerAction where
  normalize := n.normalizePoint
  naturality := n.normalizePoint_naturality
  invariant := n.normalizePoint_invariant hq
  decomposition := n.normalizePoint_decomposition hq

end ActualNormalization

end Langlands.GroupScheme.GroupIsomorphismScheme
