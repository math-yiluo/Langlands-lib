import Langlands.GroupScheme.OuterIsomorphismActualNormalization

/-! # Representation-free normalization and adjoint orbit coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GroupIsomorphismScheme.ActualNormalization

variable {S : Scheme.{u}} {G H A : GroupScheme S}
    (n : ActualNormalization (G := G) (H := H))

/-- Normalize an all-test local family by normalizing its actual pullback isomorphism.
This definition needs no scheme representing isomorphisms. -/
def localNormalize (T : Over S) (e : LocalGroupIso G H T) : LocalGroupIso G H T :=
  LocalGroupIso.ofBaseChangeIso (n.normalize T e.toBaseChangeIso)

@[simp] theorem localNormalize_toBaseChangeIso (T : Over S) (e : LocalGroupIso G H T) :
    (n.localNormalize T e).toBaseChangeIso = n.normalize T e.toBaseChangeIso :=
  LocalGroupIso.toBaseChangeIso_ofBaseChangeIso _

/-- Actual normalization is natural on all relative family refinements. -/
theorem localNormalize_refine {T W : Over S} (t : W ⟶ T) (e : LocalGroupIso G H T) :
    n.localNormalize W (e.refine t) = (n.localNormalize T e).refine t := by
  unfold localNormalize
  rw [LocalGroupIso.toBaseChangeIso_refine, n.naturality,
    LocalGroupIso.ofBaseChangeIso_refine]

/-- Inner-class normalization fixes every family already in its image. -/
theorem localNormalize_idempotent (T : Over S) (e : LocalGroupIso G H T) :
    n.localNormalize T (n.localNormalize T e) = n.localNormalize T e := by
  unfold localNormalize
  rw [LocalGroupIso.toBaseChangeIso_ofBaseChangeIso]
  exact congrArg LocalGroupIso.ofBaseChangeIso
    (n.invariant T e.toBaseChangeIso (n.normalize T e.toBaseChangeIso)
      (n.inner T e.toBaseChangeIso)).symm

variable {q : G ⟶ A} (hq : IsRelativeAdjointQuotient q)

/-- Inverse precomposition by an adjoint point leaves the normalized family fixed. -/
theorem localNormalize_invariant (T : Over S) (d : T ⟶ A.X)
    (e : LocalGroupIso G H T) :
    n.localNormalize T (e.twist hq.innerAction d⁻¹) = n.localNormalize T e := by
  unfold localNormalize
  apply congrArg LocalGroupIso.ofBaseChangeIso
  apply n.invariant T
  rw [LocalGroupIso.toBaseChangeIso_twist, hq.innerAction_baseChange]
  change IsFppfLocallyInner (_ ≪≫ e.toBaseChangeIso ≪≫ e.toBaseChangeIso.symm)
  simp only [Iso.self_symm_id, Iso.trans_refl]
  exact IsFppfLocallyInner.of_adjointPoint _
    (hq.baseChange T.hom).isQuotient _ (hq.baseChange T.hom).innerAction_restrict _ rfl

/-- The unique adjoint correction lies on the original relative test scheme. -/
theorem localNormalize_decomposition (T : Over S) (e : LocalGroupIso G H T) :
    ∃! d : T ⟶ A.X, (n.localNormalize T e).twist hq.innerAction d⁻¹ = e := by
  let E := e.toBaseChangeIso
  let N := n.normalize T E
  let aT := (hq.baseChange T.hom).innerAction
  obtain ⟨x, hx, huniq⟩ := (n.inner T E).existsUnique_adjointPoint _
    (hq.baseChange T.hom).isQuotient aT (hq.baseChange T.hom).innerAction_restrict
  let d : T ⟶ A.X := (baseChangeBasePointsEquiv T.hom A x)⁻¹
  have he (z : T ⟶ A.X) :
      ((n.localNormalize T e).twist hq.innerAction z⁻¹ = e) ↔
        aT.basePointIso ((baseChangeBasePointsEquiv T.hom A).symm z⁻¹) =
          E ≪≫ N.symm := by
    rw [← LocalGroupIso.baseChangeIsoEquiv.symm.injective.eq_iff]
    change ((n.localNormalize T e).twist hq.innerAction z⁻¹).toBaseChangeIso =
      e.toBaseChangeIso ↔ _
    rw [LocalGroupIso.toBaseChangeIso_twist, localNormalize_toBaseChangeIso,
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
    simpa only [MulEquiv.apply_symm_apply, inv_inv, d] using congrArg Inv.inv h

/-- A uniquely classifying normalized family gives adjoint orbit coordinates on
all relative tests, before introducing an isomorphism representer. -/
theorem localOrbit_bijective {U : Over S} (E : LocalGroupIso G H U)
    (hfixed : ∀ (T : Over S) (b : T ⟶ U),
      n.localNormalize T (E.refine b) = E.refine b)
    (hclass : ∀ (T : Over S) (e : LocalGroupIso G H T),
      ∃! b : T ⟶ U, E.refine b = n.localNormalize T e)
    (T : Over S) : Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ U) => (E.refine z.2).twist hq.innerAction z.1⁻¹) := by
  constructor
  · intro z w h
    have hE : E.refine z.2 = E.refine w.2 := by
      have hn := congrArg (n.localNormalize T) h
      simpa only [n.localNormalize_invariant hq, hfixed] using hn
    have hb : z.2 = w.2 := by
      apply (hclass T (E.refine z.2)).unique
      · exact (hfixed T z.2).symm
      · exact hE.symm.trans (hfixed T z.2).symm
    let e := (E.refine z.2).twist hq.innerAction z.1⁻¹
    have hn : n.localNormalize T e = E.refine z.2 :=
      (n.localNormalize_invariant hq T z.1 (E.refine z.2)).trans (hfixed T z.2)
    have hd : z.1 = w.1 := by
      apply (n.localNormalize_decomposition hq T e).unique
      · rw [hn]
      · rw [hn, hE]
        exact h.symm
    exact Prod.ext hd hb
  · intro e
    obtain ⟨b, hb, _⟩ := hclass T e
    obtain ⟨d, hd, _⟩ := n.localNormalize_decomposition hq T e
    refine ⟨(d, b), ?_⟩
    change (E.refine b).twist hq.innerAction d⁻¹ = e
    rw [hb]
    exact hd

end Langlands.GroupScheme.GroupIsomorphismScheme.ActualNormalization

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
    (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)

/-- Classifying a representation-free family in any supplied representative
preserves its all-test orbit bijection. -/
theorem orbit_bijective_of_local {U : Over S} (E : LocalGroupIso G H U)
    (hE : ∀ (T : Over S), Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ U) => (E.refine z.2).twist a z.1⁻¹))
    (T : Over S) : Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ U) =>
        lift z.1 (z.2 ≫ I.classify E) ≫ I.actionHom a) := by
  have heval (z : (T ⟶ A.X) × (T ⟶ U)) :
      I.universalIso.refine (lift z.1 (z.2 ≫ I.classify E) ≫ I.actionHom a) =
        (E.refine z.2).twist a z.1⁻¹ := by
    apply LocalGroupIso.ext_toFun
    intro W t g
    change I.universalIso.toFun
      (t ≫ (lift z.1 (z.2 ≫ I.classify E) ≫ I.actionHom a)) g =
      E.toFun (t ≫ z.2) (a.act (t ≫ z.1⁻¹) g)
    rw [← Category.assoc, comp_lift, I.actionHom_eval, GrpObj.comp_inv]
    have hc := congrArg (fun F : LocalGroupIso G H U =>
      F.toFun (t ≫ z.2) (a.act (t ≫ z.1)⁻¹ g)) (I.refine_classify E)
    simpa only [LocalGroupIso.refine_toFun, Category.assoc] using hc
  apply Function.Bijective.of_comp_left
    (f := fun p : T ⟶ I.parameter => I.universalIso.refine p)
  · simpa only [Function.comp_def, heval] using hE T
  · exact (I.bijective T).1

end Langlands.GroupScheme.GroupIsomorphismScheme
