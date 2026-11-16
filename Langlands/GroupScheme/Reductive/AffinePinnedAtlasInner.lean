import Langlands.GroupScheme.Reductive.AffinePinnedTransitionInner
import Langlands.GroupScheme.Reductive.AffinePinnedAtlasTransitions
import Langlands.GroupScheme.Rational.InnerDiscrepancyIso
import Langlands.GroupScheme.Adjoint.CenterQuotientReduction
import Langlands.GroupScheme.AutomorphicAction.BaseChangeCompatibility

/-! # Actual inner points for arbitrary pinned atlas transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U V : Over S}

/-- The lifted point has exactly its original point and parameter as coordinates. -/
theorem coverPointsEquiv_symm_left_eq_lift {T : Over S}
    (a : T ⟶ U) (g : T ⟶ G.X) :
    ((coverPointsEquiv G a).symm g).left =
      pullback.lift g.left a.left ((Over.w g).trans (Over.w a).symm) := by
  apply pullback.hom_ext
  · have h := congrArg (fun x => x.left)
      ((coverPointsEquiv G a).apply_symm_apply g)
    simpa only [coverPointsEquiv_left, pullback.lift_fst] using h
  · exact (Over.w _).trans (pullback.lift_snd _ _ _).symm

/-- Actual direct pullback of an isomorphism refines its natural local family. -/
theorem ofBaseChangeIso_pullIso
    (E : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H) (r : V ⟶ U) :
    ofBaseChangeIso (Descent.pullIso r.left (Over.w r) (Over.w r) E) =
      (ofBaseChangeIso E).refine r := by
  apply ext_toFun
  intro T a g
  apply Over.OverMorphism.ext
  change ((ofBaseChangeIso (Descent.pullIso r.left (Over.w r) (Over.w r) E)).toFun a g).left =
    ((ofBaseChangeIso E).toFun (a ≫ r) g).left
  rw [ofBaseChangeIso_toFun_left, ofBaseChangeIso_toFun_left,
    coverPointsEquiv_symm_left_eq_lift, coverPointsEquiv_symm_left_eq_lift]
  exact Descent.pullHom_eval r.left (Over.w r) (Over.w r) E.hom
    g.left a.left ((Over.w g).trans (Over.w a).symm)

end LocalGroupIso

namespace AutomorphicAction

variable {S : Scheme.{u}} {Q G : GroupScheme S} (a : AutomorphicAction Q G)

/-- Evaluation of a relative point commutes with arbitrary direct pullback. -/
theorem relativePointIso_pull {T W : Over S} (x : T ⟶ Q.X) (r : W ⟶ T) :
    Descent.pullIso r.left (Over.w r) (Over.w r) (a.relativePointIso x) =
      a.relativePointIso (r ≫ x) := by
  apply (LocalGroupIso.baseChangeIsoEquiv (G := G) (H := G) (U := W)).injective
  change LocalGroupIso.ofBaseChangeIso _ = LocalGroupIso.ofBaseChangeIso _
  rw [LocalGroupIso.ofBaseChangeIso_pullIso]
  apply LocalGroupIso.ext_toFun
  intro V t g
  simp only [LocalGroupIso.refine_toFun, relativePointIso_toFun, Category.assoc]

end AutomorphicAction

namespace Descent.DisjointComponents

variable {S T : Scheme.{u}} {I : Type u} {Z : I → Scheme.{u}}
    (q : ∀ i, Z i ⟶ T) [hq : IsIso (Sigma.desc q)]
    (k : T ⟶ S) {Q G : GroupScheme S}

include hq

/-- Assemble actual relative points over an arbitrary disjoint decomposition. -/
def relativePoint (x : ∀ i, Over.mk (q i ≫ k) ⟶ Q.X) : Over.mk k ⟶ Q.X := by
  let d : (∐ Z) ⟶ T := Sigma.desc q
  haveI : IsIso d := hq
  refine Over.homMk (inv d ≫ Sigma.desc (fun i => (x i).left)) ?_
  apply (cancel_epi d).mp
  apply Sigma.hom_ext
  intro i
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, d, Sigma.ι_comp_desc_assoc]
  exact Over.w (x i)

/-- The assembled relative point recovers each component point exactly. -/
theorem relativePoint_fac (x : ∀ i, Over.mk (q i ≫ k) ⟶ Q.X) (i : I) :
    Over.homMk (q i) rfl ≫ relativePoint q k x = x i := by
  apply Over.OverMorphism.ext
  change q i ≫ inv (Sigma.desc q) ≫ Sigma.desc (fun j => (x j).left) = (x i).left
  calc
    _ = Sigma.ι Z i ≫ Sigma.desc q ≫ inv (Sigma.desc q) ≫
        Sigma.desc (fun j => (x j).left) := by rw [Sigma.ι_comp_desc_assoc]
    _ = _ := by simp

/-- Actual inner points glue across disjoint components without a uniqueness premise. -/
theorem exists_relativePointIso (a : AutomorphicAction Q G)
    (E : (baseChange k).obj G ≅ (baseChange k).obj G)
    (h : ∀ i, ∃ x : Over.mk (q i ≫ k) ⟶ Q.X,
      pullIso (q i) rfl rfl E = a.relativePointIso x) :
    ∃ x : Over.mk k ⟶ Q.X, E = a.relativePointIso x := by
  choose x hx using h
  refine ⟨relativePoint q k x, ?_⟩
  apply pullIso_ext_along q (fun _ => rfl) (fun _ => rfl)
  intro i
  rw [hx i]
  symm
  have hr := a.relativePointIso_pull (relativePoint q k x)
    (Over.homMk (q i) rfl : Over.mk (q i ≫ k) ⟶ Over.mk k)
  simpa only [Over.homMk_left, relativePoint_fac] using hr

end Descent.DisjointComponents

end Langlands.GroupScheme
