import Langlands.GroupScheme.IsomorphismSchemeTransport
import Langlands.GroupScheme.IsomorphismSchemeBaseChange
import Langlands.GroupScheme.OuterIsomorphismScheme
import Langlands.GroupScheme.AutomorphicAction.BaseChange

/-! # Inverse-precomposition actions under target transport and base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S S' : Scheme.{u}} {G H A : GroupScheme S}

/-- Restricting a family to a new base commutes with twisting by an acting point. -/
theorem baseChangeFamily_twist (b : S' ⟶ S) {U : Over S'}
    (e : LocalGroupIso G H ((Over.map b).obj U)) (a : AutomorphicAction A G)
    (d : U ⟶ ((GroupScheme.baseChange b).obj A).X) :
    (e.twist a (GroupScheme.baseChangePointsEquiv b A U d)).baseChangeFamily b =
      (e.baseChangeFamily b).twist (a.baseChange b) d := by
  apply ext_toFun
  intro T p g
  apply (GroupScheme.baseChangePointsEquiv b H T).injective
  rw [baseChangeFamily_toFun]
  change e.toFun ((Over.map b).map p)
      (a.act (((Over.map b).map p) ≫ GroupScheme.baseChangePointsEquiv b A U d)
        (GroupScheme.baseChangePointsEquiv b G T g)) =
    GroupScheme.baseChangePointsEquiv b H T
      ((e.baseChangeFamily b).toFun p ((a.baseChange b).act (p ≫ d) g))
  rw [baseChangeFamily_toFun, AutomorphicAction.baseChangePointsEquiv_act,
    GroupScheme.baseChangePointsEquiv_naturality]

end LocalGroupIso

namespace GroupIsomorphismScheme

variable {S S' : Scheme.{u}} {G H K A : GroupScheme S}
  (I : GroupIsomorphismScheme G H)

/-- The full family at an acted parameter is the corresponding twisted family. -/
theorem refine_actionHom (a : AutomorphicAction A G) {T : Over S}
    (d : T ⟶ A.X) (p : T ⟶ I.parameter) :
    I.universalIso.refine (lift d p ≫ I.actionHom a) =
      (I.universalIso.refine p).twist a d⁻¹ := by
  apply LocalGroupIso.ext_toFun
  intro W t g
  change I.universalIso.toFun (t ≫ (lift d p ≫ I.actionHom a)) g =
    I.universalIso.toFun (t ≫ p) (a.act (t ≫ d⁻¹) g)
  simp only [← Category.assoc, comp_lift, I.actionHom_eval, GrpObj.comp_inv]

/-- Target postcomposition retains the same inverse-precomposition action. -/
theorem postcompose_actionHom (i : H ≅ K) (a : AutomorphicAction A G)
    {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter) :
    lift d p ≫ (I.postcompose i).actionHom a = lift d p ≫ I.actionHom a := by
  apply (I.postcompose i).hom_ext
  intro W t g
  dsimp only [postcompose]
  simp only [← Category.assoc, comp_lift]
  calc
    _ = (I.postcompose i).universalIso.toFun (t ≫ p)
        (a.act (t ≫ d)⁻¹ g) := (I.postcompose i).actionHom_eval a _ _ _
    _ = I.universalIso.toFun (t ≫ p) (a.act (t ≫ d)⁻¹ g) ≫ i.hom.hom.hom := rfl
    _ = _ := congrArg (fun z => z ≫ i.hom.hom.hom)
      (I.actionHom_eval a (t ≫ d) (t ≫ p) g).symm

/-- Classification of families is compatible with the actual pullback adjunction. -/
theorem baseChange_classify (b : S' ⟶ S) {T : Over S'}
    (e : LocalGroupIso G H ((Over.map b).obj T)) :
    (I.baseChange b).classify (e.baseChangeFamily b) =
      (Over.mapPullbackAdj b).homEquiv T I.parameter (I.classify e) := by
  apply ((I.baseChange b).bijective T).1
  change (I.baseChange b).universalIso.refine
      ((I.baseChange b).classify (e.baseChangeFamily b)) = _
  calc
    _ = e.baseChangeFamily b := (I.baseChange b).refine_classify _
    _ = I.baseChangePointsEquiv b T
        ((Over.mapPullbackAdj b).homEquiv T I.parameter (I.classify e)) := by
      change _ =
        (I.universalIso.refine
          (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm
            ((Over.mapPullbackAdj b).homEquiv T I.parameter (I.classify e)))).baseChangeFamily b
      rw [Equiv.symm_apply_apply, I.refine_classify]
    _ = _ := (I.baseChangeUniversalIso_refine b _).symm

/-- The inverse-precomposition action on the actual pullback representative is
the action induced by the pullback adjunction. -/
theorem baseChange_actionHom (b : S' ⟶ S) (a : AutomorphicAction A G)
    {T : Over S'} (d : T ⟶ ((GroupScheme.baseChange b).obj A).X)
    (p : T ⟶ (I.baseChange b).parameter) :
    lift d p ≫ (I.baseChange b).actionHom (a.baseChange b) =
      (Over.mapPullbackAdj b).homEquiv T I.parameter
        (lift (GroupScheme.baseChangePointsEquiv b A T d)
          (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm p) ≫
            I.actionHom a) := by
  apply ((I.baseChange b).bijective T).1
  change (I.baseChange b).universalIso.refine
      (lift d p ≫ (I.baseChange b).actionHom (a.baseChange b)) = _
  calc
    _ = ((I.baseChange b).universalIso.refine p).twist (a.baseChange b) d⁻¹ :=
      (I.baseChange b).refine_actionHom _ _ _
    _ = (I.baseChangePointsEquiv b T p).twist (a.baseChange b) d⁻¹ :=
      congrArg (fun e => e.twist (a.baseChange b) d⁻¹)
        (I.baseChangeUniversalIso_refine b p)
    _ = (I.universalIso.refine
        (lift (GroupScheme.baseChangePointsEquiv b A T d)
          (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm p) ≫
            I.actionHom a)).baseChangeFamily b := by
      change ((I.universalIso.refine
          (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm p)).baseChangeFamily b).twist
            (a.baseChange b) d⁻¹ = _
      rw [← LocalGroupIso.baseChangeFamily_twist, map_inv, ← I.refine_actionHom]
    _ = I.baseChangePointsEquiv b T
        ((Over.mapPullbackAdj b).homEquiv T I.parameter
          (lift (GroupScheme.baseChangePointsEquiv b A T d)
            (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm p) ≫
              I.actionHom a)) := by
      change _ =
        (I.universalIso.refine
          (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm
            ((Over.mapPullbackAdj b).homEquiv T I.parameter
              (lift (GroupScheme.baseChangePointsEquiv b A T d)
                (((Over.mapPullbackAdj b).homEquiv T I.parameter).symm p) ≫
                  I.actionHom a)))).baseChangeFamily b
      rw [Equiv.symm_apply_apply]
    _ = _ := (I.baseChangeUniversalIso_refine b _).symm

end GroupIsomorphismScheme

namespace OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H K A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}

/-- Target postcomposition preserves a supplied outer quotient and its class morphism. -/
def postcompose (O : OuterIsomorphismScheme I a) (i : H ≅ K) :
    OuterIsomorphismScheme (I.postcompose i) a where
  parameter := O.parameter
  classMap := O.classMap
  flat := O.flat
  surjective := O.surjective
  quasiCompact := O.quasiCompact
  invariant T d p :=
    (congrArg (fun z : T ⟶ I.parameter => z ≫ O.classMap)
      (I.postcompose_actionHom i a d p)).trans (O.invariant T d p)
  orbit T p q hpq := by
    obtain ⟨d, hd, hu⟩ := O.orbit T p q hpq
    exact ⟨d, (I.postcompose_actionHom i a d p).trans hd,
      fun c hc => hu c ((I.postcompose_actionHom i a c p).symm.trans hc)⟩

end OuterIsomorphismScheme

end Langlands.GroupScheme
