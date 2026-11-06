import Langlands.GroupScheme.Descent.FiniteStageIso
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormFiniteSeparable

/-! # Exact recovery of finite-stage local isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Descent.FiniteStage

open Langlands.AlgebraicGeometry.Picard

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {e : (baseChange (algebraBaseMap k Ω)).obj G ≅
    (baseChange (algebraBaseMap k Ω)).obj H}

private theorem hom_comp_left {S : Scheme.{u}} {G H J : GroupScheme S}
    (f : G ⟶ H) (g : H ⟶ J) :
    (f ≫ g).hom.hom.left = f.hom.hom.left ≫ g.hom.hom.left := rfl

@[reassoc]
private theorem baseChange_map_left_fst {S V : Scheme.{u}} (b : V ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left := by
  change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
  simp only [Over.pullback_map_left, pullback.lift_fst]

@[reassoc]
private theorem projection_fst (G : GroupScheme (Spec (CommRingCat.of k)))
    (E : FinIntermediateField k Ω) :
    (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) ≫
        pullback.fst G.X.hom (algebraBaseMap k E.1) =
      pullback.fst G.X.hom (algebraBaseMap k Ω) := by
  simp only [baseChangeCone, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
private theorem projection_snd (G : GroupScheme (Spec (CommRingCat.of k)))
    (E : FinIntermediateField k Ω) :
    (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) ≫
        pullback.snd G.X.hom (algebraBaseMap k E.1) =
      pullback.snd G.X.hom (algebraBaseMap k Ω) ≫ algebraBaseMap E.1 Ω := by
  simp only [baseChangeCone, pullback.map, pullback.lift_snd]

/-- The finite-stage recovery equation commutes with the actual scheme projections. -/
@[reassoc]
theorem IsoModel.recovery_projection (D : IsoModel k Ω e) :
    (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op D.fieldOfDefinition) ≫
        D.iso.hom.hom.hom.left =
      e.hom.hom.hom.left ≫
        (baseChangeCone (Ω := Ω) H.X.left H.X.hom).π.app (op D.fieldOfDefinition) := by
  have h := congrArg (fun f => f.hom.hom.left) D.recovery
  rw [hom_comp_left, hom_comp_left] at h
  let E := D.fieldOfDefinition
  let cG := (comparison k Ω E G).hom.hom.hom.left
  let cH := (comparison k Ω E H).hom.hom.hom.left
  let i := D.iso.hom.hom.hom.left
  let m := ((baseChange (algebraBaseMap E.1 Ω)).map D.iso.hom).hom.hom.left
  let pG := pullback.fst (pullback.snd G.X.hom (algebraBaseMap k E.1))
    (algebraBaseMap E.1 Ω)
  let pH := pullback.fst (pullback.snd H.X.hom (algebraBaseMap k E.1))
    (algebraBaseMap E.1 Ω)
  calc
    _ = (cG ≫ pG) ≫ i :=
      congrArg (fun z => z ≫ i) (comparison_hom_fst k Ω E G).symm
    _ = cG ≫ (pG ≫ i) := Category.assoc _ _ _
    _ = cG ≫ (m ≫ pH) :=
      congrArg (fun z => cG ≫ z)
        (baseChange_map_left_fst (algebraBaseMap E.1 Ω) D.iso.hom).symm
    _ = (cG ≫ m) ≫ pH := (Category.assoc _ _ _).symm
    _ = (e.hom.hom.hom.left ≫ cH) ≫ pH :=
      congrArg (fun z => z ≫ pH) h
    _ = e.hom.hom.hom.left ≫ (cH ≫ pH) := Category.assoc _ _ _
    _ = _ := congrArg (fun z => e.hom.hom.hom.left ≫ z)
      (comparison_hom_fst k Ω E H)

/-- Refining the finite-stage local family recovers the specified original family. -/
theorem IsoModel.localIso_refine (D : IsoModel k Ω e) :
    D.localIso.refine
        (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val) =
      LocalGroupIso.ofBaseChangeIso e := by
  apply LocalGroupIso.ext_toFun
  intro T a g
  let r := QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val
  let x := (LocalGroupIso.coverPointsEquiv G a).symm g
  have hx : x.left ≫ pullback.fst G.X.hom (algebraBaseMap k Ω) = g.left := by
    exact congrArg (fun t => t.left)
      ((LocalGroupIso.coverPointsEquiv G a).apply_symm_apply g)
  have hxlift :
      ((LocalGroupIso.coverPointsEquiv G (a ≫ r)).symm g).left =
        x.left ≫
          (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app
            (op D.fieldOfDefinition) := by
    apply pullback.hom_ext
    · have hy := congrArg (fun t => t.left)
        ((LocalGroupIso.coverPointsEquiv G (a ≫ r)).apply_symm_apply g)
      rw [LocalGroupIso.coverPointsEquiv_left] at hy
      calc
        _ = g.left := hy
        _ = x.left ≫ pullback.fst G.X.hom (algebraBaseMap k Ω) := hx.symm
        _ = x.left ≫
            ((baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app
              (op D.fieldOfDefinition) ≫
                pullback.fst G.X.hom (algebraBaseMap k D.fieldOfDefinition.1)) :=
          congrArg (fun z => x.left ≫ z) (projection_fst G D.fieldOfDefinition).symm
        _ = _ := (Category.assoc _ _ _).symm
    · change ((LocalGroupIso.coverPointsEquiv G (a ≫ r)).symm g).left ≫
          pullback.snd _ _ =
        x.left ≫
          (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app
            (op D.fieldOfDefinition) ≫ pullback.snd _ _
      have hy :
          ((LocalGroupIso.coverPointsEquiv G (a ≫ r)).symm g).left ≫
            pullback.snd G.X.hom (algebraBaseMap k D.fieldOfDefinition.1) =
          (a ≫ r).left :=
        Over.w ((LocalGroupIso.coverPointsEquiv G (a ≫ r)).symm g)
      calc
        _ = (a ≫ r).left := hy
        _ = a.left ≫ r.left := rfl
        _ = (x.left ≫ pullback.snd G.X.hom (algebraBaseMap k Ω)) ≫ r.left :=
          congrArg (fun z => z ≫ r.left) (Over.w x).symm
        _ = x.left ≫ (pullback.snd G.X.hom (algebraBaseMap k Ω) ≫ r.left) :=
          Category.assoc _ _ _
        _ = x.left ≫
            ((baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app
              (op D.fieldOfDefinition) ≫
                pullback.snd G.X.hom (algebraBaseMap k D.fieldOfDefinition.1)) :=
          congrArg (fun z => x.left ≫ z) (projection_snd G D.fieldOfDefinition).symm
        _ = _ := (Category.assoc _ _ _).symm
  apply Over.OverMorphism.ext
  change ((LocalGroupIso.ofBaseChangeIso D.iso).toFun (a ≫ r) g).left =
    ((LocalGroupIso.ofBaseChangeIso e).toFun a g).left
  rw [LocalGroupIso.ofBaseChangeIso_toFun_left,
    LocalGroupIso.ofBaseChangeIso_toFun_left, hxlift]
  simp only [Category.assoc]
  rw [D.recovery_projection_assoc]
  exact congrArg (fun z => x.left ≫ e.hom.hom.hom.left ≫ z)
    (projection_fst H D.fieldOfDefinition)

/-- Extend the finite model's natural local equivalences back to the larger field. -/
def IsoModel.refinedLocalIso (D : IsoModel k Ω e) :
    LocalGroupIso G H (Over.mk (algebraBaseMap k Ω)) :=
  D.localIso.refine
    (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val)

/-- The constructed family is exactly the one attached to the specified isomorphism. -/
theorem IsoModel.refinedLocalIso_eq (D : IsoModel k Ω e) :
    D.refinedLocalIso = LocalGroupIso.ofBaseChangeIso e :=
  D.localIso_refine

end Langlands.GroupScheme.Descent.FiniteStage
