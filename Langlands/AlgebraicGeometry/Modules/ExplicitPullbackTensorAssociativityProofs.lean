import Langlands.AlgebraicGeometry.Modules.PullbackTensorAssociativityStatements
import Langlands.AlgebraicGeometry.Modules.PushforwardTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorAssociativity

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

-- Adapted from Worker 339's private adjoint_tensor calculation.
private lemma adjoint_tensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {P Q : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ⟶ P)
    (b : (Scheme.Modules.pullback f).obj N ⟶ Q) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackTensorComparisonApp f M N ≫ tensorMap a b) =
    tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ b) ≫
        pushforwardTensorApp f P Q := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_pullbackTensorComparisonApp,
    Category.assoc, ← pushforwardTensorApp_naturality, ← Category.assoc, tensorMap_comp]
  rfl

set_option maxHeartbeats 800000 in
/-- Transfer canonical pushforward associativity through the fixed adjunction. -/
lemma explicitPullbackTensorAssociativity_of_pushforward
    (h : PushforwardTensorAssociativityStatement.{u}) :
    ExplicitPullbackTensorAssociativityStatement.{u} := by
  intro X Y f M N P
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, adjoint_tensor,
    Adjunction.homEquiv_naturality_left, adjoint_tensor,
    homEquiv_pullbackTensorComparisonApp, homEquiv_pullbackTensorComparisonApp,
    Adjunction.homEquiv_id, Adjunction.homEquiv_id]
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pushforward f
  change (tensorMap (tensorMap (η.app M) (η.app N) ≫ pushforwardTensorApp f (F.obj M) (F.obj N))
      (η.app P) ≫ pushforwardTensorApp f (tensorObj (F.obj M) (F.obj N)) (F.obj P)) ≫
      G.map (tensorAssociator (F.obj M) (F.obj N) (F.obj P)).hom =
    (tensorAssociator M N P).hom ≫
      tensorMap (η.app M)
        (tensorMap (η.app N) (η.app P) ≫ pushforwardTensorApp f (F.obj N) (F.obj P)) ≫
      pushforwardTensorApp f (F.obj M) (tensorObj (F.obj N) (F.obj P))
  have hl : tensorMap (tensorMap (η.app M) (η.app N) ≫ pushforwardTensorApp f (F.obj M) (F.obj N))
      (η.app P) =
      tensorMap (tensorMap (η.app M) (η.app N)) (η.app P) ≫
        tensorMap (pushforwardTensorApp f (F.obj M) (F.obj N)) (𝟙 (G.obj (F.obj P))) := by
    rw [tensorMap_comp]
    erw [Category.comp_id]
  have hr : tensorMap (η.app M)
      (tensorMap (η.app N) (η.app P) ≫ pushforwardTensorApp f (F.obj N) (F.obj P)) =
      tensorMap (η.app M) (tensorMap (η.app N) (η.app P)) ≫
        tensorMap (𝟙 (G.obj (F.obj M))) (pushforwardTensorApp f (F.obj N) (F.obj P)) := by
    rw [tensorMap_comp]
    erw [Category.comp_id]
  rw [hl, hr]
  simp only [Category.assoc]
  rw [h X Y f (F.obj M) (F.obj N) (F.obj P)]
  rw [← Category.assoc]
  erw [tensorAssociator_naturality (η.app M) (η.app N) (η.app P)]
  simp only [Category.assoc]
  rfl

/-- The canonical pullback tensor comparison respects the fixed associator. -/
theorem explicitPullbackTensorAssociativity :
    ExplicitPullbackTensorAssociativityStatement.{u} :=
  explicitPullbackTensorAssociativity_of_pushforward pushforwardTensorAssociativity

end Langlands.Scheme.Modules
