import Langlands.AlgebraicGeometry.Modules.Rigidification
import Langlands.AlgebraicGeometry.Modules.PullbackTensorStatement

/-! # Tensor products of rigidified module sheaves -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule.RigidifiedModule

open Langlands.Scheme.Modules

variable {S X : Scheme.{u}} {ε : S ⟶ X}
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Tensor the underlying sheaves and the two rigidifications, using the inverse of the
canonical pullback comparison. -/
def tensorObj (M N : RigidifiedModule ε) : RigidifiedModule ε := by
  letI := preservation ε
  exact
    { carrier := Langlands.Scheme.Modules.tensorObj M.carrier N.carrier
      rigidification :=
        (tensorLeftUnitor (structureModule S)).symm ≪≫
          (Langlands.Scheme.Modules.tensorFunctor S).mapIso
            (M.rigidification.prod N.rigidification) ≪≫
          ((asIso (pullbackTensorComparison ε)).app (M.carrier, N.carrier)).symm }

/-- Composing the tensor rigidification with the canonical comparison recovers the
tensor of the original rigidifications. -/
lemma tensorObj_rigidification_comp (M N : RigidifiedModule ε) :
    (tensorObj preservation M N).rigidification.hom ≫
        pullbackTensorComparisonApp ε M.carrier N.carrier =
      (tensorLeftUnitor (structureModule S)).inv ≫
        Langlands.Scheme.Modules.tensorMap M.rigidification.hom N.rigidification.hom := by
  let := preservation ε
  simp [tensorObj, ← pullbackTensorComparison_app, Category.assoc]
  rfl

/-- Tensoring compatible morphisms preserves the tensor rigidification. -/
lemma tensorMap_compatibility {M M' N N' : RigidifiedModule ε}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tensorObj preservation M N).rigidification.hom ≫
        (Scheme.Modules.pullback ε).map
          (Langlands.Scheme.Modules.tensorMap f.val g.val) =
      (tensorObj preservation M' N').rigidification.hom := by
  let := preservation ε
  apply (cancel_mono ((asIso (pullbackTensorComparison ε)).app
    (M'.carrier, N'.carrier)).hom).1
  change
    ((tensorObj preservation M N).rigidification.hom ≫
      (Scheme.Modules.pullback ε).map
        (Langlands.Scheme.Modules.tensorMap f.val g.val)) ≫
        pullbackTensorComparisonApp ε M'.carrier N'.carrier =
      (tensorObj preservation M' N').rigidification.hom ≫
        pullbackTensorComparisonApp ε M'.carrier N'.carrier
  erw [Category.assoc, pullbackTensorComparisonApp_naturality ε f.val g.val, ← Category.assoc,
    tensorObj_rigidification_comp, tensorObj_rigidification_comp, Category.assoc,
    Langlands.Scheme.Modules.tensorMap_comp M.rigidification.hom
      ((Scheme.Modules.pullback ε).map f.val) N.rigidification.hom
      ((Scheme.Modules.pullback ε).map g.val), f.property, g.property]
  rfl

/-- The actual tensor map between rigidified module sheaves. -/
def tensorMap {M M' N N' : RigidifiedModule ε} (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj preservation M N ⟶ tensorObj preservation M' N' :=
  ⟨Langlands.Scheme.Modules.tensorMap f.val g.val,
    tensorMap_compatibility preservation f g⟩

/-- The tensor bifunctor on rigidified module sheaves. -/
def tensorFunctor (ε : S ⟶ X) :
    RigidifiedModule ε × RigidifiedModule ε ⥤ RigidifiedModule ε where
  obj MN := tensorObj preservation MN.1 MN.2
  map fg := tensorMap preservation fg.1 fg.2
  map_id MN := by
    apply Subtype.ext
    exact (Langlands.Scheme.Modules.tensorFunctor X).map_id (MN.1.carrier, MN.2.carrier)
  map_comp fg hk := by
    apply Subtype.ext
    exact (Langlands.Scheme.Modules.tensorMap_comp fg.1.val hk.1.val fg.2.val hk.2.val).symm

/-- Forgetting the tensor rigidification gives precisely the published sheaf tensor bifunctor. -/
def tensorForgetIso (ε : S ⟶ X) :
    tensorFunctor preservation ε ⋙ forget ε ≅
      (forget ε).prod (forget ε) ⋙ Langlands.Scheme.Modules.tensorFunctor X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ _; simp; rfl)

end Langlands.SchemeModule.RigidifiedModule
