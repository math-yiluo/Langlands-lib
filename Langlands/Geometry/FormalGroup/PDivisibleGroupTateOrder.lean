import Langlands.Geometry.FormalGroup.PDivisibleGroupTateSections
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.Hom

/-! # The integral action on schematic Tate points -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable {O : Type v} [Ring O] {G H : PDivisibleGroup R p}

/-- The action on a test section induced by the action on the actual tower. -/
def schematicTateOrderAction (ρ : O →+* End G) (T : (Over (Spec R))ᵒᵖ) :
    O →+* AddMonoid.End (((schematicTatePointFunctor R p).obj G).obj T) := by
  let F := schematicTatePointFunctor R p ⋙ (evaluation _ _).obj T
  let e : End G →+* AddMonoid.End (F.obj G) :=
    { toFun f := (F.map f).hom
      map_one' := congrArg AddCommGrpCat.Hom.hom (F.map_id G)
      map_mul' f g := congrArg AddCommGrpCat.Hom.hom (F.map_comp g f)
      map_zero' := congrArg AddCommGrpCat.Hom.hom (F.map_zero G G)
      map_add' f g := congrArg AddCommGrpCat.Hom.hom (F.map_add (f := f) (g := g)) }
  exact e.comp ρ

@[simp] theorem schematicTateOrderAction_apply (ρ : O →+* End G) (T : (Over (Spec R))ᵒᵖ) (a : O)
    (x : ((schematicTatePointFunctor R p).obj G).obj T) :
    schematicTateOrderAction ρ T a x = ((schematicTatePointFunctor R p).map (ρ a)).app T x := rfl

/-- The test-section group is a left module over the acting ring. -/
@[instance_reducible] def schematicTatePointModule (ρ : O →+* End G) (T : (Over (Spec R))ᵒᵖ) :
    Module O (((schematicTatePointFunctor R p).obj G).obj T) :=
  Module.compHom _ (schematicTateOrderAction ρ T)

/-- Restrictions of schematic Tate sections are linear over the acting ring. -/
def schematicTateModulePresheaf (ρ : O →+* End G) :
    (Over (Spec R))ᵒᵖ ⥤ ModuleCat.{u} O where
  obj T := @ModuleCat.of O _ (((schematicTatePointFunctor R p).obj G).obj T) _
    (schematicTatePointModule ρ T)
  map {T U} b := by
    letI := schematicTatePointModule ρ T
    letI := schematicTatePointModule ρ U
    exact ModuleCat.ofHom
      { (((schematicTatePointFunctor R p).obj G).map b).hom with
        map_smul' a x := (ConcreteCategory.congr_hom
          (((schematicTatePointFunctor R p).map (ρ a)).naturality b) x).symm }
  map_id T := by
    apply (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}).map_injective
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom (((schematicTatePointFunctor R p).obj G).map_id T) x
  map_comp b c := by
    apply (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}).map_injective
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom (((schematicTatePointFunctor R p).obj G).map_comp b c) x

/-- The underlying additive point presheaf is the schematic Tate point presheaf. -/
def schematicTateModulePresheafForgetIso (ρ : O →+* End G) :
    schematicTateModulePresheaf ρ ⋙ forget₂ _ AddCommGrpCat.{u} ≅
      (schematicTatePointFunctor R p).obj G :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun b => by
    let β := ((schematicTatePointFunctor R p).obj G).map b
    change β ≫ 𝟙 _ = 𝟙 _ ≫ β
    exact (Category.comp_id β).trans (Category.id_comp β).symm

/-- The module-valued schematic Tate presheaf is a sheaf for subcanonical topologies. -/
theorem isSheaf_schematicTateModules (ρ : O →+* End G)
    (J : GrothendieckTopology (Over (Spec R))) [J.Subcanonical] :
    Presheaf.IsSheaf J (schematicTateModulePresheaf ρ) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u})
  exact (Presheaf.isSheaf_of_iso_iff (J := J) (schematicTateModulePresheafForgetIso ρ)).mpr
    (G.isSheaf_schematicTatePoints J)

/-- The action on a finite component of a schematic Tate section comes from
its actual level homomorphism. -/
theorem schematicTateOrderAction_projection (ρ : O →+* End G) (T : Over (Spec R)) (a : O)
    (x : ((schematicTatePointFunctor R p).obj G).obj (op T)) (n : ℕ) :
    (G.schematicTatePointProjection n).app (op T) (schematicTateOrderAction ρ (op T) a x) =
      Additive.ofMul (((G.schematicTatePointProjection n).app (op T) x).toMul ≫
        (CommGroupScheme.groupHom ((ρ a).app n)).hom.hom) :=
  schematicTatePointProjection_map (ρ a) T x n

/-- A morphism intertwining the two order actions induces a linear map of Tate presheaves. -/
def schematicTateModulePresheafMap (ρ : O →+* End G) (σ : O →+* End H) (f : G ⟶ H)
    (hf : ∀ a, ρ a ≫ f = f ≫ σ a) :
    schematicTateModulePresheaf ρ ⟶ schematicTateModulePresheaf σ where
  app T := by
    letI := schematicTatePointModule ρ T
    letI := schematicTatePointModule σ T
    exact ModuleCat.ofHom
      { (((schematicTatePointFunctor R p).map f).app T).hom with
        map_smul' a x := by
          let F := schematicTatePointFunctor R p
          have h := congrArg F.map (hf a)
          rw [F.map_comp, F.map_comp] at h
          exact ConcreteCategory.congr_hom (NatTrans.congr_app h T) x }
  naturality T U b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (((schematicTatePointFunctor R p).map f).naturality b) x

end Langlands.PDivisibleGroup
