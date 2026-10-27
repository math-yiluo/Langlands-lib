import Langlands.CategoryTheory.EquivariantDiagram
import Langlands.CategoryTheory.TopCatSelfForget
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-! # Continuous limit actions for varying profinite-group diagrams -/

noncomputable section

universe u v w

namespace Langlands.EquivariantDiagram

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {J : Type v} [SmallCategory J] (D : J ⥤ ProfiniteGrp.{max u v})
local instance (j : J) : TopologicalSpace ((D ⋙ forget₂ ProfiniteGrp GrpCat).obj j) :=
  inferInstanceAs (TopologicalSpace (D.obj j))

variable (F : EquivariantDiagram (D ⋙ forget₂ ProfiniteGrp GrpCat) TopCat.{max u v w})

/-- The coordinatewise action preserves the actual compatible-sequence space. -/
def profiniteLimitTranslate (g : ProfiniteGrp.limit D) :
    C((TopCat.limitCone.{v, max u w} F.obj).pt, (TopCat.limitCone.{v, max u w} F.obj).pt) where
  toFun x :=
    ⟨fun j => (F.ρ j (g.val j)).hom (x.val j), by
      intro i j f
      change F.obj.map f ((F.ρ i (g.val i)).hom (x.val i)) =
        (F.ρ j (g.val j)).hom (x.val j)
      rw [← g.property f, ← x.property f]
      exact congrArg (fun a : F.obj.obj i ⟶ F.obj.obj j => a (x.val i))
        (F.comm f (g.val i))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun j =>
      (F.ρ j (g.val j)).hom.continuous.comp
        ((continuous_apply j).comp continuous_subtype_val)

/-- The actual profinite group limit acts on the actual topological limit cone point. -/
def profiniteLimitUnderlyingAction :
    Action TopCat.{max u v w} (ProfiniteGrp.limit D) where
  V := (TopCat.limitCone.{v, max u w} F.obj).pt
  ρ :=
    { toFun g := TopCat.ofHom (profiniteLimitTranslate D F g)
      map_one' := by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        funext j
        change (F.ρ j 1).hom (x.val j) = x.val j
        rw [map_one]
        rfl
      map_mul' g h := by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        funext j
        change (F.ρ j (g.val j * h.val j)).hom (x.val j) =
          (F.ρ j (g.val j)).hom ((F.ρ j (h.val j)).hom (x.val j))
        rw [map_mul]
        rfl }

/-- Joint continuity is inherited coordinatewise for the product-subtype limit topology. -/
theorem profiniteLimitUnderlyingAction_isContinuous
    (hF : ∀ j, (F.action j).IsContinuous) :
    (profiniteLimitUnderlyingAction D F).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  have h : Continuous (fun p : D.obj j × F.obj.obj j => (F.ρ j p.1).hom p.2) :=
    (Action.isContinuous_def (F.action j)).mp (hF j)
  have hg : Continuous (fun p : ProfiniteGrp.limit D × (TopCat.limitCone.{v, max u w} F.obj).pt =>
      p.1.val j) :=
    ((continuous_apply j).comp continuous_subtype_val).comp continuous_fst
  have hx : Continuous (fun p : ProfiniteGrp.limit D × (TopCat.limitCone.{v, max u w} F.obj).pt =>
      p.2.val j) :=
    ((continuous_apply j).comp continuous_subtype_val).comp continuous_snd
  exact h.comp (hg.prodMk hx)

/-- Bundle the constructed jointly continuous action in Mathlib's category. -/
def profiniteLimitAction (hF : ∀ j, (F.action j).IsContinuous) :
    ContAction TopCat.{max u v w} (ProfiniteGrp.limit D) :=
  ⟨profiniteLimitUnderlyingAction D F, profiniteLimitUnderlyingAction_isContinuous D F hF⟩

/-- Every projection is equivariant along the actual continuous group-limit projection. -/
def profiniteLimitProjection (hF : ∀ j, (F.action j).IsContinuous) (j : J) :
    profiniteLimitAction D F hF ⟶
      (ContAction.res TopCat ((ProfiniteGrp.limitCone D).π.app j).hom).obj
        ⟨F.action j, hF j⟩ :=
  ObjectProperty.homMk
    { hom := (TopCat.limitCone.{v, max u w} F.obj).π.app j
      comm g := by
        apply TopCat.ext
        intro x
        rfl }

@[simp] theorem profiniteLimitProjection_apply (hF : ∀ j, (F.action j).IsContinuous)
    (j : J) (x : (TopCat.limitCone.{v, max u w} F.obj).pt) :
    (profiniteLimitProjection D F hF j).hom.hom x = x.val j :=
  rfl

variable {E : EquivariantDiagram (D ⋙ forget₂ ProfiniteGrp GrpCat) TopCat.{max u v w}}

/-- A morphism of varying-group diagrams induces an equivariant continuous map on limits. -/
def profiniteLimitMap (hF : ∀ j, (F.action j).IsContinuous)
    (hE : ∀ j, (E.action j).IsContinuous) (f : F ⟶ E) :
    profiniteLimitAction D F hF ⟶ profiniteLimitAction D E hE :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        { toFun x :=
            ⟨fun j => f.hom.app j (x.val j), by
              intro i j a
              change E.obj.map a (f.hom.app i (x.val i)) = f.hom.app j (x.val j)
              rw [← x.property a]
              exact (congrArg (fun k : F.obj.obj i ⟶ E.obj.obj j => k (x.val i))
                (f.hom.naturality a)).symm⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact continuous_pi fun j => (f.hom.app j).hom.continuous.comp
              ((continuous_apply j).comp continuous_subtype_val) }
      comm g := by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        funext j
        exact congrArg (fun k : F.obj.obj j ⟶ E.obj.obj j => k (x.val j))
          (f.comm j (g.val j)) }

@[simp] theorem profiniteLimitMap_apply (hF : ∀ j, (F.action j).IsContinuous)
    (hE : ∀ j, (E.action j).IsContinuous) (f : F ⟶ E)
    (x : (TopCat.limitCone.{v, max u w} F.obj).pt) (j : J) :
    ((profiniteLimitMap D F hF hE f).hom.hom x).val j = f.hom.app j (x.val j) :=
  rfl

/-- The standard full subcategory of diagrams with jointly continuous component actions. -/
def componentwiseContinuous :
    ObjectProperty
      (EquivariantDiagram (D ⋙ forget₂ ProfiniteGrp GrpCat) TopCat.{max u v w}) :=
  fun E => ∀ j, (E.action j).IsContinuous

/-- Taking the constructed limit action is functorial on continuous varying-group diagrams. -/
def profiniteLimitFunctor :
    (componentwiseContinuous.{u, v, w} D).FullSubcategory ⥤
      ContAction TopCat.{max u v w} (ProfiniteGrp.limit D) where
  obj F := profiniteLimitAction D F.obj F.property
  map f := profiniteLimitMap D _ _ _ f.hom
  map_id F := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    apply Subtype.ext
    funext j
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    apply Subtype.ext
    funext j
    rfl

end Langlands.EquivariantDiagram
