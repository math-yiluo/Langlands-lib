import Langlands.Sheaf.Equivariant.ActionOpens
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Equivariant sheaves for an action on a topological space

An equivariant sheaf is a presheaf on the actual transport category of opens
whose restriction to ordinary open inclusions is a sheaf. The morphisms are
natural transformations on the transport category, so they commute with both
ordinary restriction and group transport.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory TopologicalSpace Opposite

universe uX uG uA vA

variable (G : Type uG) [Group G] (X : Type uX) [TopologicalSpace X] [MulAction G X]
variable (A : Type uA) [Category.{vA} A]

/-- Forget the group-labelled arrows of a transport presheaf. -/
def underlyingPresheaf :
    ((ActionOpens G X)ᵒᵖ ⥤ A) ⥤ TopCat.Presheaf A (TopCat.of X) :=
  (Functor.whiskeringLeft (Opens X)ᵒᵖ (ActionOpens G X)ᵒᵖ A).obj
    (ActionOpens.inclusion G X).op

/-- The ordinary sheaf condition on the restriction to open inclusions. -/
def sheafProperty : ObjectProperty ((ActionOpens G X)ᵒᵖ ⥤ A) :=
  fun F => ((underlyingPresheaf G X A).obj F).IsSheaf

/-- The actual category of equivariant sheaves on the given topological action. -/
abbrev TopologicalSheaf :=
  (sheafProperty G X A).FullSubcategory

/-- Forget the sheaf condition while retaining all equivariant structure. -/
def toTransportPresheaf : TopologicalSheaf G X A ⥤ ((ActionOpens G X)ᵒᵖ ⥤ A) :=
  (sheafProperty G X A).ι

/-- Forget equivariance to obtain the genuine ordinary sheaf. -/
def toSheaf : TopologicalSheaf G X A ⥤ TopCat.Sheaf A (TopCat.of X) where
  obj F := ⟨(underlyingPresheaf G X A).obj F.obj, F.property⟩
  map f := ⟨(underlyingPresheaf G X A).map f.hom⟩

instance : (toTransportPresheaf G X A).Full := by
  dsimp [toTransportPresheaf]
  infer_instance

instance : (toTransportPresheaf G X A).Faithful := by
  dsimp [toTransportPresheaf]
  infer_instance

instance : (toSheaf G X A).Faithful where
  map_injective {F F'} f g h := by
    apply ObjectProperty.hom_ext
    ext U
    exact congrArg
      (fun k => k.hom.app (op U.unop.openSet)) h

instance [Preadditive A] : Preadditive (TopologicalSheaf G X A) := inferInstance

section Actions

variable {G X A}

/-- The left action on sections over the whole space. -/
def sectionAction (F : (ActionOpens G X)ᵒᵖ ⥤ A) : Action A G where
  V := F.obj (op ActionOpens.top)
  ρ :=
    { toFun g := F.map (ActionOpens.sectionArrow g).op
      map_one' := by
        change F.map (ActionOpens.sectionArrow (1 : G)).op = 𝟙 _
        rw [ActionOpens.sectionArrow_one]
        exact F.map_id _
      map_mul' g h := by
        change F.map (ActionOpens.sectionArrow (g * h)).op =
          F.map (ActionOpens.sectionArrow h).op ≫
            F.map (ActionOpens.sectionArrow g).op
        rw [ActionOpens.sectionArrow_mul, op_comp, F.map_comp] }

variable (G X A)

/-- Global sections and all equivariant maps form a functor to actions. -/
def sections : TopologicalSheaf G X A ⥤ Action A G where
  obj F := sectionAction F.obj
  map f :=
    { hom := f.hom.app (op ActionOpens.top)
      comm g := f.hom.naturality (ActionOpens.sectionArrow g).op }

variable {G X A}
variable (H : Subgroup G) (U : ActionOpens G X)
variable (hU : ∀ h : H, ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet)

/-- The subgroup action on sections over a stable open. -/
def invariantSectionAction (F : (ActionOpens G X)ᵒᵖ ⥤ A) : Action A H where
  V := F.obj (op U)
  ρ :=
    { toFun h := F.map (ActionOpens.invariantArrow H U hU h).op
      map_one' := by
        change F.map (ActionOpens.invariantArrow H U hU 1).op = 𝟙 _
        rw [ActionOpens.invariantArrow_one]
        exact F.map_id _
      map_mul' g h := by
        change F.map (ActionOpens.invariantArrow H U hU (g * h)).op =
          F.map (ActionOpens.invariantArrow H U hU h).op ≫
            F.map (ActionOpens.invariantArrow H U hU g).op
        rw [ActionOpens.invariantArrow_mul, op_comp, F.map_comp] }

/-- Evaluation on a stable open with its actual subgroup action. -/
def invariantSections : TopologicalSheaf G X A ⥤ Action A H where
  obj F := invariantSectionAction H U hU F.obj
  map f :=
    { hom := f.hom.app (op U)
      comm h := f.hom.naturality (ActionOpens.invariantArrow H U hU h).op }

variable {H U hU}

/-- A stable-open inclusion induces an equivariant restriction of sections. -/
def restriction {V : ActionOpens G X}
    (hV : ∀ h : H, ∀ x ∈ V.openSet, (h : G) • x ∈ V.openSet)
    (hUV : U.openSet ≤ V.openSet) :
    invariantSections (A := A) H V hV ⟶ invariantSections H U hU where
  app F :=
    { hom := F.obj.map (ActionOpens.inclusionHom hUV).op
      comm h := by
        change F.obj.map (ActionOpens.invariantArrow H V hV h).op ≫
            F.obj.map (ActionOpens.inclusionHom hUV).op =
          F.obj.map (ActionOpens.inclusionHom hUV).op ≫
            F.obj.map (ActionOpens.invariantArrow H U hU h).op
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        apply ActionOpens.Hom.ext
        simp [ActionOpens.inclusionHom, ActionOpens.invariantArrow] }
  naturality F F' f := by
    apply Action.Hom.ext
    exact (f.hom.naturality (ActionOpens.inclusionHom hUV).op).symm

end Actions

section Translation

variable {G X A} [ContinuousConstSMul G X]

/-- A moving-space equivariant sheaf transports sections to translated opens. -/
def translateSections (F : TopologicalSheaf G X A) (g : G)
    (U : ActionOpens G X) :
    F.obj.obj (op U) ≅ F.obj.obj (op (ActionOpens.translate g U)) :=
  (F.obj.mapIso (ActionOpens.translationIso g U).op).symm

theorem translateSections_naturality {F F' : TopologicalSheaf G X A}
    (f : F ⟶ F') (g : G) (U : ActionOpens G X) :
    (translateSections F g U).hom ≫ f.hom.app (op (ActionOpens.translate g U)) =
      f.hom.app (op U) ≫ (translateSections F' g U).hom :=
  f.hom.naturality (ActionOpens.translationIso g U).inv.op

end Translation

end Langlands.Sheaf.Equivariant
