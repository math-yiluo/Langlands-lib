import Langlands.Sheaf.Renard.SectionActions
import Langlands.Sheaf.Equivariant.LocallyConstantSmooth
import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Mathlib.Algebra.Module.PUnit

/-!
# The singleton sheaf functors in Renard III.3.2

Representations give the existing full locally constant sheaf on PUnit.
The comparison maps use evaluation and original restrictions of sections.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions.SingletonSheaves

open CategoryTheory TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant

universe uG

variable (G : Type uG) [Group G] [TopologicalSpace G]

instance singletonContinuousSMul : ContinuousSMul G PUnit where
  continuous_smul := continuous_const

instance singletonStableNeighbourhoods : HasStableNeighbourhoods G PUnit where
  exists_stable x O hO hx := by
    refine ⟨⊤, O, hO, hx, Set.Subset.rfl, ?_⟩
    intro g _ y hy
    rwa [Subsingleton.elim (g • y) y]

/-- The existing full locally constant coefficient sheaf on the actual singleton. -/
def algebraic : Rep.{0} ℂ G ⥤ ActionSheaf G PUnit :=
  LocallyConstantSheaf.functor ℂ G PUnit

/-- The same original singleton sheaf, with smoothness on all compact sections. -/
def functor : Langlands.SmoothRep.{0, uG, 0} ℂ G ⥤ SmoothActionSheaf G PUnit :=
  (smoothActionProperty G PUnit).lift
    (Langlands.SmoothRep.toRep ⋙ algebraic G)
    (fun A => CompactSections.isSmooth_representation_of_isSmoothSheaf
      (LocallyConstantSheaf.isSmoothSheaf A.representation A.isSmooth))

/-- A point of an open singleton set makes the whole singleton lie in that open. -/
def topArrow (U : ActionOpens G PUnit) (y : U.openSet) : ActionOpens.top ⟶ U :=
  ⟨1, fun z _ => by
    rw [one_smul, Subsingleton.elim z y.val]
    exact y.property⟩

variable {G}

/-- Original restriction to the same open, viewed as a global compact section. -/
def compactFromLocal (F : ActionSheaf G PUnit) (U : ActionOpens G PUnit) (y : U.openSet) :
    F.obj.obj (op U) →ₗ[ℂ]
      Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj) where
  toFun s := ⟨F.obj.map (topArrow G U y).op s, (Set.toFinite _).isCompact⟩
  map_add' s t := Subtype.ext ((F.obj.map (topArrow G U y).op).hom.map_add s t)
  map_smul' c s := Subtype.ext ((F.obj.map (topArrow G U y).op).hom.map_smul c s)

/-- Each original local section determines its locally constant compact-section value. -/
def toCoefficientSection (F : ActionSheaf G PUnit) (U : ActionOpens G PUnit) :
    F.obj.obj (op U) →ₗ[ℂ]
      LocallyConstant U.openSet
        (Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj)) where
  toFun s := ⟨fun y => compactFromLocal F U y s, IsLocallyConstant.of_discrete _⟩
  map_add' s t := LocallyConstant.ext (fun y => (compactFromLocal F U y).map_add s t)
  map_smul' c s := LocallyConstant.ext (fun y => (compactFromLocal F U y).map_smul c s)

/-- The original singleton sheaf maps canonically into the sheaf of its compact sections. -/
def unitComponent (F : SmoothActionSheaf G PUnit) :
    F.obj ⟶ (algebraic G).obj ((gammaC G PUnit).obj F).obj :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (toCoefficientSection F.obj U.unop)
      naturality U V m := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        apply LocallyConstant.ext
        intro y
        apply Subtype.ext
        change F.obj.obj.map (topArrow G V.unop y).op (F.obj.obj.map m s) =
          (globalRepresentation F.obj m.unop.label⁻¹)
            (F.obj.obj.map (topArrow G U.unop (LocallyConstantSheaf.pointMap m.unop y)).op s)
        change (F.obj.obj.map m ≫ F.obj.obj.map (topArrow G V.unop y).op).hom s =
          (F.obj.obj.map (topArrow G U.unop (LocallyConstantSheaf.pointMap m.unop y)).op ≫
            F.obj.obj.map (ActionOpens.sectionArrow m.unop.label⁻¹).op).hom s
        rw [← F.obj.obj.map_comp, ← F.obj.obj.map_comp]
        have h : topArrow G V.unop y ≫ m.unop =
            ActionOpens.sectionArrow m.unop.label⁻¹ ≫
              topArrow G U.unop (LocallyConstantSheaf.pointMap m.unop y) := by
          apply ActionOpens.Hom.ext
          simp [topArrow, ActionOpens.sectionArrow]
        exact congrArg (fun a => (F.obj.obj.map a.op).hom s) h }

variable (G)

/-- The natural original-section comparison for the two singleton functors. -/
def unit : 𝟭 (SmoothActionSheaf G PUnit) ⟶ gammaC G PUnit ⋙ functor G where
  app F := ObjectProperty.homMk (unitComponent F)
  naturality F F' k := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro y
    apply Subtype.ext
    exact congrArg (fun a => a.hom s)
      (k.hom.hom.naturality (topArrow G U.unop y).op).symm

variable {G}

/-- Evaluate the actual compact singleton coefficient section at its point. -/
def evaluation (A : Langlands.SmoothRep.{0, uG, 0} ℂ G) :
    Representation.IntertwiningMap
      ((gammaC G PUnit).obj ((functor G).obj A)).representation A.representation where
  toLinearMap :=
    { toFun s := LocallyConstant.toFun
        (show LocallyConstant (⊤ : Opens PUnit) A from s.val) ⟨PUnit.unit, trivial⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro s
    change A.representation (g⁻¹)⁻¹
        (LocallyConstant.toFun s.val ⟨g⁻¹ • PUnit.unit, _⟩) =
      A.representation g (LocallyConstant.toFun s.val ⟨PUnit.unit, trivial⟩)
    rw [inv_inv]

variable (G)

/-- The natural coefficient evaluation for singleton sheaves. -/
def counit : functor G ⋙ gammaC G PUnit ⟶ 𝟭 (Langlands.SmoothRep.{0, uG, 0} ℂ G) where
  app A := Langlands.SmoothRep.ofHom (evaluation A)
  naturality A B k := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro s
    rfl

/-- The unit sends an original local section by its original restriction map. -/
theorem unit_apply (F : SmoothActionSheaf G PUnit) (U : ActionOpens G PUnit)
    (s : F.obj.obj.obj (op U)) (y : U.openSet) :
    LocallyConstant.toFun ((((unit G).app F).hom.hom.app (op U)).hom s) y =
      compactFromLocal F.obj U y s := rfl

/-- The counit is literal coefficient evaluation at the original singleton point. -/
theorem counit_apply (A : Langlands.SmoothRep.{0, uG, 0} ℂ G)
    (s : (gammaC G PUnit).obj ((functor G).obj A)) :
    Langlands.SmoothRep.hom ((counit G).app A) s =
      LocallyConstant.toFun (show LocallyConstant (⊤ : Opens PUnit) A from s.val)
        ⟨PUnit.unit, trivial⟩ := rfl

end Langlands.Sheaf.Renard.SectionActions.SingletonSheaves
