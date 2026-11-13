import Langlands.Sheaf.Renard.SingletonEquivalenceStatement

/-!
# Proof of the Renard III.3.2 singleton identification

The published original-section unit and literal coefficient-evaluation counit
are invertible on the actual singleton, satisfy both triangle laws, and so make
the two exact singleton functors equivalences.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Langlands.Sheaf.Renard.SingletonEquivalence

open CategoryTheory TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.SectionActions.SingletonSheaves

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The label-one inclusion of a transport object into the whole singleton. -/
def toTop (U : ActionOpens G PUnit) : U ⟶ ActionOpens.top :=
  ActionOpens.inclusionHom le_top

theorem toTop_comp_topArrow (U : ActionOpens G PUnit) (y : U.openSet) :
    toTop U ≫ topArrow G U y = 𝟙 U :=
  ActionOpens.Hom.ext (mul_one (1 : G))

theorem topArrow_comp_toTop (U : ActionOpens G PUnit) (y : U.openSet) :
    topArrow G U y ≫ toTop U = 𝟙 ActionOpens.top :=
  ActionOpens.Hom.ext (mul_one (1 : G))

/-- Extending a local section to the whole singleton and restricting back is the identity. -/
theorem restrict_extend (F : ActionSheaf G PUnit) (U : ActionOpens G PUnit)
    (y : U.openSet) (s : F.obj.obj (op U)) :
    F.obj.map (toTop U).op (F.obj.map (topArrow G U y).op s) = s := by
  change (F.obj.map (topArrow G U y).op ≫ F.obj.map (toTop U).op).hom s = s
  rw [← F.obj.map_comp, ← op_comp, toTop_comp_topArrow, op_id, F.obj.map_id]
  rfl

/-- Restricting a global section to a nonempty open and extending back is the identity. -/
theorem extend_restrict (F : ActionSheaf G PUnit) (U : ActionOpens G PUnit)
    (y : U.openSet) (t : F.obj.obj (op ActionOpens.top)) :
    F.obj.map (topArrow G U y).op (F.obj.map (toTop U).op t) = t := by
  change (F.obj.map (toTop U).op ≫ F.obj.map (topArrow G U y).op).hom t = t
  rw [← F.obj.map_comp, ← op_comp, topArrow_comp_toTop, op_id, F.obj.map_id]
  rfl

/-- Sections over an empty transport object vanish, by the actual sheaf condition. -/
theorem subsingleton_of_empty (F : ActionSheaf G PUnit) (U : ActionOpens G PUnit)
    (hU : U.openSet = ⊥) : Subsingleton (F.obj.obj (op U)) := by
  have ht := TopCat.Sheaf.isTerminalOfEqEmpty
    ((toSheaf G PUnit (ModuleCat.{0} ℂ)).obj F) hU
  have h0 : (𝟙 _ : F.obj.obj (op U) ⟶ F.obj.obj (op U)) = 0 := ht.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h0) a
  have hb : b = 0 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h0) b
  rw [ha, hb]

/-- Each component of the original-section unit is a linear bijection. -/
theorem toCoefficientSection_bijective (F : ActionSheaf G PUnit) (U : ActionOpens G PUnit) :
    Function.Bijective (toCoefficientSection F U) := by
  by_cases hU : Nonempty U.openSet
  · obtain ⟨y⟩ := hU
    constructor
    · intro s t h
      have h' : F.obj.map (topArrow G U y).op s = F.obj.map (topArrow G U y).op t :=
        congrArg (fun f => (LocallyConstant.toFun f y).val) h
      rw [← restrict_extend F U y s, ← restrict_extend F U y t, h']
    · intro f
      refine ⟨F.obj.map (toTop U).op (f y).val, ?_⟩
      apply LocallyConstant.ext
      intro z
      obtain rfl : z = y := Subsingleton.elim z y
      apply Subtype.ext
      exact extend_restrict F U z (f z).val
  · have hbot : U.openSet = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hU ⟨⟨x, hx⟩⟩
    have := subsingleton_of_empty F U hbot
    have : Subsingleton (LocallyConstant U.openSet
        (Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj))) :=
      ⟨fun a b => LocallyConstant.ext fun z => (hU ⟨z⟩).elim⟩
    exact ⟨fun a b _ => Subsingleton.elim a b, fun f => ⟨0, Subsingleton.elim _ _⟩⟩

instance isIso_unit_app (F : SmoothActionSheaf G PUnit) : IsIso ((unit G).app F) := by
  have : ∀ U, IsIso (((unit G).app F).hom.hom.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2 (toCoefficientSection_bijective F.obj U.unop)
  have : IsIso ((unit G).app F).hom.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafProperty G PUnit (ModuleCat.{0} ℂ)).ι.map ((unit G).app F).hom) :=
    (inferInstance : IsIso ((unit G).app F).hom.hom)
  have : IsIso ((unit G).app F).hom :=
    (sheafProperty G PUnit (ModuleCat.{0} ℂ)).fullyFaithfulι.isIso_of_isIso_map _
  have : IsIso ((smoothActionProperty G PUnit).ι.map ((unit G).app F)) :=
    (inferInstance : IsIso ((unit G).app F).hom)
  exact (smoothActionProperty G PUnit).fullyFaithfulι.isIso_of_isIso_map _

instance isIso_unit : IsIso (unit G) := NatIso.isIso_of_isIso_app _

/-- The constant compact coefficient section with a given value. -/
def constSection (A : Langlands.SmoothRep.{0, uG, 0} ℂ G) :
    Representation.IntertwiningMap A.representation
      ((gammaC G PUnit).obj ((functor G).obj A)).representation where
  toLinearMap :=
    { toFun a := ⟨LocallyConstant.const (⊤ : Opens PUnit) a, (Set.toFinite _).isCompact⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change A.representation g a = A.representation (g⁻¹)⁻¹ a
    rw [inv_inv]

instance isIso_counit_app (A : Langlands.SmoothRep.{0, uG, 0} ℂ G) :
    IsIso ((counit G).app A) :=
  ⟨⟨Langlands.SmoothRep.ofHom (constSection A),
    by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      apply LocallyConstant.ext
      intro x
      rfl,
    by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      rfl⟩⟩

instance isIso_counit : IsIso (counit G) := NatIso.isIso_of_isIso_app _

/-- The first triangle law: unit followed by evaluation is the identity on compact sections. -/
theorem triangle_gammaC (F : SmoothActionSheaf G PUnit) :
    (gammaC G PUnit).map ((unit G).app F) ≫
        (counit G).app ((gammaC G PUnit).obj F) =
      𝟙 ((gammaC G PUnit).obj F) := by
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change F.obj.obj.map (topArrow G ActionOpens.top ⟨PUnit.unit, trivial⟩).op s.val = s.val
  have h : topArrow G (ActionOpens.top (G := G) (X := PUnit)) ⟨PUnit.unit, trivial⟩ =
      𝟙 ActionOpens.top := ActionOpens.Hom.ext rfl
  rw [h, op_id, F.obj.obj.map_id]
  rfl

/-- The second triangle law: on the coefficient sheaf, unit then evaluation is the identity. -/
theorem triangle_functor (A : Langlands.SmoothRep.{0, uG, 0} ℂ G) :
    (unit G).app ((functor G).obj A) ≫ (functor G).map ((counit G).app A) =
      𝟙 ((functor G).obj A) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply LocallyConstant.ext
  intro y
  change A.representation (1 : G)⁻¹ (LocallyConstant.toFun s ⟨(1 : G) • PUnit.unit, _⟩) =
    LocallyConstant.toFun s y
  rw [inv_one, map_one]
  rfl

variable (G) in
/-- The singleton equivalence built from the exact published unit and counit. -/
def equivalence : SmoothActionSheaf G PUnit ≌ Langlands.SmoothRep.{0, uG, 0} ℂ G :=
  Equivalence.mk' (gammaC G PUnit) (functor G) (asIso (unit G)) (asIso (counit G))
    triangle_gammaC

/-- Renard III.3.2: the singleton identification, with the exact unit and counit. -/
theorem statement : Statement.{uG} := by
  intro G _ _ _ _
  exact ⟨inferInstance, inferInstance, triangle_gammaC, triangle_functor,
    (equivalence G).isEquivalence_functor, (equivalence G).isEquivalence_inverse⟩

end Langlands.Sheaf.Renard.SingletonEquivalence
