import Langlands.Sheaf.Equivariant.FunctionSheaf
import Langlands.Sheaf.CompactSupport

/-!
# Compactly supported sections for a moving-space action

Transport of open neighborhoods proves that the section action preserves
compact support. The resulting operators and maps are restrictions of the
already constructed section action and genuine sheaf morphisms.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory TopologicalSpace Opposite

universe u uG

variable {R : Type u} [CommRing R]
variable {G : Type uG} [Group G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X]

namespace CompactSections

variable (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)

/-- The ordinary presheaf underlying the transport data. -/
abbrev ordinary : (TopCat.of X).Presheaf (ModuleCat.{u} R) :=
  (underlyingPresheaf G X (ModuleCat.{u} R)).obj F

/-- Ordinary restriction from the whole space to a transport object. -/
def restrict (U : ActionOpens G X) :
    F.obj (op ActionOpens.top) ⟶ F.obj (op U) :=
  F.map (ActionOpens.inclusionHom (U := U) (V := ActionOpens.top) le_top).op

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of a germ is equivalent to vanishing on an actual open neighborhood. -/
theorem germ_zero_iff (s : F.obj (op ActionOpens.top)) (x : X) :
    (ordinary F).Γgerm x s = 0 ↔
      ∃ U : ActionOpens G X, x ∈ U.openSet ∧ restrict F U s = 0 := by
  constructor
  · intro hx
    obtain ⟨W, hxW, i, j, hW⟩ :=
      (ordinary F).germ_eq x (U := ⊤) (V := ⊤) trivial trivial s 0
        (by simpa [TopCat.Presheaf.Γgerm] using hx)
    refine ⟨⟨W⟩, hxW, ?_⟩
    have hzero := hW.trans (((ordinary F).map j.op).hom.map_zero)
    have hi : (ActionOpens.inclusion G X).map i =
        ActionOpens.inclusionHom
          (U := ⟨W⟩) (V := ActionOpens.top) (show W ≤ ⊤ from le_top) := by
      apply ActionOpens.Hom.ext
      rfl
    change F.map ((ActionOpens.inclusion G X).map i).op s = 0 at hzero
    rw [hi] at hzero
    exact hzero
  · rintro ⟨U, hxU, hU⟩
    rw [← (ordinary F).Γgerm_res_apply x hxU s
      (i := homOfLE (show U.openSet ≤ ⊤ from le_top))]
    change (ordinary F).germ U.openSet x hxU (restrict F U s) = 0
    rw [hU]
    exact ((ordinary F).germ U.openSet x hxU).hom.map_zero

variable [ContinuousConstSMul G X]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a transported section equals transport of its restriction. -/
theorem restrict_action (g : G) (U : ActionOpens G X)
    (s : F.obj (op ActionOpens.top)) :
    restrict F (ActionOpens.translate g U) (((sectionAction F).ρ g).hom s) =
      F.map (ActionOpens.translationIso g U).inv.op (restrict F U s) := by
  let i : U ⟶ ActionOpens.top := ActionOpens.inclusionHom le_top
  let j : ActionOpens.translate g U ⟶ ActionOpens.top :=
    ActionOpens.inclusionHom le_top
  have h : (ActionOpens.sectionArrow g).op ≫ j.op =
      i.op ≫ (ActionOpens.translationIso g U).inv.op := by
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    simp [i, j, ActionOpens.inclusionHom, ActionOpens.sectionArrow,
      ActionOpens.translationIso]
  have hf := congrArg F.map h
  rw [F.map_comp, F.map_comp] at hf
  exact congrArg
    (fun f : F.obj (op ActionOpens.top) ⟶
      F.obj (op (ActionOpens.translate g U)) => f.hom s) hf

/-- A zero germ transports to a zero germ at the translated point. -/
theorem germ_action_zero (g : G) (s : F.obj (op ActionOpens.top)) (x : X)
    (hx : (ordinary F).Γgerm (g⁻¹ • x) s = 0) :
    (ordinary F).Γgerm x (((sectionAction F).ρ g).hom s) = 0 := by
  obtain ⟨U, hxU, hU⟩ := (germ_zero_iff F s _).1 hx
  apply (germ_zero_iff F _ x).2
  refine ⟨ActionOpens.translate g U, hxU, ?_⟩
  rw [restrict_action, hU, map_zero]

/-- The support of a transported section lies in the translated support. -/
theorem support_action_subset (g : G) (s : F.obj (op ActionOpens.top)) :
    Langlands.Sheaf.CompactSupport.support (ordinary F) (((sectionAction F).ρ g).hom s) ⊆
      (fun x : X => g • x) '' Langlands.Sheaf.CompactSupport.support (ordinary F) s := by
  intro x hx
  refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
  intro hz
  exact hx (germ_action_zero F g s x hz)

/-- Every group operator preserves the actual compact-support submodule. -/
theorem preserves_compactSupport (g : G) (s : F.obj (op ActionOpens.top))
    (hs : IsCompact (Langlands.Sheaf.CompactSupport.support (ordinary F) s)) :
    IsCompact (Langlands.Sheaf.CompactSupport.support (ordinary F)
      (((sectionAction F).ρ g).hom s)) :=
  (hs.image (continuous_const_smul g)).of_isClosed_subset
    (Langlands.Sheaf.CompactSupport.isClosed_support _ _) (support_action_subset F g s)

/-- The ordinary global representation before imposing compact support. -/
abbrev globalRepresentation : Representation R G (F.obj (op ActionOpens.top)) :=
  ((Rep.ActionToRep R G).obj (sectionAction F)).ρ

/-- Support is exactly translated by the group operator. -/
theorem support_action (g : G) (s : F.obj (op ActionOpens.top)) :
    Langlands.Sheaf.CompactSupport.support (ordinary F) (globalRepresentation F g s) =
      (fun x : X => g • x) '' Langlands.Sheaf.CompactSupport.support (ordinary F) s := by
  apply Set.Subset.antisymm (support_action_subset F g s)
  rintro x ⟨y, hy, rfl⟩ hz
  have h := germ_action_zero F g⁻¹ (globalRepresentation F g s) y
    (by rw [inv_inv]; exact hz)
  change (ordinary F).Γgerm y
    (globalRepresentation F g⁻¹ (globalRepresentation F g s)) = 0 at h
  rw [Representation.inv_self_apply] at h
  exact hy h

set_option backward.isDefEq.respectTransparency false in
/-- Compactly supported sections with their constructed group representation. -/
def representation :
    Representation R G (Langlands.Sheaf.CompactSupport.submodule (ordinary F)) where
  toFun g := (globalRepresentation F g).restrict (preserves_compactSupport F g)
  map_one' := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change globalRepresentation F 1 s.val = s.val
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change globalRepresentation F (g * h) s.val =
      globalRepresentation F g (globalRepresentation F h s.val)
    simp [map_mul, Module.End.mul_apply]

variable {F}

/-- Every equivariant sheaf map restricts to an intertwiner on compact sections. -/
def map {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (f : F ⟶ F') :
    (representation F.obj).IntertwiningMap (representation F'.obj) where
  toLinearMap :=
    Langlands.Sheaf.CompactSupport.map
      ((underlyingPresheaf G X (ModuleCat.{u} R)).map f.hom)
  isIntertwining' g := by
    ext s
    exact congrArg
      (fun k : F.obj.obj (op ActionOpens.top) ⟶
        F'.obj.obj (op ActionOpens.top) => k.hom s.val)
      (f.hom.naturality (ActionOpens.sectionArrow g).op)

variable (R G X)

/-- Compactly supported sections form a functor to the actual representation category. -/
def functor : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G where
  obj F := Rep.of (representation F.obj)
  map f := Rep.ofHom (map f)
  map_id F := by
    ext s
    rfl
  map_comp f g := by
    ext s
    rfl

/-- Forget compact support by a natural equivariant injection into global sections. -/
def inclusion : functor R G X ⟶ sectionRepresentation R G X where
  app F := Rep.ofHom
    { toLinearMap := (Langlands.Sheaf.CompactSupport.submodule (ordinary F.obj)).subtype
      isIntertwining' _ := rfl }
  naturality _ _ f := by
    ext s
    rfl

end CompactSections

end Langlands.Sheaf.Equivariant
