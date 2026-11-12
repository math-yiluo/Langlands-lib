import Langlands.Cohomology.EquivariantDerivedSections
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # The constant equivariant sheaf adjunction -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

/-- A representation gives a constant transport presheaf, with inverse label action. -/
def constantTransport : Rep.{u} R G ⥤ (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M :=
    { obj _ := ModuleCat.of R M
      map f := ModuleCat.ofHom (M.ρ f.unop.label⁻¹)
      map_id _ := by
        ext m
        change M.ρ (1 : G)⁻¹ m = m
        simp
      map_comp f g := by
        ext m
        change M.ρ (f.unop.label * g.unop.label)⁻¹ m =
          M.ρ g.unop.label⁻¹ (M.ρ f.unop.label⁻¹ m)
        simp [mul_inv_rev, map_mul, Module.End.mul_apply] }
  map a :=
    { app _ := ModuleCat.ofHom a.hom.toLinearMap
      naturality _ _ f := by
        ext m
        exact Rep.hom_comm_apply a f.unop.label⁻¹ m }

/-- Global sections on transport presheaves, retaining their representation. -/
def transportSections : ((ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) ⥤ Rep.{u} R G :=
  { obj F := (Rep.ActionToRep R G).obj (sectionAction F)
    map a := (Rep.ActionToRep R G).map
      { hom := a.app (op ActionOpens.top)
        comm g := a.naturality (ActionOpens.sectionArrow g).op } }

/-- Restrict a global module map to every open. -/
def constantTransportLift (M : Rep.{u} R G)
    (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (a : M ⟶ (transportSections R G X).obj F) :
    (constantTransport R G X).obj M ⟶ F where
  app U := ModuleCat.ofHom a.hom.toLinearMap ≫
    F.map (ActionOpens.inclusionHom (show U.unop.openSet ≤ ⊤ from le_top)).op
  naturality U V f := by
    let iU : U.unop ⟶ ActionOpens.top := ActionOpens.inclusionHom le_top
    let iV : V.unop ⟶ ActionOpens.top := ActionOpens.inclusionHom le_top
    have h : iV ≫ ActionOpens.sectionArrow f.unop.label⁻¹ = f.unop ≫ iU := by
      apply ActionOpens.Hom.ext
      simp [iU, iV, ActionOpens.inclusionHom, ActionOpens.sectionArrow]
    have ha : ModuleCat.ofHom (M.ρ f.unop.label⁻¹) ≫
        ModuleCat.ofHom a.hom.toLinearMap =
      ModuleCat.ofHom a.hom.toLinearMap ≫
        F.map (ActionOpens.sectionArrow f.unop.label⁻¹).op := by
      ext m
      exact Rep.hom_comm_apply a f.unop.label⁻¹ m
    change ModuleCat.ofHom (M.ρ f.unop.label⁻¹) ≫
      (ModuleCat.ofHom a.hom.toLinearMap ≫ F.map iV.op) =
        (ModuleCat.ofHom a.hom.toLinearMap ≫ F.map iU.op) ≫ F.map f
    rw [← Category.assoc, ha, Category.assoc, ← F.map_comp,
      ← op_comp, h, op_comp, F.map_comp, Category.assoc]
    rfl

/-- Maps out of the constant transport presheaf are equivariant global module maps. -/
def constantTransportHomEquiv (M : Rep.{u} R G)
    (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    ((constantTransport R G X).obj M ⟶ F) ≃
      (M ⟶ (transportSections R G X).obj F) where
  toFun a := Rep.ofHom
    { toLinearMap := (a.app (op ActionOpens.top)).hom
      isIntertwining' g := by
        ext m
        simpa [constantTransport, ActionOpens.sectionArrow, sectionAction,
          Rep.ActionToRep] using
          ConcreteCategory.congr_hom (a.naturality (ActionOpens.sectionArrow g).op) m }
  invFun := constantTransportLift R G X M F
  left_inv a := by
    apply NatTrans.ext
    funext U
    change ModuleCat.ofHom (a.app (op ActionOpens.top)).hom ≫
      F.map (ActionOpens.inclusionHom le_top).op = a.app U
    have h := a.naturality (ActionOpens.inclusionHom
      (show U.unop.openSet ≤ ⊤ from le_top)).op
    dsimp [constantTransport] at h
    have hi : ModuleCat.ofHom (M.ρ (1 : G)⁻¹) =
        𝟙 (ModuleCat.of R M) := by ext m; simp
    dsimp [ActionOpens.inclusionHom] at h
    erw [hi, Category.id_comp] at h
    exact h.symm
  right_inv a := by
    ext m
    have h : ActionOpens.inclusionHom (show (⊤ : TopologicalSpace.Opens X) ≤ ⊤ from le_top) =
        𝟙 (ActionOpens.top (G := G) (X := X)) := by
      apply ActionOpens.Hom.ext
      rfl
    have hh : F.map (ActionOpens.inclusionHom
        (show (⊤ : TopologicalSpace.Opens X) ≤ ⊤ from le_top)).op =
        𝟙 (F.obj (op ActionOpens.top)) := by
      erw [h, op_id, F.map_id]
      rfl
    exact ConcreteCategory.congr_hom hh (a.hom m)

/-- The constant transport presheaf is left adjoint to equivariant global sections. -/
def constantTransportAdjunction :
    constantTransport R G X ⊣ transportSections R G X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantTransportHomEquiv R G X
      homEquiv_naturality_left_symm := by
        intro M N F a b
        ext U m
        rfl
      homEquiv_naturality_right := by
        intro M F F' a b
        ext m
        rfl }

instance constantTransport_preservesMonomorphisms :
    (constantTransport R G X).PreservesMonomorphisms where
  preserves {M N} a _ := by
    have : ∀ U, Mono (((constantTransport R G X).map a).app U) := fun U => by
      change Mono ((forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).map a)
      infer_instance
    exact NatTrans.mono_of_mono_app _

/-- Sheafification of the constant transport presheaf. -/
def constantEquivariantSheaf : Rep.{u} R G ⥤ TopologicalSheaf G X (ModuleCat.{u} R) :=
  constantTransport R G X ⋙
    presheafToSheaf (transportTopology G X) (ModuleCat.{u} R) ⋙
      (sheafEquivalence G X (ModuleCat.{u} R)).inverse

/-- Global sections of a transport sheaf recover the published section representation. -/
def transportSectionsIso :
    (sheafEquivalence G X (ModuleCat.{u} R)).functor ⋙
      sheafToPresheaf (transportTopology G X) (ModuleCat.{u} R) ⋙
        transportSections R G X ≅ sectionRepresentation R G X :=
  Iso.refl _

/-- Constant equivariant sheaves are left adjoint to the section representation. -/
def constantEquivariantSheafAdjunction :
    constantEquivariantSheaf R G X ⊣ sectionRepresentation R G X :=
  ((constantTransportAdjunction R G X).comp
    ((sheafificationAdjunction (transportTopology G X) (ModuleCat.{u} R)).comp
      (sheafEquivalence G X (ModuleCat.{u} R)).symm.toAdjunction)).ofNatIsoRight
        (transportSectionsIso R G X)

instance constantEquivariantSheaf_preservesMonomorphisms :
    (constantEquivariantSheaf R G X).PreservesMonomorphisms := by
  dsimp [constantEquivariantSheaf]
  infer_instance

/-- Global sections send injective equivariant sheaves to injective representations. -/
instance sectionRepresentation_preservesInjectiveObjects :
    (sectionRepresentation R G X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (constantEquivariantSheafAdjunction R G X)

end Langlands.Cohomology.EquivariantComposite
