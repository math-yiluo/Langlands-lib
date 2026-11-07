import Langlands.Shimura.Coefficients.HarrisLatticeLevelInclusion
import Langlands.Shimura.LevelColimit
import Langlands.CategoryTheory.EquivariantDiagram

/-! # Canonical Harris lattices and reductions over all ordered compact levels -/

noncomputable section

universe u

open CategoryTheory Opposite

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CompactOpenLevel

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The original level subgroups and their actual inclusions over the existing ordered levels. -/
def orderedSubgroupFunctor : Ordered G ⥤ GrpCat.{u} where
  obj U := GrpCat.of U.subgroup
  map f := GrpCat.ofHom (Subgroup.inclusion (leOfHom f))
  map_id _ := by ext g; rfl
  map_comp _ _ := by ext g; rfl

@[simp] theorem orderedSubgroupFunctor_obj (U : Ordered G) :
    (orderedSubgroupFunctor G).obj U = GrpCat.of U.subgroup := rfl

@[simp] theorem orderedSubgroupFunctor_map {U V : Ordered G} (f : U ⟶ V) :
    ((orderedSubgroupFunctor G).map f).hom = Subgroup.inclusion (leOfHom f) := rfl

end Langlands.Shimura.CompactOpenLevel

namespace Langlands.Shimura.Coefficients

open Langlands.Global AdelicFunctoriality AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
  {L : Type u} [Field L] [NumberField L]
  {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
  {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
  (p : FinitePlace ℚ)

local notation "R" => HarrisCoefficientIntegers L p
local notation "Levels" => CompactOpenLevel.Ordered σ.FiniteAdelicPoints
local notation "groups" => CompactOpenLevel.orderedSubgroupFunctor σ.FiniteAdelicPoints

/-- The actual canonical full lattices form a covariant diagram under level inclusion. -/
def harrisLatticeLevelFunctor : Levels ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (harrisLattice ρ p U)
  map {U V} f := ModuleCat.ofHom (harrisLatticeInclusion ρ p V U (leOfHom f))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem harrisLatticeLevelFunctor_obj (U : Levels) :
    (harrisLatticeLevelFunctor ρ p).obj U = ModuleCat.of R (harrisLattice ρ p U) := rfl

/-- The level arrow is the already constructed ambient inclusion, with the same vector. -/
@[simp] theorem harrisLatticeLevelFunctor_map {U V : Levels} (f : U ⟶ V) :
    (harrisLatticeLevelFunctor ρ p).map f =
      ModuleCat.ofHom (harrisLatticeInclusion ρ p V U (leOfHom f)) := rfl

/-- Keep the original action of every level subgroup on its independently constructed lattice. -/
def harrisLatticeLevelDiagram : EquivariantDiagram groups (ModuleCat.{u} R) where
  obj := harrisLatticeLevelFunctor ρ p
  ρ U := (harrisLatticeAction ρ p U).ρ
  comm {U V} f g := (harrisLatticeActionInclusion ρ p V U (leOfHom f)).comm g

/-- The original full reductions form an equivariant diagram at every exponent. -/
def harrisTorsionLevelDiagram (m : ℕ) (k : ℕᵒᵖ) :
    EquivariantDiagram groups (ModuleCat.{u} R) where
  obj := harrisLatticeLevelFunctor ρ p ⋙
    Langlands.Coefficients.AdicSystem.powerReduction (harrisCoefficientScalarIdeal L p m) k.unop
  ρ U := ((harrisTorsionSystem ρ p U m).obj k).ρ
  comm {U V} f g := ((harrisTorsionSystemInclusion ρ p V U (leOfHom f) m).app k).comm g

/-- The actual original level inclusions are compatible with the entire exponent inverse system. -/
def harrisTorsionLevelSystem (m : ℕ) :
    ℕᵒᵖ ⥤ EquivariantDiagram groups (ModuleCat.{u} R) where
  obj k := harrisTorsionLevelDiagram ρ p m k
  map f :=
    { hom :=
        { app U := ((harrisTorsionSystem ρ p U m).map f).hom
          naturality {U V} h := by
            have hnat := congrArg Action.Hom.hom
              ((harrisTorsionSystemInclusion ρ p V U (leOfHom h) m).naturality f)
            exact hnat.symm }
      comm U g := ((harrisTorsionSystem ρ p U m).map f).comm g }
  map_id k := by
    apply EquivariantDiagram.Hom.ext
    apply NatTrans.ext
    funext U
    exact congrArg Action.Hom.hom ((harrisTorsionSystem ρ p U m).map_id k)
  map_comp f g := by
    apply EquivariantDiagram.Hom.ext
    apply NatTrans.ext
    funext U
    exact congrArg Action.Hom.hom ((harrisTorsionSystem ρ p U m).map_comp f g)

/-- Every vertex is the original coefficient module, without a replacement lattice. -/
@[simp] theorem harrisTorsionLevelSystem_obj_obj (m : ℕ) (k : ℕᵒᵖ) (U : Levels) :
    ((harrisTorsionLevelSystem ρ p m).obj k).obj.obj U =
      ((harrisTorsionSystem ρ p U m).obj k).V := rfl

/-- The level morphisms are precisely the original reduced inclusion maps. -/
@[simp] theorem harrisTorsionLevelSystem_level_map (m : ℕ) (k : ℕᵒᵖ)
    {U V : Levels} (f : U ⟶ V) :
    ((harrisTorsionLevelSystem ρ p m).obj k).obj.map f =
      ((harrisTorsionSystemInclusion ρ p V U (leOfHom f) m).app k).hom := rfl

/-- The actions are exactly the original coefficient actions of the actual level subgroups. -/
@[simp] theorem harrisTorsionLevelSystem_action (m : ℕ) (k : ℕᵒᵖ)
    (U : Levels) (g : U.subgroup) :
    ((harrisTorsionLevelSystem ρ p m).obj k).ρ U g =
      ((harrisTorsionSystem ρ p U m).obj k).ρ g := rfl

/-- The exponent morphisms are precisely the original coefficient reductions. -/
@[simp] theorem harrisTorsionLevelSystem_exponent_map (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) (U : Levels) :
    ((harrisTorsionLevelSystem ρ p m).map f).hom.app U =
      ((harrisTorsionSystem ρ p U m).map f).hom := rfl

/-- Level inclusions and original coefficient reductions commute simultaneously. -/
@[reassoc] theorem harrisTorsionLevelSystem_square (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) {U V : Levels} (h : U ⟶ V) :
    ((harrisTorsionLevelSystem ρ p m).obj i).obj.map h ≫
        ((harrisTorsionSystem ρ p V m).map f).hom =
      ((harrisTorsionSystem ρ p U m).map f).hom ≫
        ((harrisTorsionLevelSystem ρ p m).obj j).obj.map h :=
  ((harrisTorsionLevelSystem ρ p m).map f).hom.naturality h

/-- At every exponent, the original inclusion map sends a class to the same ambient vector. -/
@[simp] theorem harrisTorsionLevelSystem_level_map_mk (m : ℕ) (k : ℕᵒᵖ)
    {U V : Levels} (f : U ⟶ V) (x : harrisLattice ρ p U) :
    (((harrisTorsionLevelSystem ρ p m).obj k).obj.map f).hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeInclusion ρ p V U (leOfHom f) x) := rfl

/-- The actual reduced inclusions compose under any two successive level refinements. -/
@[reassoc] theorem harrisTorsionSystemInclusion_comp (m : ℕ) (k : ℕᵒᵖ)
    (U V T : CompactOpenLevel σ.FiniteAdelicPoints)
    (hVU : V.subgroup ≤ U.subgroup) (hTV : T.subgroup ≤ V.subgroup) :
    ((harrisTorsionSystemInclusion ρ p V T hTV m).app k).hom ≫
        ((harrisTorsionSystemInclusion ρ p U V hVU m).app k).hom =
      ((harrisTorsionSystemInclusion ρ p U T (hTV.trans hVU) m).app k).hom := by
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The reduced inclusion at an unchanged level is the actual identity. -/
@[simp] theorem harrisTorsionSystemInclusion_refl (m : ℕ) (k : ℕᵒᵖ)
    (U : CompactOpenLevel σ.FiniteAdelicPoints) :
    ((harrisTorsionSystemInclusion ρ p U U le_rfl m).app k).hom =
      𝟙 ((harrisTorsionSystem ρ p U m).obj k).V := by
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Langlands.Shimura.Coefficients
