import Langlands.Shimura.Coefficients.HarrisLatticeLevelSystem
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientLatticeComparison
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelIndex

/-! # Original CM coefficient actions over ordered small levels and all exponents -/

noncomputable section

open CategoryTheory Opposite

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.Global Langlands.Shimura.Coefficients

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n) [Module.Finite ℚ A]

local notation "G" => D.rationalInvolution.FiniteAdelicPoints
local notation "Levels" => OrderedSmallCMLevel D
local notation "small" U:arg => (orderedSmallCMLevelToSmallCMLevel D).obj U

/-- The actual ordinary coefficient level at each original ordered CM level. -/
def cmHarrisOrdinaryLevelFunctor : Levels ⥤ CompactOpenLevel.Ordered G where
  obj U := CompactOpenLevel.inverseOpposite U.val
  map f := homOfLE (CompactOpenLevel.inverseOpposite_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem cmHarrisOrdinaryLevelFunctor_obj (U : Levels) :
    (cmHarrisOrdinaryLevelFunctor D).obj U = CompactOpenLevel.inverseOpposite U.val := rfl

/-- The original opposite CM subgroups and their same-element inclusions. -/
def cmHarrisOrderedGroups : Levels ⥤ GrpCat :=
  orderedSmallCMLevelForget D ⋙ CompactOpenLevel.orderedSubgroupFunctor Gᵐᵒᵖ

/-- The original inverse-unop group equivalences are natural in every CM level inclusion. -/
def cmHarrisOrderedGroupIso : cmHarrisOrderedGroups D ≅
    cmHarrisOrdinaryLevelFunctor D ⋙ CompactOpenLevel.orderedSubgroupFunctor G :=
  NatIso.ofComponents (fun U => (CompactOpenLevel.inverseOppositeEquiv U.val).toGrpIso)
    (fun f => by ext g; rfl)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The natural group isomorphism has exactly the existing inverse-unop component. -/
@[simp] theorem cmHarrisOrderedGroupIso_hom_app (U : Levels) :
    (((cmHarrisOrderedGroupIso D).hom.app U).hom) =
      (CompactOpenLevel.inverseOppositeEquiv U.val).toMonoidHom := rfl

variable {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ)

local notation "R" => HarrisCoefficientIntegers K p
local notation "ordinary" U:arg => CompactOpenLevel.inverseOpposite (U).val

/-- Reindex the actual generic coefficients and retain the original CM level action. -/
def cmHarrisCoefficientLevelDiagram (m : ℕ) (k : ℕᵒᵖ) :
    EquivariantDiagram (cmHarrisOrderedGroups D) (ModuleCat R) where
  obj := cmHarrisOrdinaryLevelFunctor D ⋙ ((harrisTorsionLevelSystem ρ p m).obj k).obj
  ρ U := ((cmHarrisTorsionSystem D ρ p (small U) m).obj k).ρ
  comm {U V} f g :=
    ((cmHarrisTorsionSystemInclusion D ρ p (small V) (small U) (leOfHom f) m).app k).comm g

/-- All original CM coefficient reductions are natural over all ordered small levels. -/
def cmHarrisCoefficientLevelSystem (m : ℕ) :
    ℕᵒᵖ ⥤ EquivariantDiagram (cmHarrisOrderedGroups D) (ModuleCat R) where
  obj k := cmHarrisCoefficientLevelDiagram D ρ p m k
  map f :=
    { hom :=
        { app U := ((cmHarrisTorsionSystem D ρ p (small U) m).map f).hom
          naturality {U V} h := by
            have hnat := congrArg Action.Hom.hom
              ((cmHarrisTorsionSystemInclusion D ρ p (small V) (small U)
                (leOfHom h) m).naturality f)
            exact hnat.symm }
      comm U g := ((cmHarrisTorsionSystem D ρ p (small U) m).map f).comm g }
  map_id k := by
    apply EquivariantDiagram.Hom.ext
    apply NatTrans.ext
    funext U
    exact congrArg Action.Hom.hom ((cmHarrisTorsionSystem D ρ p (small U) m).map_id k)
  map_comp f g := by
    apply EquivariantDiagram.Hom.ext
    apply NatTrans.ext
    funext U
    exact congrArg Action.Hom.hom ((cmHarrisTorsionSystem D ρ p (small U) m).map_comp f g)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The full underlying level diagram is the exact generic diagram on the ordinary levels. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_obj_forget (m : ℕ) (k : ℕᵒᵖ) :
    ((cmHarrisCoefficientLevelSystem D ρ p m).obj k).obj =
      cmHarrisOrdinaryLevelFunctor D ⋙ ((harrisTorsionLevelSystem ρ p m).obj k).obj := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The coefficient at each vertex is the original CM coefficient, with no new lattice choice. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_obj_obj (m : ℕ) (k : ℕᵒᵖ) (U : Levels) :
    ((cmHarrisCoefficientLevelSystem D ρ p m).obj k).obj.obj U =
      ((cmHarrisTorsionSystem D ρ p (small U) m).obj k).V := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Every level arrow uses exactly the existing actual CM lattice inclusion reduction. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_level_map (m : ℕ) (k : ℕᵒᵖ)
    {U V : Levels} (f : U ⟶ V) :
    ((cmHarrisCoefficientLevelSystem D ρ p m).obj k).obj.map f =
      ((cmHarrisTorsionSystemInclusion D ρ p (small V) (small U) (leOfHom f) m).app k).hom := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Every exponent arrow is the unchanged original CM reduction. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_exponent_map (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) (U : Levels) :
    ((cmHarrisCoefficientLevelSystem D ρ p m).map f).hom.app U =
      ((cmHarrisTorsionSystem D ρ p (small U) m).map f).hom := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The action at every level is precisely the original inverse-unop action. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_action (m : ℕ) (k : ℕᵒᵖ)
    (U : Levels) (g : U.val.subgroup) :
    ((cmHarrisCoefficientLevelSystem D ρ p m).obj k).ρ U g =
      ((harrisTorsionSystem ρ p (ordinary U) m).obj k).ρ
        (CompactOpenLevel.inverseOppositeEquiv U.val g) := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- On actual lattice classes this is the original inverse-unop ambient operator. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_action_mk (m : ℕ) (k : ℕᵒᵖ)
    (U : Levels) (g : U.val.subgroup) (x : (harrisLatticeAction ρ p (ordinary U)).V) :
    (((cmHarrisCoefficientLevelSystem D ρ p m).obj k).ρ U g).hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((harrisLatticeAction ρ p (ordinary U)).ρ
        (CompactOpenLevel.inverseOppositeEquiv U.val g)).hom x) := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The included coefficient class keeps the same original ambient vector. -/
@[simp] theorem cmHarrisCoefficientLevelSystem_level_map_mk (m : ℕ) (k : ℕᵒᵖ)
    {U V : Levels} (f : U ⟶ V) (x : harrisLattice ρ p (ordinary U)) :
    (((cmHarrisCoefficientLevelSystem D ρ p m).obj k).obj.map f).hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeInclusion ρ p (ordinary V) (ordinary U)
        (CompactOpenLevel.inverseOpposite_mono (leOfHom f)) x) := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Original CM level inclusions and exponent reductions commute simultaneously. -/
@[reassoc] theorem cmHarrisCoefficientLevelSystem_square (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) {U V : Levels} (h : U ⟶ V) :
    ((cmHarrisCoefficientLevelSystem D ρ p m).obj i).obj.map h ≫
        ((cmHarrisTorsionSystem D ρ p (small V) m).map f).hom =
      ((cmHarrisTorsionSystem D ρ p (small U) m).map f).hom ≫
        ((cmHarrisCoefficientLevelSystem D ρ p m).obj j).obj.map h :=
  ((cmHarrisCoefficientLevelSystem D ρ p m).map f).hom.naturality h

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The named original CM reduced inclusions compose through every further small level. -/
@[reassoc] theorem cmHarrisTorsionSystemInclusion_comp (m : ℕ) (k : ℕᵒᵖ)
    (U V T : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
    (hTV : T.obj.subgroup ≤ V.obj.subgroup) :
    ((cmHarrisTorsionSystemInclusion D ρ p V T hTV m).app k).hom ≫
        ((cmHarrisTorsionSystemInclusion D ρ p U V hVU m).app k).hom =
      ((cmHarrisTorsionSystemInclusion D ρ p U T (hTV.trans hVU) m).app k).hom :=
  harrisTorsionSystemInclusion_comp ρ p m k
    (CompactOpenLevel.inverseOpposite U.obj) (CompactOpenLevel.inverseOpposite V.obj)
    (CompactOpenLevel.inverseOpposite T.obj)
    (CompactOpenLevel.inverseOpposite_mono hVU) (CompactOpenLevel.inverseOpposite_mono hTV)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- At an unchanged original CM level, the actual reduced inclusion is the identity. -/
@[simp] theorem cmHarrisTorsionSystemInclusion_refl (m : ℕ) (k : ℕᵒᵖ) (U : SmallCMLevel D) :
    ((cmHarrisTorsionSystemInclusion D ρ p U U le_rfl m).app k).hom =
      𝟙 ((cmHarrisTorsionSystem D ρ p U m).obj k).V :=
  harrisTorsionSystemInclusion_refl ρ p m k (CompactOpenLevel.inverseOpposite U.obj)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
