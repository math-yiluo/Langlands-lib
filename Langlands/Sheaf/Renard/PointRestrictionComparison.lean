import Langlands.Sheaf.Renard.InverseImageStalks
import Langlands.Sheaf.Renard.SingletonSheaves
import Langlands.Sheaf.Renard.SmoothInverseImage
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Actual singleton restriction and the original fixed stalk
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions.PointRestrictionComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Langlands.Sheaf.Equivariant

/-- The singleton's whole open is terminal even in its opposite neighbourhood category. -/
def singletonNhdsTerminal :
    IsTerminal (op (⊤ : OpenNhds (X := TopCat.of PUnit) PUnit.unit)) := by
  refine IsTerminal.ofUniqueHom (fun (U : (OpenNhds (X := TopCat.of PUnit) PUnit.unit)ᵒᵖ) =>
    (homOfLE (show (⊤ : OpenNhds (X := TopCat.of PUnit) PUnit.unit) ≤ U.unop from
      fun y _ => by cases y; exact U.unop.property)).op) ?_
  intro U k
  apply Quiver.Hom.unop_inj
  rfl

instance globalGerm_isIso (F : (TopCat.of PUnit).Presheaf (ModuleCat.{0} ℂ)) :
    IsIso (F.Γgerm PUnit.unit) := by
  change IsIso (colimit.ι ((OpenNhds.inclusion
    (X := TopCat.of PUnit) PUnit.unit).op ⋙ F) (op ⊤))
  exact (colimit.isColimit _).isIso_ι_app_of_isTerminal _ singletonNhdsTerminal

variable {G : Type} [Group G] [TopologicalSpace G]

/-- Every original singleton global section belongs to the original compact submodule. -/
def allSectionsEquiv (F : ActionSheaf G PUnit) :
    Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj) ≃ₗ[ℂ]
      F.obj.obj (op ActionOpens.top) where
  toFun := Subtype.val
  invFun s := ⟨s, (Set.toFinite _).isCompact⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original compact global germ on the actual singleton is an isomorphism. -/
def compactGermIso (F : ActionSheaf G PUnit) :
    ModuleCat.of ℂ (Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj)) ≅
      (CompactSections.ordinary F.obj).stalk PUnit.unit :=
  (allSectionsEquiv F).toModuleIso ≪≫ asIso ((CompactSections.ordinary F.obj).Γgerm PUnit.unit)

/-- The singleton compact germ retains the original inverse-labelled stalk action. -/
theorem compactGermIso_action (F : ActionSheaf G PUnit) (g : G) :
    ModuleCat.ofHom (compactRepresentation F g) ≫ (compactGermIso F).hom =
      (compactGermIso F).hom ≫ Godement.stalkPull F.obj g⁻¹ PUnit.unit PUnit.unit rfl := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (congrArg (fun a => a.hom s.val)
    (Godement.germ_stalkPull_arrow F.obj
      (ActionOpens.sectionArrow g) PUnit.unit PUnit.unit rfl trivial)).symm

omit [TopologicalSpace G] in
/-- Original sheaf maps commute with the singleton compact germs. -/
theorem compactGermIso_naturality {F F' : ActionSheaf G PUnit} (k : F ⟶ F') :
    ModuleCat.ofHom (CompactSections.map k).toLinearMap ≫ (compactGermIso F').hom =
      (compactGermIso F).hom ≫
        (TopCat.Presheaf.stalkFunctor (X := TopCat.of PUnit) (ModuleCat.{0} ℂ) PUnit.unit).map
          ((underlyingPresheaf G PUnit (ModuleCat.{0} ℂ)).map k.hom) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (Langlands.Sheaf.CompactGerms.germ_naturality
    ((toSheaf G PUnit (ModuleCat.{0} ℂ)).map k) PUnit.unit s).symm

variable {Y : Type} [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
variable (Q : Subgroup G) (y : Y) (hfix : ∀ q : Q, (q : G) • y = y)

/-- The literal continuous singleton inclusion at the original point. -/
def pointMap : C(PUnit, Y) := ContinuousMap.const PUnit y

omit [TopologicalSpace G] [ContinuousSMul G Y] in
include hfix in
/-- The original stabilizer condition is exactly the singleton map's equivariance. -/
theorem pointMap_equivariant (q : Q) (z : PUnit) :
    pointMap y (q • z) = (q : G) • pointMap y z := (hfix q).symm

/-- The actual original-stalk comparison after subgroup and singleton inverse image. -/
def pointStalkIso (F : ActionSheaf G Y) :
    (CompactSections.ordinary F.obj).stalk y ≅
      (CompactSections.ordinary
        ((subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix)).obj F).obj).stalk
          PUnit.unit :=
  InverseImageStalks.stalkIso (pointMap y) (pointMap_equivariant Q y hfix)
    ((subgroupRestriction Q).obj F) PUnit.unit

/-- The point comparison commutes with the two original labelled stalk transports. -/
theorem pointStalkIso_action (F : ActionSheaf G Y) (q : Q) :
    (fixedStalkAction Q y hfix F).ρ q ≫ (pointStalkIso Q y hfix F).hom =
      (pointStalkIso Q y hfix F).hom ≫ Godement.stalkPull
        ((subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix)).obj F).obj
        q⁻¹ PUnit.unit PUnit.unit rfl :=
  InverseImageStalks.preimageStalkMap_transport
    (pointMap y) (pointMap_equivariant Q y hfix)
    (InverseImageStalks.unit (pointMap y) (pointMap_equivariant Q y hfix)
      ((subgroupRestriction Q).obj F)) q⁻¹ PUnit.unit PUnit.unit rfl

/-- The original inverse-image stalk comparison is natural after subgroup restriction. -/
theorem pointStalkIso_naturality {F F' : ActionSheaf G Y} (k : F ⟶ F') :
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of Y) (ModuleCat.{0} ℂ) y).map
        ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).map k.hom) ≫ (pointStalkIso Q y hfix F').hom =
      (pointStalkIso Q y hfix F).hom ≫
        (TopCat.Presheaf.stalkFunctor (X := TopCat.of PUnit) (ModuleCat.{0} ℂ) PUnit.unit).map
          ((underlyingPresheaf Q PUnit (ModuleCat.{0} ℂ)).map
            ((subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix)).map k).hom) :=
  InverseImageStalks.stalkMap_naturality (pointMap y) (pointMap_equivariant Q y hfix)
    ((subgroupRestriction Q).map k) PUnit.unit

/-- Singleton compact sections map to the literal original stalk. -/
def moduleIso (F : ActionSheaf G Y) :
    ModuleCat.of ℂ (Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary
      ((subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix)).obj F).obj)) ≅
        (CompactSections.ordinary F.obj).stalk y :=
  compactGermIso ((subgroupSpaceRestriction Q (pointMap y)
    (pointMap_equivariant Q y hfix)).obj F) ≪≫ (pointStalkIso Q y hfix F).symm

/-- The comparison is precisely the compact global germ followed by inverse image's inverse. -/
@[reassoc (attr := simp)]
theorem moduleIso_pointStalkIso (F : ActionSheaf G Y) :
    (moduleIso Q y hfix F).hom ≫ (pointStalkIso Q y hfix F).hom =
      (compactGermIso ((subgroupSpaceRestriction Q (pointMap y)
        (pointMap_equivariant Q y hfix)).obj F)).hom := by
  simp [moduleIso]

/-- The actual point comparison is natural on the original compact-section maps. -/
theorem moduleIso_naturality {F F' : ActionSheaf G Y} (k : F ⟶ F') :
    ModuleCat.ofHom (CompactSections.map
        ((subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix)).map k)).toLinearMap ≫
      (moduleIso Q y hfix F').hom =
    (moduleIso Q y hfix F).hom ≫
      (TopCat.Presheaf.stalkFunctor (X := TopCat.of Y) (ModuleCat.{0} ℂ) y).map
        ((underlyingPresheaf G Y (ModuleCat.{0} ℂ)).map k.hom) := by
  apply (cancel_mono (pointStalkIso Q y hfix F').hom).1
  rw [Category.assoc, moduleIso_pointStalkIso, Category.assoc, pointStalkIso_naturality,
    moduleIso_pointStalkIso_assoc]
  exact compactGermIso_naturality _

/-- The compact-section/stalk comparison respects exactly the original Q-actions. -/
def actionIso (F : ActionSheaf G Y) :
    (Rep.RepToAction ℂ Q).obj ((CompactSections.functor ℂ Q PUnit).obj
      ((subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix)).obj F)) ≅
        fixedStalkAction Q y hfix F :=
  Action.mkIso (moduleIso Q y hfix F) (fun q => by
    apply (cancel_mono (pointStalkIso Q y hfix F).hom).1
    rw [Category.assoc, moduleIso_pointStalkIso, Category.assoc, pointStalkIso_action,
      moduleIso_pointStalkIso_assoc]
    exact compactGermIso_action _ q)

/-- The natural comparison in the original action category. -/
def actionsIso :
    subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix) ⋙
        CompactSections.functor ℂ Q PUnit ⋙ Rep.RepToAction ℂ Q ≅
      fixedStalkActions Q y hfix :=
  NatIso.ofComponents (actionIso Q y hfix) (fun k => by
    apply Action.Hom.ext
    exact moduleIso_naturality Q y hfix k)

/-- Compact sections of actual singleton restriction are the original fixed-stalk representation. -/
def algebraicIso :
    subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix) ⋙
        CompactSections.functor ℂ Q PUnit ≅
      fixedStalkFunctor Q y hfix :=
  Functor.isoWhiskerLeft
      (subgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix) ⋙
        CompactSections.functor ℂ Q PUnit) (Rep.repIsoAction ℂ Q).unitIso ≪≫
    Functor.isoWhiskerRight (actionsIso Q y hfix) (Rep.ActionToRep ℂ Q)

variable [IsTopologicalGroup G]

/-- Renard's actual smooth point restriction has the original smooth stalk representation. -/
def smoothIso (hG : Langlands.Topology.IsLocallyProfinite G)
    (hQ : IsClosed (Q : Set G)) (hY : Langlands.Topology.IsLocallyProfinite Y) :
    smoothSubgroupSpaceRestriction Q (pointMap y) (pointMap_equivariant Q y hfix) hG hQ hY ⋙
        gammaC Q PUnit ≅ smoothFixedStalkFunctor Q y hfix hY :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk (Langlands.smoothRepProperty ℂ Q)
    ((algebraicIso Q y hfix).app F.obj)) (fun k => by
      apply ObjectProperty.hom_ext
      exact (algebraicIso Q y hfix).hom.naturality k.hom)

end Langlands.Sheaf.Renard.SectionActions.PointRestrictionComparison
