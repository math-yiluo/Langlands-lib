/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.AlgebraicGeometry.ModuleCupNaiveMap
public import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMonoidalNormalization
import WeilConjectures.Topology.PointModuleEvaluationEquivalence
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived

/-! # Transport of the ordinary global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
/-- Underived global pullback data and its tensor-counit normalization.
Source: Stacks Tags 008A, 008Y, 0FKU (blueprint: lem-sc-global-tensor-pullback-underived-data).
The proof transports the concrete ringed-space pullback adjunction along point evaluation,
then applies the separate monoidal normalization theorem for the tensor-counit identity. -/
theorem exists_globalTensorPullback_underived_data :
    ∃ (e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (_ : Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)))
      (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M)))
      (_ : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
            X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
              ⟨(toGlobalSectionsPoint X).hom.c⟩)
          (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M))
          (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
          eqToHom (h N).symm)
      (hadd : P.Additive) (mon : P.Monoidal)
      (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace),
      letI := hadd
      letI := mon
      letI := adj.isLeftAdjoint
      ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
        Functor.LaxMonoidal.μ P
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
          P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
        adj.counit.app M ⊗ₘ adj.counit.app N := by
  let G := RingedSpace.globalSectionsFunctor (globalSectionsPoint X)
  let : Unique (globalSectionsPoint X) := inferInstanceAs (Unique PUnit.{u + 1})
  have : G.IsEquivalence :=
    RingedSpace.globalSectionsFunctor_isEquivalence_of_unique (globalSectionsPoint X)
  let e := G.asEquivalence
  obtain ⟨T, hT, hmT, haddT, ⟨adjT⟩⟩ :=
    RingedSpace.exists_tensorModulePullback (toGlobalSectionsPoint X)
  let P := e.inverse ⋙ T
  let := haddT
  let : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have hadd : P.Additive := inferInstance
  let F := RingedSpace.moduleDirectImage (toGlobalSectionsPoint X)
  let rightIso : F ⋙ e.functor ≅ RingedSpace.globalSectionsFunctor X.toRingedSpace :=
    NatIso.ofComponents (fun M ↦
      { hom := ModuleCat.ofHom LinearMap.id
        inv := ModuleCat.ofHom LinearMap.id }) (by intros; rfl)
  let adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace :=
    (e.symm.toAdjunction.comp adjT).ofNatIsoRight rightIso
  have hP := fun M ↦ hT (e.inverse.obj M)
  have hmP : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (hP M) ≫
      SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M))
        (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
        eqToHom (hP N).symm := fun a ↦ hmT (e.inverse.map a)
  obtain ⟨mon, hcounit⟩ := globalTensorPullback_monoidal_normalization X
    e ⟨Iso.refl _⟩ P hP hmP adj
  exact ⟨e, ⟨Iso.refl _⟩, P, hP, hmP, hadd, mon, adj, hcounit⟩
end
end AlgebraicGeometry.Scheme.Modules
