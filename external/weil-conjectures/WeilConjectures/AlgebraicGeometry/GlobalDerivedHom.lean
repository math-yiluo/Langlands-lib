/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Topology.PointModuleEvaluationEquivalence

/-!
# Global derived Hom on a scheme

Source: Stacks Project, Cohomology of Sheaves, Section 20.44, Tag 0B6A
(blueprint: def-pc-global-derived-rhom).

The structure sheaf on the one-point space is the pushforward of O_X: its value on
that point is A = O_X(X), and on the empty open it is the zero ring. The map of
structure sheaves is the identity. Modules on the point are A-modules, by an
equivalence whose functor is evaluation on the point. Derived global sections is the
right derived functor of Γ(X,-) valued in A-modules; it agrees with Rp_* followed by
that equivalence. Global derived Hom is its composite with the shared internal Hom.

## Main definitions and statements

* `globalSectionsPoint`, `toGlobalSectionsPoint`: the point ringed space and p.
* `schemeDerivedGlobalSections`: unbounded RΓ, with its point and resolution comparisons.
* `schemeGlobalDerivedHom`: RΓ composed with derived internal Hom.
-/

@[expose] public section

universe u w wA wPt

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

-- The functor of an equivalence of preadditive categories preserves binary products,
-- hence is additive; `mapDerivedCategory` of it needs this (found with
-- `synthInstance.maxSize 2048`).
attribute [local instance] Functor.additive_of_preserves_binary_products

namespace AlgebraicGeometry

/-- The one-point ringed space with structure ring O_X(X), constructed by pushing O_X
along the unique continuous map to the point. Source: Stacks, Tag 0B6A
(blueprint: def-pc-global-derived-rhom). -/
def globalSectionsPoint (X : Scheme.{u}) : RingedSpace.{u} where
  carrier := TopCat.of PUnit.{u + 1}
  presheaf := (TopCat.Presheaf.pushforward CommRingCat
    (TopCat.ofHom (ContinuousMap.const X.carrier PUnit.unit))).obj X.presheaf
  IsSheaf := TopCat.Sheaf.pushforward_sheaf_of_sheaf _ X.IsSheaf

/-- The ringed-space morphism p to (pt, O_X(X)); p-sharp is the identity, in particular
on the whole space. Source: Stacks, Tag 0B6A
(blueprint: def-pc-global-derived-rhom). -/
def toGlobalSectionsPoint (X : Scheme.{u}) : X.toRingedSpace ⟶ globalSectionsPoint X :=
  ⟨{ base := TopCat.ofHom (ContinuousMap.const X.carrier PUnit.unit), c := 𝟙 _ }⟩

/-- RΓ(X,-) valued in D(O_X(X)): the unbounded right derived functor of global sections
`Γ(X,-) : Mod(O_X) ⥤ Mod(O_X(X))`. Source: Stacks, Tag 0B6A
(blueprint: def-pc-global-derived-rhom). -/
def schemeDerivedGlobalSections (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    schemeDerivedCategory X ⥤
      DerivedCategory (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor

set_option synthInstance.maxSize 2048 in
/-- RΓ(X,-) is Rp_* to (pt, O_X(X)) followed by the identification of modules on the point
with O_X(X)-modules: there is an equivalence of module categories whose functor is
evaluation on the point, and Rp_* followed by it is RΓ(X,-).
Source: Stacks, Tag 0B6A (blueprint: def-pc-global-derived-rhom).
Proof:
1. An A-module M gives the sheaf on the point with M on the whole point and zero on
   the empty open; the sheaf condition forces every module sheaf to be zero on the
   empty open, so evaluation and this construction are mutually inverse, including on
   morphisms. The pushforward structure ring on the whole point is Γ(X,O_X).
2. By def-pc-ringed-spaces-derived-direct-image, Rp_* is computed by p_* of a
   K-injective resolution, naturally in the complex.
3. An equivalence is exact, so its derived-category map is termwise application.
4. Since p-sharp is the identity, p_* followed by evaluation is Γ(X,-), including
   its A-action. These natural comparisons descend through localization. -/
theorem schemeDerivedGlobalSections_point_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wPt} (SheafOfModules.{u} (moduleRings (globalSectionsPoint X)))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    ∃ e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)),
      Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)) ∧
      Nonempty (RingedSpace.derivedModuleDirectImage (toGlobalSectionsPoint X) ⋙
        e.functor.mapDerivedCategory ≅ schemeDerivedGlobalSections X) := by
  let G : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ⥤
      ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
    RingedSpace.globalSectionsFunctor (globalSectionsPoint X)
  let : Unique (globalSectionsPoint X) := inferInstanceAs (Unique PUnit.{u + 1})
  have : G.IsEquivalence :=
    RingedSpace.globalSectionsFunctor_isEquivalence_of_unique (globalSectionsPoint X)
  let e := G.asEquivalence
  refine ⟨e, ⟨Iso.refl _⟩, ?_⟩
  let F := RingedSpace.moduleDirectImage (toGlobalSectionsPoint X)
  have h : F ⋙ G ≅ RingedSpace.globalSectionsFunctor X.toRingedSpace :=
    NatIso.ofComponents (fun M ↦
      { hom := ModuleCat.ofHom LinearMap.id
        inv := ModuleCat.ofHom LinearMap.id }) (by intros; rfl)
  exact ⟨(F.rightDerivedFunctorCompMapDerivedCategoryIso G).symm ≪≫
    Functor.rightDerivedFunctorNatIso h⟩

/-- Any K-injective resolution K → I computes RΓ(X,K) by Γ(X,I).
Source: Stacks, Tag 0B6A (blueprint: def-pc-global-derived-rhom).
Proof: `schemeDerivedGlobalSections` is the right derived functor of Γ(X,-), and the
right derived functor is computed on K-injective complexes by termwise application
(`Functor.rightDerivedFunctorObjQIso`). Since K → I is a quasi-isomorphism,
Q(K) ≅ Q(I); compose. -/
theorem schemeDerivedGlobalSections_computed_by_resolution (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    {K I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (s : K ⟶ I) [QuasiIso s] [I.IsKInjective] :
    Nonempty ((schemeDerivedGlobalSections X).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) := by
  exact ⟨(schemeDerivedGlobalSections X).mapIso (asIso (DerivedCategory.Q.map s)) ≪≫
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorObjQIso I⟩


/-- Global derived Hom: RΓ(X,R𝓗om(P,Q)) in D(O_X(X)), contravariant in P and
covariant in Q, encoded as a functor from D(O_X)ᵒᵖ × D(O_X).
Source: Stacks, Tag 0B6A (blueprint: def-pc-global-derived-rhom). -/
def schemeGlobalDerivedHom (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    (schemeDerivedCategory X)ᵒᵖ × schemeDerivedCategory X ⥤
      DerivedCategory (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
  derivedInternalHom (Opens.grothendieckTopology X) X.sheaf ⋙
    schemeDerivedGlobalSections X

end AlgebraicGeometry
