/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ConstantInternalModuleSheafEncoding.ConstantInternalModuleSheafEquivalenceSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonCoefficients

/-! # Specified finite coefficient realization and generator predicates

Source: blueprint finite comparison, coefficient paragraph
(blueprint: lem-ctf-finite-comparison-coefficients).

The constructions are kept separately so their coefficient-presentation lemmas can be
used by the localizing proof without a cyclic import.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject
namespace AlgebraicGeometry.ProEtale

private noncomputable def finiteComparisonPresheafEncodingIso
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    finiteComparisonPresheaf X B ⋙
        ConstantInternalModuleSheafEncoding.modulePresheafEncoding
          (C := X.ProEt) (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) ≅
      𝟭 (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) := by
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext m; rfl)
  · intro U V f
    ext m
    rfl
  · intro F G f
    ext U m
    rfl

private theorem finiteComparisonConstantRealization_isEquivalence
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    (finiteComparisonConstantRealization X B).IsEquivalence := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let A := ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) R
  let G := internalToModule R
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R G rfl
  let L := finiteComparisonConstantRealization X B
  let E := sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙ finiteComparisonPresheaf X B
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := X.ProEt) R G
  let adj := (sheafificationAdjunction J Ab.{u + 1}).mapModAdjunction A
  have hu (M : Sheaf J (ModuleCat.{u + 1} R)) : IsIso (adj.unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (Mod.forget A)]
    change IsIso ((adj.unit.app (E.obj M)).hom)
    rw [Adjunction.mapModAdjunction_unit_app_hom]
    exact isIso_toSheafify J
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj M).property
  let η := Functor.whiskerRight (Functor.whiskerLeft E adj.unit) P
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Functor.map_isIso P (adj.unit.app (E.obj M))
  let e0 : E ⋙ P ≅ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    Functor.isoWhiskerLeft _ (finiteComparisonPresheafEncodingIso X B)
  let e : (L ⋙ H) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) ≅
      (𝟭 _) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    (asIso η).symm ≪≫ e0
  let i := ((fullyFaithfulSheafToPresheaf J (ModuleCat.{u + 1} R)).whiskeringRight _)
    |>.preimageIso e
  have : (L ⋙ H).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  exact Functor.isEquivalence_of_comp_right L H

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

end AlgebraicGeometry.ProEtale
