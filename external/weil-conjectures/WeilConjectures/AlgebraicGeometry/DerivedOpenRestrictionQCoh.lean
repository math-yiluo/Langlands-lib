/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Quasi-coherence and derived restriction

Source: Stacks Project, Tags 08DW and 06Z0; exact restriction to open subschemes.
(blueprint: lem-pc-derived-open-restriction-qcoh-iff).
-/

@[expose] public section

universe u w wO

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem overEquiv_functor_qcoh (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) [M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  have : ∀ W, (Over.post (X := W) U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over W)
      (((Opens.grothendieckTopology X).over U).over _) := fun W =>
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.symm.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.symm.functor) _
    (U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))
private theorem overEquiv_inverse_qcoh (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) [M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  have : ∀ W, (Over.post (X := W) U.overEquivalence.symm.inverse).IsContinuous
      (((Opens.grothendieckTopology X).over U).over W)
      ((Opens.grothendieckTopology ↥U).over _) := fun W =>
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.symm.inverse _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.symm.inverse) _
    (U.sheafOfModulesEquivOverInverseUnit (moduleRings X.toRingedSpace))

/-- Exact restriction detects quasi-coherence of the restricted cohomology sheaves.
Source: Stacks Project, Tag 08DW, proof of (1), and Tag 06Z0.
Proof: represent K by a cochain complex. Restriction and the over equivalence are exact,
so their homology is the restriction of its homology. Descend this comparison through Q.
The over equivalence and its inverse preserve colimits and the structure module, hence
transport local presentations in both directions. Thus a cohomology sheaf over U is
quasi-coherent precisely when the corresponding sheaf on the open subscheme is.
Apply this in each integer degree. Empty opens and unbounded complexes are allowed.
(blueprint: lem-pc-derived-open-restriction-qcoh-iff). -/
theorem schemeDerivedQCoh_openRestriction_iff (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    schemeDerivedQCohProperty U.toScheme
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj K) ↔
      ∀ n : ℤ, (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).over U).IsQuasicoherent := by
  classical
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have comparison (n : ℤ) :
      (DerivedCategory.homologyFunctor _ n).obj (F.mapDerivedCategory.obj K) ≅
        F.obj ((DerivedCategory.homologyFunctor _ n).obj K) :=
    (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) n).app P ≪≫
      F.mapIso ((DerivedCategory.homologyFunctorFactors _ n).symm.app P ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso e)
  constructor
  · intro h n
    have hF := (SheafOfModules.isQuasicoherent
      (moduleRings U.toScheme.toRingedSpace)).prop_of_iso (comparison n) (h n)
    have := hF
    have hInv := overEquiv_inverse_qcoh X U
      (F.obj ((DerivedCategory.homologyFunctor _ n).obj K))
    exact (SheafOfModules.isQuasicoherent
      ((moduleRings X.toRingedSpace).over U)).prop_of_iso
      ((Scheme.Modules.overEquiv U).unitIso.symm.app _) hInv
  · intro h n
    have := h n
    have hF := overEquiv_functor_qcoh X U
      (((DerivedCategory.homologyFunctor _ n).obj K).over U)
    exact (SheafOfModules.isQuasicoherent
      (moduleRings U.toScheme.toRingedSpace)).prop_of_iso (comparison n).symm hF

end AlgebraicGeometry
