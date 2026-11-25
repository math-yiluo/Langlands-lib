/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Comparing basic-open sections with sections of the restricted scheme

Source: Stacks Project, Tags 08D2 and 08BS; restriction of scalars for section modules.
(blueprint: lem-sc-principal-open-sections-restriction-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def sectionsForgetIso (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    affineOpenSections A U ⋙ forget₂ (ModuleCat A) AddCommGrpCat ≅
    SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
      (Scheme.Modules.overEquiv U).functor ⋙
      RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
      forget₂ (ModuleCat ((moduleRings U.toScheme.toRingedSpace).obj.obj (.op ⊤)))
        AddCommGrpCat := by
  let V := (U.overEquivalence.inverse.obj ⊤).left
  have hU : U = V := by
    ext x
    simp [V, TopologicalSpace.Opens.overEquivalence]
  refine NatIso.ofComponents
    (fun M ↦ M.val.presheaf.mapIso (eqToIso (congrArg Opposite.op hU))) ?_
  intro M N f
  ext x
  exact (PresheafOfModules.naturality_apply f.val
    (eqToHom (congrArg Opposite.op hU)) x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Basic-open sections detect the same quasi-isomorphisms as global sections after
restriction to the open subscheme. No quasi-coherence or resolution is assumed.
Source: Stacks Project, Tags 08D2 and 08BS, sections on an open subscheme.
(blueprint: lem-sc-principal-open-sections-restriction-comparison).

Proof: Put U = D(g). Restriction to the localized site followed by the canonical
module equivalence overEquiv U is ordinary open-subscheme restriction. Its global
sections on U are the original module's sections on U, with scalars in O(U).
The canonical ring map A to O(U) restricts this action to the action used by
modulesSpecToSheaf and hence by affineOpenSections. The identifications are
natural in sheaf-module morphisms, and therefore identify both section complexes
and the map induced by i after restriction of scalars. Restriction of scalars is
exact: it leaves the underlying additive group, kernels, images and quotients
unchanged. Thus it preserves and reflects homology isomorphisms in every degree.
For an empty basic open all these section modules are zero. -/
theorem principalOpenSections_restriction_quasiIso_iff
    (A : Type u) [CommRing A] (g : A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (i : F ⟶ J) :
    let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen g
    let R := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    QuasiIso (((affineOpenSections A U).mapHomologicalComplex (ComplexShape.up ℤ)).map i) ↔
      QuasiIso (((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
         (ComplexShape.up ℤ)).map
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map i)) := by
  dsimp only
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen g
  let R := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
    (Scheme.Modules.overEquiv U).functor
  let Γ := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let V := forget₂ (ModuleCat A) AddCommGrpCat
  let W := forget₂ (ModuleCat ((moduleRings U.toScheme.toRingedSpace).obj.obj (.op ⊤)))
    AddCommGrpCat
  have : R.Additive := by
    constructor
    intro M N f h
    rfl
  have : Γ.Additive := RingedSpace.globalSectionsFunctor_additive _
  have : W.Additive := inferInstanceAs (forget₂ _ AddCommGrpCat).Additive
  let e₀ : affineOpenSections A U ⋙ V ≅ R ⋙ Γ ⋙ W := sectionsForgetIso A U
  let c := ComplexShape.up ℤ
  let eL := Functor.mapHomologicalComplexCompIso
    (Iso.refl (affineOpenSections A U ⋙ V)) c
  let eR₁ := Functor.mapHomologicalComplexCompIso (Iso.refl (Γ ⋙ W)) c
  let eR₂ := Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ Γ ⋙ W)) c
  let e := eL ≪≫ NatIso.mapHomologicalComplex e₀ c ≪≫ eR₂.symm ≪≫
    (Functor.isoWhiskerLeft (R.mapHomologicalComplex c) eR₁).symm
  have h := quasiIso_iff_of_arrow_mk_iso
    ((V.mapHomologicalComplex c).map
      (((affineOpenSections A U).mapHomologicalComplex c).map i))
    ((W.mapHomologicalComplex c).map ((Γ.mapHomologicalComplex c).map
      ((R.mapHomologicalComplex c).map i)))
    (Arrow.isoMk (e.app F) (e.app J) (e.hom.naturality i).symm)
  rw [HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((affineOpenSections A U).mapHomologicalComplex (ComplexShape.up ℤ)).map i) V,
    HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map i)) W] at h
  exact h

end AlgebraicGeometry
