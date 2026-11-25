/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- Derived affine tilde and derived global sections admit an adjunction on
quasi-coherent derived objects, with the two defining functor comparisons.
Source: Stacks Project, Tag 06Z0, elucidation of the two adjoint functors;
Tag 079W supplies derived adjunction.
(blueprint: new-affine-qcoh-derived-adjunction-construction).

Proof: View Spec A as a ringed space over the one-point ringed space A.
The pullback is associated sheaf and is exact, since localization of modules
is exact. Apply it termwise to complexes; its cohomology is associated sheaf
of module cohomology, hence quasi-coherent. Localize this complex functor to
obtain F and its comparison. The right adjoint is derived global sections,
computed on K-injective resolutions, with scalars transported through ΓSpecIso.
The ordinary tilde/global-sections adjunction induces the derived adjunction.
Its restriction has the same hom-equivalence because the quasi-coherent
subcategory is full; this gives F ⊣ G and the comparison for G. -/
theorem affineQCohDerivedAdjunction_construction (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    ∃ (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
      (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A)),
      Nonempty (F ⊣ G) ∧
      Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) ∧
      Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor) := by
  let L : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  let R := RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom
  let : L.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  have adj : L ⊣ R := tilde.adjunction
  let : L.IsLeftAdjoint := adj.isLeftAdjoint
  let : Limits.PreservesFiniteColimits L := inferInstance
  let : L.PreservesMonomorphisms := ⟨by
    intro M N f hf
    let : Mono f := hf
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  let : L.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels L
  let : Limits.PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesHomology
  let P := schemeDerivedQCohProperty (Spec (.of A))
  have hL : ∀ K, P (L.mapDerivedCategory.obj K) := by
    intro K n
    let e := (L.mapDerivedCategoryHomologyFunctorIso n).app K
    apply (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso e
    change (tilde (R := .of A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)).IsQuasicoherent
    infer_instance
  let F := P.lift L.mapDerivedCategory hL
  let G := P.ι ⋙ R.rightDerivedFunctor
  let dadj := adj.mapDerivedCategoryRightDerivedAdjunction
  refine ⟨F, G, ?_, ?_, ⟨Iso.refl _⟩⟩
  · exact ⟨dadj.restrictFullyFaithful (Functor.FullyFaithful.id _) P.fullyFaithfulι
      ((Functor.leftUnitor _) ≪≫ (P.liftCompιIso _ hL).symm)
      (Functor.rightUnitor _).symm⟩
  · exact ⟨L.mapDerivedCategoryFactors⟩

end AlgebraicGeometry
