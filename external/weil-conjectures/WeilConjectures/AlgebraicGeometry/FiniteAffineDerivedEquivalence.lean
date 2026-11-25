/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionIsos
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Derived quasi-coherent equivalence for an affine morphism

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.5.4, Tag 0AVW
(blueprint: lem-sc-finite-affine-derived-equivalence).
-/

@[expose] public section

universe v wX wY wA

open CategoryTheory

namespace AlgebraicGeometry

private lemma finite_affine_moduleDirectImage_restrictScalars_eq
    {X Y : Scheme.{v}} (f : X ⟶ Y) :
    RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f) ⋙
      SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f))
        ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ =
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom := rfl

/-- An affine morphism gives an equivalence with quasi-coherent derived modules over
its direct-image algebra. Its functor is induced by `Rg_*` for the canonical morphism
`g : (X, O_X) → (Y, f_* O_X)`. Restricting scalars recovers `Rf_*`.
Source: Stacks Project, Tag 0AVW
(blueprint: lem-sc-finite-affine-derived-equivalence).

Proof:
1. The affine module correspondence (`lem-weil-pbc-affine-module-correspondence`)
   identifies quasi-coherent modules on X with quasi-coherent direct-image-algebra modules.
2. On affine stalks g is a localization map, hence flat. Its pullback is exact, and
   cohomology of its derived pullback is pullback of cohomology. The ringed-space derived
   adjunction (`lem-pc-ringed-spaces-derived-adjoint-general`) gives Lg-star left adjoint
   to Rg-star. First use Step 4 to identify scalar restriction of Rg-star with Rf-star.
   The affine cohomology formula (`lem-sc-affine-derived-cohomology`) then shows Rg-star
   has quasi-coherent cohomology over the direct-image algebra.
3. Lg-star also preserves quasi-coherent cohomology. Its underived functor agrees with
   the affine correspondence's two tensor operations by tensor associativity. Exactness
   identifies the cohomology maps of the derived unit and counit with the affine
   correspondence's beta and alpha, which are isomorphisms. Thus the restricted functors
   give mutually inverse equivalences.
4. Scalar restriction is exact: the underlying sheaves, kernels and cokernels are
   unchanged. Choose a K-injective representative I of K. Rg-star and Rf-star are the
   same complex f-star I with different scalar structures
   (`def-pc-ringed-spaces-derived-direct-image`, `lemma-coherent-base-change-invertible-sheaves`).
   Hence scalar restriction of the equivalence is naturally isomorphic to Rf-star. -/
theorem finite_affine_derived_equivalence {X Y : Scheme.{v}} (f : X ⟶ Y)
    [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ E : schemeDerivedQCohCategory X ≌ directImageAlgebraDerivedQCohCategory f,
      Nonempty (E.functor ⋙ (directImageAlgebraDerivedQCohProperty f).ι ≅
        (schemeDerivedQCohProperty X).ι ⋙
          RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)) ∧
      ∃ S : directImageAlgebraDerivedQCohCategory f ⥤ schemeDerivedQCohCategory Y,
        Nonempty (S ⋙ (schemeDerivedQCohProperty Y).ι ≅
          (directImageAlgebraDerivedQCohProperty f).ι ⋙
            (SheafOfModules.restrictScalars
              (R := moduleRings Y.toRingedSpace)
              (R' := moduleRings (directImageAlgebraSpace f))
              ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor) ∧
        Nonempty (E.functor ⋙ S ⋙ (schemeDerivedQCohProperty Y).ι ≅
          (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) := by
  classical
  let pX := schemeDerivedQCohProperty X
  let pA := directImageAlgebraDerivedQCohProperty f
  let R := RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  have : Limits.PreservesFiniteLimits T :=
    @sheafAlgebraRestrictScalars_preservesFiniteLimits.{v, wY, wA} Y
      (Under.mk (show Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf from ⟨f.c⟩))
      inferInstance (by
        change HasDerivedCategory.{wA}
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))
        infer_instance)
  have : Limits.PreservesFiniteColimits T :=
    @sheafAlgebraRestrictScalars_preservesFiniteColimits.{v, wY, wA} Y
      (Under.mk (show Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf from ⟨f.c⟩))
      inferInstance (by
        change HasDerivedCategory.{wA}
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))
        infer_instance)
  have hT : ∀ M, pA M → schemeDerivedQCohProperty Y (T.rightDerivedFunctor.obj M) := by
    intro M hM n
    let e := (T.rightDerivedFunctorHomologyFunctorIso n).app M
    have hq := ((Scheme.Modules.affine_module_correspondence f).1 _).mp (hM n)
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso e hq
  have underived : RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f) ⋙ T ≅
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom :=
    eqToIso (finite_affine_moduleDirectImage_restrictScalars_eq f)
  let comparison : R ⋙ T.rightDerivedFunctor ≅ schemeDerivedDirectImage f :=
    Functor.isoWhiskerLeft R T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) T).symm ≪≫
      Functor.rightDerivedFunctorNatIso underived
  have hR : ∀ K, pX K → pA (R.obj K) := by
    intro K hK n
    obtain ⟨⟨e⟩, hq⟩ := schemeHigherDirectImage_of_affine f K hK n
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) n
    let c : T.obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj (R.obj K)) ≅
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K) :=
      (T.rightDerivedFunctorHomologyFunctorIso n).app (R.obj K) ≪≫
      H.mapIso (comparison.app K) ≪≫ e
    apply ((Scheme.Modules.affine_module_correspondence f).1 _).mpr
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso c.symm hq
  obtain ⟨P, hP, hmap, hadd, L, ε, hderived, hflat, ⟨adj⟩⟩ :=
    RingedSpace.derivedModulePullback_adjunction (toDirectImageAlgebraSpace f)
  have hL := affine_algebra_derived_pullback_preserves_qcoh f L adj
  obtain ⟨hunit, hcounit⟩ := affine_algebra_derived_adjunction_isos f L adj
  let LR := pX.lift (pA.ι ⋙ L) (fun M ↦ hL M.obj M.property)
  let RR := pA.lift (pX.ι ⋙ R) (fun K ↦ hR K.obj K.property)
  let adjQ : LR ⊣ RR := adj.restrictFullyFaithful pA.fullyFaithfulι pX.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  have : ∀ M, IsIso (adjQ.unit.app M) := by
    intro M
    have h : IsIso (pA.ι.map (adjQ.unit.app M)) := by
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      have := hunit M.obj M.property
      dsimp
      infer_instance
    exact isIso_of_reflects_iso (adjQ.unit.app M) pA.ι
  have : ∀ K, IsIso (adjQ.counit.app K) := by
    intro K
    have h : IsIso (pX.ι.map (adjQ.counit.app K)) := by
      rw [Adjunction.map_restrictFullyFaithful_counit_app]
      change IsIso (𝟙 (L.obj (R.obj K.obj)) ≫
        L.map (𝟙 (R.obj K.obj)) ≫ adj.counit.app K.obj)
      have := hcounit K.obj K.property
      infer_instance
    exact isIso_of_reflects_iso (adjQ.counit.app K) pX.ι
  let E := adjQ.toEquivalence.symm
  let S := (schemeDerivedQCohProperty Y).lift (pA.ι ⋙ T.rightDerivedFunctor)
    (fun M ↦ hT M.obj M.property)
  refine ⟨E, ⟨pA.liftCompιIso _ _⟩, S,
    ⟨(schemeDerivedQCohProperty Y).liftCompιIso _ _⟩, ?_⟩
  exact ⟨Functor.isoWhiskerLeft pX.ι comparison⟩

end AlgebraicGeometry
