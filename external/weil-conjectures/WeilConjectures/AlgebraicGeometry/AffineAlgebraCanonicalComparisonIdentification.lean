/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility

import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCycleClassEpi
import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveBoundaryExactness

/-! # Identification of the canonical affine cohomology comparison

Source: Stacks Project, Tags 0AVW and 08D4.
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_of_preserved_left_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (P : D ⥤ C) [P.Additive]
    [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ F) (I : CochainComplex C ℤ) (n : ℤ)
    [F.PreservesLeftHomologyOf (I.sc n)] :
    ∃ e : ((F.mapHomologicalComplex (.up ℤ)).obj I).homology n ≅ F.obj (I.homology n),
      e.hom = a.homEquiv _ _
        ((P.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n) := by
  let S := I.sc n
  let h := S.homologyData.left
  let e := S.mapHomologyIso F
  let ψ : ShortComplex.LeftHomologyMapData (S.mapNatTrans a.counit)
      ((h.map F).map P) h :=
    { φK := a.counit.app h.K
      φH := a.counit.app h.H
      commi := (a.counit.naturality h.i).symm
      commf' := by simp
      commπ := by exact a.counit.naturality h.π }
  have hhid : h.homologyIso = Iso.refl S.homology := by
    ext
    dsimp [h, ShortComplex.LeftHomologyData.homologyIso,
      ShortComplex.leftHomologyIso, ShortComplex.LeftHomologyData.leftHomologyIso,
      ShortComplex.leftHomologyMapIso']
    simp only [← ShortComplex.leftHomologyMap'_comp, Category.comp_id,
      ShortComplex.leftHomologyMap'_id]
    rfl
  have hfac := ψ.homologyMap_eq
  dsimp only [ψ] at hfac
  rw [hhid] at hfac
  simp only [Iso.refl_inv] at hfac
  refine ⟨e, ?_⟩
  apply (a.homEquiv _ _).symm.injective
  erw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply]
  change P.map e.hom ≫ a.counit.app (I.homology n) = _
  have hc : HomologicalComplex.homologyMap
      ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n =
      (P.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        P.map e.hom ≫ a.counit.app (I.homology n) := by
    have hsc : ShortComplex.homologyMap (S.mapNatTrans a.counit) =
        ((S.map F).mapHomologyIso P).hom ≫ P.map e.hom ≫ a.counit.app S.homology := by
      rw [(h.map F).mapHomologyIso_eq P]
      simpa [e, h, ShortComplex.mapHomologyIso, ShortComplex.homology] using hfac
    simpa [Functor.mapHomologicalComplexHomologyIso,
      Functor.mapHomologicalComplexCompShortComplexFunctorIso,
      HomologicalComplex.homologyFunctorIso, ShortComplex.homologyFunctorIso,
      HomologicalComplex.homologyMap, Adjunction.mapHomologicalComplex, S,
      ShortComplex.homologyFunctor, HomologicalComplex.homology,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      ShortComplex.mapNatTrans, HomologicalComplex.sc,
      Functor.mapHomologicalComplex, ShortComplex.map,
      Functor.mapShortComplex] using hsc
  rw [hc]
  simp

/-- The affine K-injective cohomology comparison witness can be chosen to be the
canonical comparison used by the counit construction.
Source: Stacks Project, Tag 0AVW, proof of affine-morphism-equivalence; Tag 08D4.
(blueprint: new-affine-algebra-canonical-comparison-identification).

Proof: The affine sections calculation identifies the edge morphism on every affine
open with the map sending a cycle section to its cohomology class. The resulting
maps are natural in restrictions and linear over the direct-image algebra, so they
assemble to the canonical morphism in `affineAlgebraCounitHomologyComparison`.
The unbounded truncation argument of Tag 08D4 proves this edge morphism invertible
in every integer degree. The equality follows by extensionality on affine opens.
-/
theorem affine_algebra_kinjective_canonical_comparison_identification
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ∃ e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n),
      e.hom = affineAlgebraCounitHomologyComparison f P a I n := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let S := I.sc n
  let h := S.homologyData.left
  have : Limits.PreservesLimitsOfSize.{0, 0} F := a.rightAdjoint_preservesLimits
  have : Limits.PreservesFiniteLimits F := inferInstance
  have hepi : Epi (F.map h.π) := affine_algebra_kinjective_cycle_class_epi f I hI n
  let B := (ShortComplex.mk h.f' h.π h.f'_π).map F
  have : Epi B.g := hepi
  have hex : B.Exact := affine_algebra_kinjective_boundary_exactness f I hI n
  have hpres : h.IsPreservedBy F :=
    { g := inferInstance
      f' := by
        apply Limits.preservesColimit_of_preserves_colimit_cocone h.hπ
        exact (Limits.isColimitMapCoconeCoforkEquiv' F h.wπ).symm hex.gIsCokernel }
  let := hpres
  let := Functor.PreservesLeftHomologyOf.mk' F h
  exact comparison_of_preserved_left_homology F P a I n

end AlgebraicGeometry
