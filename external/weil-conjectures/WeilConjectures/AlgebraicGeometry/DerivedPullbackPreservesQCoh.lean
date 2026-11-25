/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackModuleModel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Affine-local cohomology of derived pullback

Source: Stacks Project, Tag 08DW, part (1), with its affine calculation in part (2).
(blueprint: lem-pc-derived-pullback-qcoh-component).
-/

@[expose] public section

universe uX wD

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Affine-local cohomology calculation for derived pullback.
Source: Stacks Project, Tag 08DW(1), proof using Tag 08DW(2) and Tag 06Z0.
Proof: restrict E to V using exact restriction and quasi-coherence of its cohomology.
On the affine morphism U → V, choose a K-flat module representative on the canonical
spectrum of V. The affine model comparison represents its pullback by tilde of its
base-changed complex on the spectrum of U, followed by exact restriction to U.
The affine derived equivalence puts the tilde complex in the quasi-coherent derived
subcategory. Exact restriction commutes with homology and preserves quasi-coherence.
Transfer through the affine model and the derived open-restriction comparison, then
use the over equivalence to obtain the claimed cohomology over-object.
Empty opens, arbitrary degrees, unbounded complexes and nonflat f are included.
(blueprint: lem-pc-derived-pullback-qcoh-component). -/
theorem derivedPullback_cohomology_over_affine {X Y : Scheme.{uX}} (f : X ⟶ Y)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E)
    (n : ℤ) (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    (((DerivedCategory.homologyFunctor
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj
        ((derivedPullback f).obj E)).over U).IsQuasicoherent := by
  set_option synthInstance.maxSize 2048 in
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        let : HasDerivedCategory (SheafOfModules.{uX}
            (moduleRings U.toScheme.toRingedSpace)) := HasDerivedCategory.standard _
        let : HasDerivedCategory (SheafOfModules.{uX}
            (moduleRings V.toScheme.toRingedSpace)) := HasDerivedCategory.standard _
        have hV' := (schemeDerivedQCoh_openRestriction_iff Y V E).2
          (fun i => by
            have := hE i
            exact SheafOfModules.isQuasicoherent_over ((DerivedCategory.homologyFunctor
              (SheafOfModules.{uX} (moduleRings Y.toRingedSpace)) i).obj E) V)
        have : IsAffine U.toScheme := hU
        have : IsAffine V.toScheme := hV
        let : HasDerivedCategory (SheafOfModules.{uX}
            (moduleRings (Spec Γ(U.toScheme, ⊤)).toRingedSpace)) := HasDerivedCategory.standard _
        let : HasDerivedCategory (ModuleCat.{uX} Γ(U.toScheme, ⊤)) :=
          HasDerivedCategory.standard _
        obtain ⟨P, _, _, ⟨model⟩⟩ := exists_affine_derivedPullback_module_model
          (f.resLE V U hUV) _ hV'
        let M := ((ModuleCat.extendScalars (f.resLE V U hUV).appTop.hom).mapHomologicalComplex
          (.up ℤ)).obj P
        obtain ⟨a, ⟨tildeIso⟩, _⟩ := exists_affineQCohDerivedEquivalence_core Γ(U.toScheme, ⊤)
        let T := (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{uX} Γ(U.toScheme, ⊤) ⥤
            SheafOfModules.{uX} (moduleRings (Spec Γ(U.toScheme, ⊤)).toRingedSpace))
            (tilde.functor Γ(U.toScheme, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M
        let R : SheafOfModules.{uX} (moduleRings (Spec Γ(U.toScheme, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace) :=
          Scheme.Modules.restrictFunctor U.toScheme.toSpecΓ
        have : R.Additive := by
          change (Scheme.Modules.restrictFunctor U.toScheme.toSpecΓ).Additive
          infer_instance
        have : Limits.PreservesFiniteLimits R := by
          change Limits.PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.toScheme.toSpecΓ)
          infer_instance
        have : Limits.PreservesFiniteColimits R := by
          change Limits.PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.toScheme.toSpecΓ)
          infer_instance
        have hT (i : ℤ) :=
          (SheafOfModules.isQuasicoherent
            (moduleRings (Spec Γ(U.toScheme, ⊤)).toRingedSpace)).prop_of_iso
            ((DerivedCategory.homologyFunctor _ i).mapIso (tildeIso.app M))
            ((a.functor.obj (DerivedCategory.Q.obj M)).property i)
        have hModel (i : ℤ) :=
          (DerivedCategory.homologyFunctor _ i).mapIso (R.mapDerivedCategoryFactors.app T) ≪≫
            (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
            (R.mapHomologicalComplexHomologyIso (.up ℤ) i).app T ≪≫
            R.mapIso ((DerivedCategory.homologyFunctorFactors _ i).symm.app T)
        have hAffine (i : ℤ) := by
          have : ((DerivedCategory.homologyFunctor
            (SheafOfModules.{uX} (moduleRings (Spec Γ(U.toScheme, ⊤)).toRingedSpace)) i).obj
              (DerivedCategory.Q.obj T)).IsQuasicoherent := hT i
          exact (SheafOfModules.isQuasicoherent
            (moduleRings U.toScheme.toRingedSpace)).prop_of_iso
            ((hModel i).symm ≪≫ ((DerivedCategory.homologyFunctor _ i).mapIso model).symm)
            (@Scheme.Modules.isQuasicoherent_restrictFunctor _ _
              U.toScheme.toSpecΓ inferInstance _ this)
        obtain ⟨e⟩ := derivedPullback_openRestriction_iso_universes f U V hUV
        have hRestricted (i : ℤ) :=
          (SheafOfModules.isQuasicoherent (moduleRings U.toScheme.toRingedSpace)).prop_of_iso
            ((DerivedCategory.homologyFunctor _ i).mapIso (e.app E).symm) (hAffine i)
        exact (schemeDerivedQCoh_openRestriction_iff X U _).1 hRestricted n

end AlgebraicGeometry
