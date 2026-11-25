/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.NormalizedGenericDataCore

/-!
# Normalized generic data retaining the residue-field square

Source: Stacks Project, Tag 09Z6, generic trivialization and normalization.
(blueprint: new-normalized-generic-data-with-factorization).
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Normalized generic data with its finite residue-field factorization.
Source: Stacks Project, Tag 09Z6, normalization and generic trivialization.
(blueprint: new-normalized-generic-data-with-factorization).
The construction pulls back to the residue field, trivializes after a finite
separable extension, and normalizes that extension over the reduced closure. -/
theorem exists_constructible_module_normalized_generic_data_with_factorization
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X), IsIntegralHom ν ∧
      ∃ (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
        (M : ModuleCat.{u + 1} Λ), Finite M ∧
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
        Nonempty
          ((upperStar (ModuleCat.{u + 1} Λ) g).obj
            ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
           (upperStar (ModuleCat.{u + 1} Λ) g).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
        ∃ a : Algebra (X.residueField x) K,
          @Module.Finite (X.residueField x) K _ _ a.toModule ∧
          Spec.map (CommRingCat.ofHom (@algebraMap (X.residueField x) K _ _ a)) ≫
            X.fromSpecResidueField x = g ≫ ν := by
  let G := (upperStar (ModuleCat.{u + 1} Λ) (X.fromSpecResidueField x)).obj F
  let : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  let : Scheme.IsConstructibleSheaf G :=
    Scheme.IsConstructibleSheaf.upperStar (X.fromSpecResidueField x) F
  have hG : Scheme.IsConstructibleEtaleModuleSheaf G :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr inferInstance
  obtain ⟨K, hK, hAlg, hfin, _, M, hM, ⟨e⟩⟩ :=
    constructible_field_finite_separable_constant (X.residueField x) Λ G hG
  let := hK
  let := hAlg
  let := hfin
  obtain ⟨_, _, Y, ν, g, hν, hcomp, hY, hnormal, η, hη, hgη, hres⟩ :=
    normalization_in_finite_residue_field_extension X x K
  let := hY
  have hunit := isIso_unit_constantSheaf_of_generic_residueFieldIso Λ Y
    (fun y ↦ (hnormal y).2) K g η hη hgη hres M
  refine ⟨Y, ν, hν, K, hK, g, M, hM, hunit, ⟨?_⟩, hAlg, hfin, hcomp⟩
  exact ((upperStarComp (ModuleCat.{u + 1} Λ) g ν).app F).symm ≪≫
    eqToIso (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} Λ) f).obj F) hcomp.symm) ≪≫
    (upperStarComp (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)))
      (X.fromSpecResidueField x)).app F ≪≫ e ≪≫
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M).symm
end AlgebraicGeometry.Etale
