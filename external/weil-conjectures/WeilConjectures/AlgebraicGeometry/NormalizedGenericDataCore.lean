/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.ConstructibleSheaf.FinitePushforward
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Transport the canonical generic-stalk unit along the source-field isomorphism.
The residue-field square makes the generic stalk map invertible; the composition-unit
identity then transfers the normal generic constant theorem (Stacks Project, Tag 09Z5). -/
private theorem isIso_unit_constantSheaf_of_generic_residueFieldIso
    (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u}) [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ Y) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hgη : g (IsLocalRing.closedPoint K) = η)
    (hres : IsIso (g.residueFieldMap (IsLocalRing.closedPoint K)))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have hg : g (IsLocalRing.closedPoint K) = genericPoint Y :=
    hgη.trans (hη.eq (genericPoint_spec Y))
  let : Field ((Spec (.of K)).presheaf.stalk (IsLocalRing.closedPoint K)) :=
    ((stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField K)).toField
  have hyres : IsIso (Y.residue (g (IsLocalRing.closedPoint K))) := by
    rw [hg]
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨RingHom.injective _, Y.residue_surjective _⟩
  have hkres : IsIso ((Spec (.of K)).residue (IsLocalRing.closedPoint K)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨RingHom.injective _, (Spec (.of K)).residue_surjective _⟩
  let := hyres
  let := hkres
  let := hres
  have hstalk : IsIso (g.stalkMap (IsLocalRing.closedPoint K)) := by
    have h := Scheme.residue_residueFieldMap g (IsLocalRing.closedPoint K)
    have : IsIso (g.stalkMap (IsLocalRing.closedPoint K) ≫
        (Spec (.of K)).residue (IsLocalRing.closedPoint K)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((Spec (.of K)).residue _)
  let := hstalk
  let φ := Scheme.stalkClosedPointTo g
  have : IsIso φ := by
    dsimp [φ, Scheme.stalkClosedPointTo]
    infer_instance
  let e := Spec.map φ
  have : IsIso e := by dsimp [e]; infer_instance
  have hcomp : e ≫ Y.fromSpecStalk (g (IsLocalRing.closedPoint K)) = g :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  have hu : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Y.fromSpecStalk (g (IsLocalRing.closedPoint K)))).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
    rw [hg]
    exact (isIso_unit_constantSheaf_of_isIntegrallyClosed Λ hY M).1
  let := hu
  have hh := upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) e
    (Y.fromSpecStalk (g (IsLocalRing.closedPoint K)))
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) g hcomp.symm
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) e
          (Y.fromSpecStalk (g (IsLocalRing.closedPoint K))) g hcomp.symm).hom.app
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
    rw [hh]
    rw [Adjunction.comp_unit_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) e
        (Y.fromSpecStalk (g (IsLocalRing.closedPoint K))) g hcomp.symm).hom.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))

/-- Core normalized generic data, omitting the geometric lifting clause.
Source: Stacks Project, Tag 09Z6, normalization and generic trivialization.
(blueprint: new-normalized-generic-data-core).
The construction pulls back to the residue field, trivializes after a finite
separable extension, and normalizes that extension over the reduced closure. -/
theorem exists_constructible_module_normalized_generic_data_core
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
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
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
  refine ⟨Y, ν, hν, K, hK, g, M, hM, hunit, ⟨?_⟩⟩
  exact ((upperStarComp (ModuleCat.{u + 1} Λ) g ν).app F).symm ≪≫
    eqToIso (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} Λ) f).obj F) hcomp.symm) ≪≫
    (upperStarComp (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)))
      (X.fromSpecResidueField x)).app F ≪≫ e ≪≫
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M).symm
end AlgebraicGeometry.Etale
