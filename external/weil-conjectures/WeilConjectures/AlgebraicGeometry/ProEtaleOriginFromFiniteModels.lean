/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import all WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-! # ProEtaleOriginFromFiniteModels

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def lowerStarRestrictionIso
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (V : X.Etale) (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (AlgebraicGeometry.Etale.localizationRestriction
      (ModuleCat.{u + 1} Λ) V.hom V.prop).obj
      ((AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) X).obj F) ≅
    (AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) V.left).obj
      ((AlgebraicGeometry.ProEtale.localizationRestriction
        (ModuleCat.{u + 1} Λ) V.hom inferInstance).obj F) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))

/-- Finite constant pro-étale models descend to a finite locally constant étale origin.
Source: Stacks Project, Tag 099Y, proof of `lemma-compare-locally-constant`.
The comparison lower star is locally constant on the finite model cover, and its
comparison counit is an isomorphism after restriction; these local inverses glue.
(auxiliary; not a blueprint node) -/
theorem etale_origin_of_finite_models
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) (g i)).obj F) ≅
            (constantSheaf (Scheme.ProEt.topology (W i))
              (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf G ∧
        Nonempty ((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} Λ) X).obj G ≅ F) := by
  classical
  obtain ⟨𝒰, hmodels⟩ := etale_cover_of_proetale_finite_models X Λ F hF
  let G := (AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) X).obj F
  have hvalues (i : 𝒰.I₀) : ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (G.over (𝒰.etalePrecoverageToEtale i) ≅
        (constantSheaf (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj M) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hmodels i
    let V := 𝒰.etalePrecoverageToEtale i
    let A := ModuleCat.{u + 1} Λ
    let E := (Etale.overSheafEquiv V A).functor
    let R := AlgebraicGeometry.ProEtale.comparisonLowerStar A V.left
    let T := (constantSheaf V.left.smallEtaleTopology A).obj M
    let eF : (AlgebraicGeometry.ProEtale.localizationRestriction
        A V.hom inferInstance).obj F ≅ (constantSheaf (ProEt.topology V.left) A).obj M :=
      ((AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
        A V.hom inferInstance).app F).symm ≪≫ e
    let eG : E.obj (G.over V) ≅ T :=
      overSheafEquivFunctorObjOverIso A V G ≪≫
      (AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction A V.hom V.prop).app G ≪≫
      lowerStarRestrictionIso X Λ V F ≪≫ R.mapIso eF ≪≫
      R.mapIso ((comparisonConstantIso V.left Λ).app M).symm ≪≫
      (asIso ((AlgebraicGeometry.ProEtale.comparisonAdjunction A V.left).unit.app T)).symm
    let c := ((Etale.overEquiv V).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over V) V.left.smallEtaleTopology A Over.mkIdTerminal).app M
    exact ⟨M, hM, ⟨E.preimageIso (eG ≪≫ c.symm)⟩⟩
  choose M hM eM using hvalues
  let d : LocallyConstantDatum G :=
    ⟨𝒰, fun i ↦ Sheaf.isConstant_of_iso _ (eM i).some⟩
  have hG : IsFiniteLocallyConstantSheaf G :=
    (finite_locally_constant_module_values_iff G).1.mp
      ⟨d, fun i ↦ ⟨M i, hM i, eM i⟩⟩
  have hcounit : IsIso
      ((AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app F) := by
    let A := ModuleCat.{u + 1} Λ
    have : ∀ i, WeaklyEtale (𝒰.f i) := fun i ↦ inferInstance
    apply AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction A
      ((AlgebraicGeometry.ProEtale.comparisonAdjunction A X).counit.app F)
      𝒰.f (etalePrecoverage_le_proetalePrecoverage _ 𝒰.mem₀)
    intro i
    obtain ⟨M, _, ⟨e⟩⟩ := hmodels i
    let V := 𝒰.etalePrecoverageToEtale i
    let eF : (AlgebraicGeometry.ProEtale.localizationRestriction
        A V.hom inferInstance).obj F ≅
        (AlgebraicGeometry.ProEtale.comparisonUpperStar A V.left).obj
          ((constantSheaf V.left.smallEtaleTopology A).obj M) :=
      ((AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
        A V.hom inferInstance).app F).symm ≪≫ e ≪≫
        ((comparisonConstantIso V.left Λ).app M).symm
    exact comparison_counit_restriction_isIso X Λ V F
      ((AlgebraicGeometry.ProEtale.comparisonAdjunction A V.left).isIso_counit_app_of_iso eF)
  exact ⟨G, hG, ⟨asIso
    ((AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app F)⟩⟩

end AlgebraicGeometry.Scheme
