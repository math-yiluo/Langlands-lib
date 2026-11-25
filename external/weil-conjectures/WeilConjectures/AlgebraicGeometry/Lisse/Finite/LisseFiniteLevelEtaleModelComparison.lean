/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Bounded etale models from finite locally constant cohomology models

## References

* Stacks Tags 099Y, 099Z and 09B1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

private def modelHomologyIso (Z : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _))).inverse ⋙
        (@DerivedCategory.homologyFunctor
          (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _) q) := by
  let B := Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)
  let H := @DerivedCategory.homologyFunctor B _ _ (HasDerivedCategory.standard B) q
  let Q := @DerivedCategory.Q B _ _ (HasDerivedCategory.standard B)
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory B _ _ (HasDerivedCategory.standard B))
  let eQ : DerivedCategory.Q ⋙ e.inverse ≅ Q :=
    Functor.associator Q e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft Q e.unitIso.symm ≪≫ Q.rightUnitor
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) B).preimageIso
      (DerivedCategory.homologyFunctorFactors B q ≪≫
        (@DerivedCategory.homologyFunctorFactors B _ _
          (HasDerivedCategory.standard B) q).symm ≪≫
        Functor.isoWhiskerRight eQ.symm H ≪≫ Functor.associator _ _ _)

private theorem modelClassical_of_iso (Z : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {F G : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : ProEtale.IsClassicalModuleFor Z Λ F) :
    ProEtale.IsClassicalModuleFor Z Λ G := by
  intro I _ _ P
  have hmap := ProEtale.continuityMap_natural P e.hom.hom
  have : IsIso (ProEtale.continuityMap P F.obj) := hF P
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op
      ((sheafToPresheaf _ _).mapIso e)).hom
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
  rw [hmap]
  infer_instance

/-- A bounded pro-etale complex whose cohomology has finite locally constant etale
models has an etale model with the same bounds and finite locally constant cohomology.
The comparison is the canonical derived counit, so the chosen model is tied to K. -/
theorem lisse_finite_level_etale_model_comparison
    (Z : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hcohom : ∀ q : ℤ, ∃ G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf G ∧
        Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).obj G ≅
          (DerivedCategory.homologyFunctor _ q).obj K)) :
    ∃ D : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      (∀ q : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} Λ) Z).mapDerivedCategory.obj D ≅ K) := by
  classical
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Z
  obtain ⟨a, b, hab⟩ := hbounded
  let Kplus : DerivedCategory.Plus
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)) :=
    ⟨K, a, (DerivedCategory.isGE_iff K a).2 (fun q hq ↦ hab q (Or.inl hq))⟩
  have hclass : ProEtale.ClassicalPlus Z Λ Kplus := by
    intro q
    obtain ⟨G, _, ⟨e⟩⟩ := hcohom q
    obtain ⟨L, hL, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves Z).2.2 Λ
    have hG : ProEtale.IsClassicalModuleFor Z Λ (F.obj G) := by
      change ProEtale.IsClassicalModuleFor Z Λ
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).obj G)
      rw [← hL]
      exact (L.obj G).property
    apply modelClassical_of_iso Z Λ (e ≪≫ (modelHomologyIso Z Λ q).app K)
    exact hG
  let adj := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) Z).derivedPlus
  have : IsIso (adj.counit.app Kplus) :=
    (ProEtale.classicalDerivedEquivalence Z Λ).2.1 Kplus hclass
  let R := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) Z).rightDerivedFunctorPlus
  let D := (R.obj Kplus).obj
  let e : F.mapDerivedCategory.obj D ≅ K :=
    DerivedCategory.Plus.ι.mapIso (asIso (adj.counit.app Kplus))
  refine ⟨D, ⟨a, b, ?_⟩, ?_, ⟨e⟩⟩
  · intro q hq
    exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((hab q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e))
  · intro q
    obtain ⟨G, hG, ⟨eG⟩⟩ := hcohom q
    have := hG
    let eq : F.obj ((DerivedCategory.homologyFunctor _ q).obj D) ≅ F.obj G :=
      (F.mapDerivedCategoryHomologyFunctorIso q).app D ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫ eG.symm
    exact IsFiniteLocallyConstantSheaf.of_iso (F.preimageIso eq).symm

end AlgebraicGeometry.Scheme
