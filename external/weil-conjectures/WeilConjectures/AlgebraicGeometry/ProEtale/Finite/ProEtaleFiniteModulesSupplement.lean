/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules

/-!
# Finite coefficients on the small pro-etale site

## Main definitions

* `finiteCoefficientRingSheaf`: sheafified continuous functions on connected components.
* `FiniteCoefficientModules`: left modules over this ring sheaf.
* `FiniteCoefficientDerivedCategory` and `FiniteCoefficientDerivedCategoryPlus`: the
  unbounded localization and its strictly full bounded below subcategory.
* `finiteCoefficientEtaleRingSheaf` and `FiniteCoefficientEtaleDerivedCategory`: etale
  coefficients, using the canonical fixed-ring module-sheaf presentation.
* `finiteCoefficientDerivedComparison`: the exact module inverse image on complexes.
* `isBoundedConstructibleFiniteCoefficient`: the essential image of bounded constructible
  etale complexes, with its full subcategory `FiniteCoefficientBoundedConstructibleDerivedCategory`.
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private noncomputable def coefficientModulePresheafFullyFaithful
    (C : Type uC) [Category.{vC} C] (Λ : Type (u + 1)) [Ring Λ] :
    (finiteCoefficientModulePresheaf C Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private theorem coefficientRealization_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      finiteCoefficientModulePresheaf C Λ ⋙
      PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  have : (finiteCoefficientModulePresheaf C Λ).Full :=
    (coefficientModulePresheafFullyFaithful C Λ).full
  have : (finiteCoefficientModulePresheaf C Λ).Faithful :=
    (coefficientModulePresheafFullyFaithful C Λ).faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf C Λ
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    let F' : Sheaf J (ModuleCat.{u + 1} Λ) :=
      ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
    refine ⟨F', ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  change (E ⋙ S).IsEquivalence
  exact Functor.IsEquivalence.mk

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- The category of left modules over the specified coefficient ring sheaf, with sectionwise
linear morphisms. -/
noncomputable abbrev FiniteCoefficientModules :=
  ringedSiteModules.{u + 1} (finiteCoefficientRingSheaf T Λ)

/-- Localization of integer-indexed cochain complexes of coefficient modules at
quasi-isomorphisms. -/
noncomputable abbrev FiniteCoefficientDerivedCategory :=
  @DerivedCategory (FiniteCoefficientModules T Λ) _ _ (HasDerivedCategory.standard _)

/-- The strictly full bounded below subcategory, using the standard cohomological
lower bound. -/
noncomputable abbrev FiniteCoefficientDerivedCategoryPlus :=
  @DerivedCategory.Plus (FiniteCoefficientModules T Λ) _ _ (HasDerivedCategory.standard _)

/-- The etale derived category in the standard fixed-ring module-sheaf encoding.
The canonical equivalence above identifies its abelian category with modules over
`finiteCoefficientEtaleRingSheaf`. -/
abbrev FiniteCoefficientEtaleDerivedCategory :=
  DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Realization as modules over the specified ring sheaf: keep the module presheaf,
then apply the canonical associated-module-sheaf functor along constant scalar sections. -/
noncomputable def finiteCoefficientRealization :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⥤
      FiniteCoefficientModules T Λ :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt Λ ⋙
    PresheafOfModules.sheafification (finiteCoefficientScalarMap T Λ)

/-- Realization is additive and exact; it is the canonical identification of fixed-ring
module sheaves with modules over the coefficient ring sheaf. -/
theorem finiteCoefficientRealization_exact :
    (finiteCoefficientRealization T Λ).Additive ∧
    PreservesFiniteLimits (finiteCoefficientRealization T Λ) ∧
    PreservesFiniteColimits (finiteCoefficientRealization T Λ) := by
  have : (finiteCoefficientRealization T Λ).IsEquivalence :=
    coefficientRealization_isEquivalence (Scheme.ProEt.topology T) Λ
      (finiteCoefficientRingSheaf T Λ) (finiteCoefficientScalarMap T Λ)
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the canonical coefficient realization. -/
noncomputable instance finiteCoefficientRealization_additive :
    (finiteCoefficientRealization T Λ).Additive :=
  (finiteCoefficientRealization_exact T Λ).1

/-- Left exactness of the canonical coefficient realization. -/
noncomputable instance finiteCoefficientRealization_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientRealization T Λ) :=
  (finiteCoefficientRealization_exact T Λ).2.1

/-- Right exactness of the canonical coefficient realization. -/
noncomputable instance finiteCoefficientRealization_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientRealization T Λ) :=
  (finiteCoefficientRealization_exact T Λ).2.2

/-- The specified inverse image on left module sheaves: the comparison inverse image,
followed by its canonical coefficient-ring realization. -/
noncomputable def finiteCoefficientComparison :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ FiniteCoefficientModules T Λ :=
  comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ

/-- Additivity inherited from comparison and coefficient realization. -/
noncomputable instance finiteCoefficientComparison_additive :
    (finiteCoefficientComparison T Λ).Additive :=
  inferInstanceAs
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ).Additive

/-- Left exactness inherited from comparison and coefficient realization. -/
noncomputable instance finiteCoefficientComparison_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientComparison T Λ) :=
  inferInstanceAs (PreservesFiniteLimits
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ))

/-- Right exactness inherited from comparison and coefficient realization. -/
noncomputable instance finiteCoefficientComparison_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientComparison T Λ) :=
  inferInstanceAs (PreservesFiniteColimits
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ))

/-- The chosen localization of ringed module sheaves, with the standard morphism universe. -/
noncomputable instance finiteCoefficientModules_hasDerivedCategory :
    HasDerivedCategory.{u + 2} (FiniteCoefficientModules T Λ) :=
  HasDerivedCategory.standard _

/-- Applying the exact comparison termwise to integer-indexed cochain complexes induces
this functor on their localizations. -/
noncomputable def finiteCoefficientDerivedComparison :
    FiniteCoefficientEtaleDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategory T Λ :=
  (finiteCoefficientComparison T Λ).mapDerivedCategory

/-- Bounded constructible objects are the essential image of bounded constructible
etale complexes under the canonical derived comparison functor. -/
def isBoundedConstructibleFiniteCoefficient (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    ObjectProperty (FiniteCoefficientDerivedCategory T Λ) :=
  ObjectProperty.map (fun L : FiniteCoefficientEtaleDerivedCategory T Λ ↦
    (∀ j : ℤ, ∃ S : Scheme.Stratification T,
      (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
      ∀ k : Fin S.n,
        ∃ d : Scheme.LocallyConstantDatum
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj
            ((_root_.DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj L)),
          ∀ i : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
            Nonempty
              ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj
                ((_root_.DerivedCategory.homologyFunctor
                  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj L)).over
                    (d.cover.etalePrecoverageToEtale i)) ≅
                (constantSheaf
                  ((S.domain k).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
                  (ModuleCat.{u + 1} Λ)).obj M)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj L))
    (finiteCoefficientDerivedComparison T Λ)

/-- Equivalence structure on the canonical coefficient realization. -/
noncomputable instance finiteCoefficientRealizationIsEquivalenceRing (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).IsEquivalence :=
  coefficientRealization_isEquivalence (Scheme.ProEt.topology T) Λ
    (finiteCoefficientRingSheaf T Λ) (finiteCoefficientScalarMap T Λ)

/-- The canonical realization identifies fixed-ring module sheaves with modules over the
continuous-function coefficient sheaf, including finite noncommutative coefficient rings. -/
theorem finiteCoefficientRealization_isEquivalence_ring (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).IsEquivalence :=
  finiteCoefficientRealizationIsEquivalenceRing.{u} T Λ

end AlgebraicGeometry.ProEtale
