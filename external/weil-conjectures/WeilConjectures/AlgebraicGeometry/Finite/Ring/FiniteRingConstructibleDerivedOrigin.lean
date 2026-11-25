/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Bounded constructible derived comparison for arbitrary finite rings

Source: Stacks Project, Tag 09AL, lemma-compare-constructible-derived, and its exact
cohomology comparison, with the blueprint's global finite-stratification convention
(blueprint: lem-weil-pbc-finite-ring-constructible-derived-origin).

The induced equivalence is stated by its equivalent full-faithfulness and essential-image
criterion. The functor is the specified exact inverse image, in the canonical constant-ring
presentation used by intrinsic constructibility. Its source is the existing full bounded
constructible etale subcategory. The essential-image criterion includes the etale-origin
conclusion, without choosing an inverse equivalence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def intrinsicRealizationRestrictionIso (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    (ProEtale.finiteCoefficientIntrinsicRealization X B).obj
      ((proEtaleModuleRestriction X B).obj M) ≅ M :=
  asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X B)).counit.app M)

private theorem intrinsicRealization_constructible_iff (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    (G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    IsConstructibleProEtaleModuleSheaf X B
      ((ProEtale.finiteCoefficientIntrinsicRealization X B).obj G) ↔
        ProEtale.IsConstructible (ULift.{u + 1, u} B) G := by
  let R := ProEtale.finiteCoefficientIntrinsicRealization X B
  have : R.IsEquivalence :=
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X B).1
  let e : (proEtaleModuleRestriction X B).obj (R.obj G) ≅ G :=
    R.preimageIso (intrinsicRealizationRestrictionIso X B (R.obj G))
  rw [proEtaleModuleRestriction_constructible_iff]
  exact ⟨fun h ↦ ProEtale.isConstructible_of_iso e h,
    fun h ↦ ProEtale.isConstructible_of_iso e.symm h⟩

private theorem intrinsicConstructible_of_iso (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    {M N : proEtaleRingModules X (proEtaleConstantRing X B)} (e : M ≅ N)
    (h : IsConstructibleProEtaleModuleSheaf X B M) :
    IsConstructibleProEtaleModuleSheaf X B N := by
  rw [proEtaleModuleRestriction_constructible_iff] at h ⊢
  exact ProEtale.isConstructible_of_iso ((proEtaleModuleRestriction X B).mapIso e) h

/-- Exact inverse image induces an equivalence from bounded constructible etale complexes
onto the pro-etale complexes with intrinsically constructible bounded cohomology, and
preserves and reflects every cohomological interval. Fullness, faithfulness and the
specified essential image are the standard criterion for this induced equivalence.
The ring is any finite commutative ring, including the zero ring; no valuation ring is used.
Source: Stacks Project, Tag 09AL, with the global finite partitions of the blueprint
(blueprint: lem-weil-pbc-finite-ring-constructible-derived-origin).

Proof: factor the specified inverse image into fixed-coefficient inverse image and
constant-ring realization. The latter is an exact equivalence; its sheafification counit
identifies it with the inverse of restriction to constant scalars. The proved restriction
comparison therefore identifies intrinsic constructibility with fixed-module constructibility,
without changing the global finite-stratification convention.

Full faithfulness on bounded below complexes restricts to the bounded constructible
subcategory, and is unchanged by composition with the realization equivalence. For the
essential-image criterion, exact cohomology comparison proves the forward implication.
For the converse, transfer the complex through realization, descend its constructible
cohomology sheaves, and apply the existing theorem
`ProEtale.DerivedCategory.boundedConstructible_of_homology`. That theorem performs the
bounded truncation induction, lifting connecting maps by full faithfulness and using
triangulated closure of the essential image. Convert the resulting etale cohomology
predicates and bounds to the stated bounded constructible subcategory. Finally exactness
preserves cohomological vanishing and faithfulness reflects it degreewise; this proves the
interval assertion, also when the interval is empty. -/
theorem finiteRing_constructibleDerived_origin (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B] :
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} B) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).Full ∧
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} B) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).Faithful ∧
    (∀ K : proEtaleDerivedCategory X B,
      (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} B) X) ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).essImage K ↔
      (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X B
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj K)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj K)) ∧
    (∀ (L : ProEtale.FiniteCoefficientEtaleDerivedCategory X (ULift.{u + 1, u} B))
      (a b : ℤ),
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) i).obj L)) ↔
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj
            ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj L)))) := by
  classical
  let R := ProEtale.finiteCoefficientIntrinsicRealization X B
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X
  have hfinite := ProEtale.siteComparison_finiteLevel X (ULift.{u + 1, u} B)
  have : PreservesFiniteLimits C := hfinite.1
  have : PreservesFiniteColimits C := hfinite.2.1
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) X
  have : R.IsEquivalence :=
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X B).1
  have hplus (L : P.FullSubcategory) : DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨a, b, _, hvan⟩ := L.property.2
    exact ⟨a, (DerivedCategory.isGE_iff L.obj a).2 fun i hi ↦ hvan i (Or.inl hi)⟩
  have hfull : (P.ι ⋙ C.mapDerivedCategory).Full := ⟨fun {K L} f ↦ by
    obtain ⟨g, hg⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj (hplus L)).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩⟩
  have hfaithful : (P.ι ⋙ C.mapDerivedCategory).Faithful := ⟨fun {K L} f g h ↦ by
    exact ObjectProperty.hom_ext _
      ((ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj (hplus L)).1 h)⟩
  let e : P.ι ⋙ ProEtale.finiteCoefficientIntrinsicDerivedComparison X B ≅
      (P.ι ⋙ C.mapDerivedCategory) ⋙ R.mapDerivedCategory :=
    Functor.isoWhiskerLeft P.ι (Functor.mapDerivedCategoryCompIso C R).symm ≪≫
      (Functor.associator _ _ _).symm
  refine ⟨Functor.Full.of_iso e.symm, Functor.Faithful.of_iso e.symm, ?_, ?_⟩
  · intro K
    constructor
    · rintro ⟨L, ⟨eL⟩⟩
      let F := ProEtale.finiteCoefficientIntrinsicComparison X B
      refine ⟨?_, ?_⟩
      · intro i
        have hc := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
          (L.property.1 i)
        let := hc
        have hC := ProEtale.isConstructible_comparisonUpperStar_obj
          ((DerivedCategory.homologyFunctor _ i).obj L.obj)
        have hR := (intrinsicRealization_constructible_iff X B _).mpr hC
        exact intrinsicConstructible_of_iso X B
          ((F.mapDerivedCategoryHomologyFunctorIso i).app L.obj ≪≫
            (DerivedCategory.homologyFunctor _ i).mapIso eL) hR
      · obtain ⟨a, b, hab, hv⟩ := L.property.2
        refine ⟨a, b, hab, fun i hi ↦ ?_⟩
        exact (F.isZero_homologyFunctor_mapDerivedCategory_obj (hv i hi)).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso eL).symm
    · rintro ⟨hc, a, b, hab, hv⟩
      let J := R.mapDerivedCategory.objPreimage K
      let eJ : R.mapDerivedCategory.obj J ≅ K := R.mapDerivedCategory.objObjPreimageIso K
      have he (i : ℤ) : R.obj ((DerivedCategory.homologyFunctor _ i).obj J) ≅
          (DerivedCategory.homologyFunctor _ i).obj K :=
        (R.mapDerivedCategoryHomologyFunctorIso i).app J ≪≫
          (DerivedCategory.homologyFunctor _ i).mapIso eJ
      have hJ : DerivedCategory.TStructure.t.bounded J := by
        apply R.bounded_of_bounded_mapDerivedCategory_obj
        refine ⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr ?_⟩,
          ⟨b, (DerivedCategory.isLE_iff _ b).mpr ?_⟩⟩
        · intro i hi
          exact (hv i (Or.inl hi)).of_iso
            ((DerivedCategory.homologyFunctor _ i).mapIso eJ)
        · intro i hi
          exact (hv i (Or.inr hi)).of_iso
            ((DerivedCategory.homologyFunctor _ i).mapIso eJ)
      have hH (i : ℤ) : ProEtale.IsConstructible (ULift.{u + 1, u} B)
          ((DerivedCategory.homologyFunctor _ i).obj J) := by
        apply (intrinsicRealization_constructible_iff X B _).mp
        exact intrinsicConstructible_of_iso X B (he i).symm (hc i)
      obtain ⟨L, hL, ⟨eL⟩⟩ :=
        ProEtale.DerivedCategory.boundedConstructible_of_homology
          (ULift.{u + 1, u} B) hJ (fun i ↦
            ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
              (ULift.{u + 1, u} B) (hH i))
      have hLP : P L := by
        refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
          (hL.2 i), ?_⟩
        obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hL.1
        refine ⟨min c d, max c d, min_le_max, fun i hi ↦ ?_⟩
        rcases hi with hi | hi
        · exact (DerivedCategory.isGE_iff L c).mp hc i (lt_of_lt_of_le hi (min_le_left _ _))
        · exact (DerivedCategory.isLE_iff L d).mp hd i (lt_of_le_of_lt (le_max_right _ _) hi)
      refine ⟨⟨L, hLP⟩, ⟨?_⟩⟩
      exact (Functor.mapDerivedCategoryCompIso C R).symm.app L ≪≫
        R.mapDerivedCategory.mapIso eL ≪≫ eJ
  · intro L a b
    have : C.Faithful := inferInstance
    have : (ProEtale.finiteCoefficientIntrinsicComparison X B).Faithful :=
      inferInstanceAs (C ⋙ R).Faithful
    constructor
    · intro h i hi
      exact (ProEtale.finiteCoefficientIntrinsicComparison X B)
        |>.isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)
    · intro h i hi
      exact (ProEtale.finiteCoefficientIntrinsicComparison X B)
        |>.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)

end AlgebraicGeometry.Scheme
