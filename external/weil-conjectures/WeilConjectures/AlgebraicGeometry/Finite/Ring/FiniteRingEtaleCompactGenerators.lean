/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.AlgebraicGeometry.Flat.FlatModel
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleLisseStratumCompact
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Compact generators on finite-type étale sites

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Section 6.4,
hypothesis before Example 6.4.1, Example 6.4.1, Lemmas 6.4.2 and 6.4.5,
and Proposition 6.4.8 (blueprint: lem-pur-etale-finite-ring-compact-generators).

Coproducts and the generator set are indexed in universe `u + 1`, the universe of the
module values and the small presentation of the site. The derived category has objects
in universe `u + 2`, but this does not enlarge the universe of its available coproducts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Bounded constructible finite-Tor complexes on a finite-type scheme over an algebraically
closed field are compact in the full unbounded étale derived category, and a set of these
complexes detects isomorphisms. No separatedness is required.

Proof, following the node and Bhatt--Scholze, Section 6.4:
1. The finite-type assumptions make `T` Noetherian. Grothendieck abelianness gives
   local smallness, and `derived_hasCoproducts` gives the required coproduct universe.
2. `compactObjects_isThick` and `boundedConstructible_induction` reduce compactness to the
   finite locally constant flat stratum objects. Flatness passes to geometric fibres
   through `Point.flat_sheafFiber_obj`; `uliftSheafFiberIso` aligns the universes.
   `lem-pur-etale-lisse-stratum-compact` proves these generators compact.
3. Use the actual type `T.AffineEtale` as the index set. The free Yoneda sheaves are
   constructible and flat by the source library's `isConstructibleSheaf_freeYoneda`
   and `flat_freeYoneda`. Their single complexes are bounded constructible, using
   `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf` to compare the
   constructibility conventions.
   Their explicit single flat models give Tor amplitude `[0,0]` via
   `hasTorAmplitudeIn_iff_exists_flatModel`.
4. `lem-pur-affine-etale-free-detection` supplies only the detection of isomorphisms
   by this explicit family and its shifts. Combine it with the preceding properties.

Source: Bhatt--Scholze, Section 6.4, Example 6.4.1, Lemmas 6.4.2 and 6.4.5, and
Proposition 6.4.8; perfect-value constructibility is related to bounded constructibility
and finite Tor amplitude by Lemma 6.3.7 and the finite-Tor perfectness criterion.
(blueprint: lem-pur-etale-finite-ring-compact-generators) -/
theorem finiteRing_compactGenerators
    {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ : ℕ) (hℓprime : Nat.Prime ℓ) (hℓunit : IsUnit (ℓ : k))
    {T : Scheme.{u}} (f : T ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    {C : Type (u + 1)} [CommRing C] [Finite C]
    (hC : ∃ n : ℕ, (ℓ : C) ^ n = 0) :
    ∃ (hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C T)),
      LocallySmall.{u + 1} (DerivedCategoryModule C T) ∧
      (∀ E : DerivedCategoryModule C T,
        DerivedCategory.isBoundedConstructible C T E ∧
          (∃ r s : ℤ, r ≤ s ∧ DerivedCategory.hasTorAmplitudeIn C T r s E) →
        @IsCompactObject (DerivedCategoryModule C T) _ _ hcoprod E) ∧
      (∃ (S : Type (u + 1)) (E : S → DerivedCategoryModule C T),
        (∀ s : S, DerivedCategory.isBoundedConstructible C T (E s) ∧
          ∃ r t : ℤ, r ≤ t ∧ DerivedCategory.hasTorAmplitudeIn C T r t (E s)) ∧
        ∀ (A B : DerivedCategoryModule C T) (h : A ⟶ B),
        (∀ (s : S) (n : ℤ),
            Function.Bijective (fun (φ : (E s)⟦n⟧ ⟶ A) ↦ φ ≫ h)) → IsIso h) := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian T := {}
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)) := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)) :=
    IsGrothendieckAbelian.hasColimits _
  let hc : HasCoproducts.{u + 1} (DerivedCategoryModule C T) :=
    CategoryTheory.derived_hasCoproducts
  let P : ObjectProperty (DerivedCategoryModule C T) := fun K ↦ IsCompactObject K
  have hthick := compactObjects_isThick (C := DerivedCategoryModule C T)
  let : P.IsTriangulated := hthick.1
  let : P.IsStableUnderRetracts := hthick.2
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have hcompact : ∀ K : DerivedCategoryModule C T,
      DerivedCategory.isBoundedConstructible C T K ∧
        (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn C T a b K) →
      IsCompactObject K := by
    intro K hK
    apply boundedConstructible_induction T C P ?_ K hK.1 hK.2
    rintro K ⟨str, i, j, hj, L, heq, hL, hflat, ⟨e⟩⟩
    have := hj
    have := hL
    obtain ⟨hc', hcompact⟩ :=
      isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf
        (k := k) (C := C) ℓ hℓprime hℓunit hC
        (X := T) (Z := (str.immersion i).image) (V := str.domain i)
        (str.immersion i).imageι j f L (by
          intro Ω _ _ s
          have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
              (CategoryTheory.forget (ModuleCat.{u + 1} C)) := inferInstance
          have h := GrothendieckTopology.Point.flat_sheafFiber_obj
            (A := ModuleCat.{u + 1} C) (J := (str.domain i).smallEtaleTopology)
            ((Scheme.pointSmallEtale s).ulift.{u + 1}) hflat
          exact ObjectProperty.prop_of_iso
            (P := ObjectProperty.flat)
            ((GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
              (Scheme.pointSmallEtale s) (ModuleCat.{u + 1} C)).app L) h)
    exact P.prop_of_iso e.symm hcompact
  refine ⟨hc, inferInstance, hcompact, T.AffineEtale,
    affineEtaleFreeComplex C T, ?_, ?_⟩
  · intro U
    let W := (Scheme.AffineEtale.Spec T).obj U
    have : IsAffine W.left := by
      change IsAffine ((Scheme.Spec).obj _)
      infer_instance
    let F := Sheaf.freeYoneda T.smallEtaleTopology W (ModuleCat.of C C)
    have hF : Scheme.IsConstructibleSheaf F := isConstructibleSheaf_freeYoneda W
    have hbc := DerivedCategory.boundedConstructible_singleFunctor_obj F 0
    change DerivedCategory.isBoundedConstructible C T
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ∧ _
    constructor
    · constructor
      · intro q
        exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
          (hbc.2 q)
      · refine ⟨0, 0, le_rfl, fun q hq ↦ ?_⟩
        rcases hq with hq | hq
        · exact (_root_.DerivedCategory.isGE_iff _ 0).1 inferInstance q hq
        · exact (_root_.DerivedCategory.isLE_iff _ 0).1 inferInstance q hq
    · refine ⟨0, 0, le_rfl, ?_⟩
      apply (hasTorAmplitudeIn_iff_exists_flatModel C 0 0 le_rfl _ hbc).2
      refine ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F,
        ⟨fun q hq ↦ ?_, fun q ↦ ?_⟩,
        ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩
      · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
      · by_cases hq : q = 0
        · subst hq
          exact ObjectProperty.prop_of_iso _
            (HomologicalComplex.singleObjXSelf _ 0 F).symm (flat_freeYoneda W)
        · exact ObjectProperty.flat_of_isZero
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)
  · intro A B h hh
    exact isIso_of_affineEtaleFreeComplex C T h hh

end AlgebraicGeometry.Etale
