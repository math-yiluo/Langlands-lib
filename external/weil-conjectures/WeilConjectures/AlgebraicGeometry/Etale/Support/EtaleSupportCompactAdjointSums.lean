/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.CategoryTheory.CompactCone
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeSheafFiniteness
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts

/-!
# Compact support, compact images, and coproducts of the exceptional adjoint

Source: Bhatt--Scholze, The pro-étale topology for schemes, Section 6.4,
Example 6.4.1 and Proposition 6.4.8, with Definition 6.3.1; the retained compact-image,
adjoint-coproduct and coefficient-functor argument of the blueprint node
(blueprint: lem-pur-etale-support-compact-adjoint-sums).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem boundedConstructible_iff
    (C : Type (u + 1)) [CommRing C] [Finite C] (T : Scheme.{u})
    (K : DerivedCategoryModule C T) :
    DerivedCategory.isBoundedConstructible C T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} C) T K := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ hz q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ hz q (.inr hq)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb q (lt_of_le_of_lt (le_max_right _ _) hq)

set_option linter.unusedVariables false in
/-- Compact support sends bounded constructible finite-Tor complexes to compact objects;
its fixed right adjoint preserves coproducts and is exact with adjunction-compatible shifts.
The termwise constant and the two coefficient tensor functors are exact and preserve sums.

Source: Bhatt--Scholze, Section 6.4, Example 6.4.1 and Proposition 6.4.8, Definition 6.3.1
(blueprint: lem-pur-etale-support-compact-adjoint-sums).

Proof plan:
1. Apply `theorem-results-from-etale-theory` to each nonzero cohomology sheaf. Reconstruct
   the input by the successive good-truncation triangles of
   `proposition-open-direct-image-preserves-finite`. Exactness and `thm-constructible-serre` give
   bounded constructibility of its image.
2. For a sheaf Q on Y use exact inverse image and the assumed projection formula,
   together with `lem-kun-tensor-sym`, to identify FE tensor Q with F(E tensor f*Q).
   The assumed interval bound gives Tor amplitude [a,b+N], including nonregular C.
3. `lem-pur-etale-finite-ring-compact-generators` on X and Y makes all such images
   compact and supplies bounded constructible finite-Tor compact generators on X.
   Their shifts have the same properties and therefore compact F-images.
4. Apply `lem-sc-compact-tests-right-adjoint-coproducts` to the family indexed by
   S times the integers. Adjunction identifies its Hom tests with the compactness
   comparisons for F(E_s[n]); detection proves the G-coproduct comparison invertible.
5. `lem-weil-pbc-adjunction-shift-compatibility-unique` supplies the coherent G-shifts
   normalized by the fixed adjunction. `lem-sf-triangulated-right-adjoint` gives exactness.
6. Constant presheaves preserve exact sequences and coproducts sectionwise.
   Exact colimit-preserving sheafification gives the same for constant module sheaves
   (`lem-weil-pbc-site-r-module-presheaf-sheafification-exact`). Apply the exact derived
   functor theorem. Module and module-sheaf Grothendieck abelianness and
   `lem-kun-grothendieck-derived-coproducts` identify derived sums termwise.
7. Compose these constant functors with tensor by GM or M, and then G where appropriate.
   `proposition-open-direct-image-preserves-finite` and
   `proposition-open-direct-image-preserves-finite` give exactness and preservation of arbitrary
   sums with the composite shift comparisons.
-/
theorem support_compactImages_adjoint_sums
    {k : Type u} [Field k] [IsAlgClosed k]
    (p ℓ : ℕ) [CharP k p] (hp : Nat.Prime p) (hℓ : Nat.Prime ℓ) (hℓp : ℓ ≠ p)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (C : Type (u + 1)) [CommRing C] [Finite C]
    (hC : ∃ m : ℕ, (ℓ : C) ^ m = 0)
    (G : DerivedCategoryModule C Y ⥤ DerivedCategoryModule C X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ G)
    [(rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).CommShift ℤ]
    [(rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).IsTriangulated]
    (N : ℤ) (hN : 0 ≤ N)
    (hinterval : ∀ (a b : ℤ), a ≤ b → ∀ E : DerivedCategoryModule C X,
      _root_.DerivedCategory.IsGE E a → _root_.DerivedCategory.IsLE E b →
      _root_.DerivedCategory.IsGE
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj E) a ∧
      _root_.DerivedCategory.IsLE
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj E) (b + N))
    (hprojection : ∀ (K : DerivedCategoryModule C X) (L : DerivedCategoryModule C Y),
      IsIso (compactSupportProjectionMapOfCompactification C c K L)) :
    ∃ (hX : HasCoproducts.{u + 1} (DerivedCategoryModule C X))
      (hY : HasCoproducts.{u + 1} (DerivedCategoryModule C Y)),
      (∀ (a b : ℤ) (E : DerivedCategoryModule C X),
        DerivedCategory.isBoundedConstructible C X E →
        DerivedCategory.hasTorAmplitudeIn C X a b E →
        DerivedCategory.isBoundedConstructible C Y
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj E) ∧
        DerivedCategory.hasTorAmplitudeIn C Y a (b + N)
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj E) ∧
        @IsCompactObject (DerivedCategoryModule C Y) _ _ hY
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj E)) ∧
      (∃ (S : Type (u + 1)) (E : S → DerivedCategoryModule C X),
        (∀ s : S, DerivedCategory.isBoundedConstructible C X (E s) ∧
          (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn C X a b (E s)) ∧
          @IsCompactObject (DerivedCategoryModule C X) _ _ hX (E s) ∧
          @IsCompactObject (DerivedCategoryModule C Y) _ _ hY
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj
              (E s))) ∧
        ∀ (A B : DerivedCategoryModule C X) (h : A ⟶ B),
          (∀ (s : S) (n : ℤ),
            Function.Bijective (fun φ : (E s)⟦n⟧ ⟶ A ↦ φ ≫ h)) → IsIso h) ∧
      (∀ I : Type v, PreservesColimitsOfShape (Discrete I) G) ∧
      ∃ (hG : G.CommShift ℤ),
        G.IsTriangulated ∧
        (∀ (n : ℤ) (M : DerivedCategoryModule C Y),
          adj.counit.app (M⟦n⟧) =
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
                ((G.commShiftIso n).hom.app M) ≫
              ((rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} C) c).commShiftIso n).hom.app (G.obj M) ≫
              (shiftFunctor _ n).map (adj.counit.app M)) ∧
        (constantSheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategory.IsTriangulated ∧
        (constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategory.IsTriangulated ∧
        (∀ I : Type v, PreservesColimitsOfShape (Discrete I)
          (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ∧
          PreservesColimitsOfShape (Discrete I)
            (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory) ∧
        ∀ M : DerivedCategoryModule C Y,
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ⋙
            (derivedTensor (ModuleCat.{u + 1} C) X).flip.obj (G.obj M)).IsTriangulated ∧
          (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ⋙
            (derivedTensor (ModuleCat.{u + 1} C) Y).flip.obj M) ⋙ G).IsTriangulated ∧
          ∀ I : Type v, PreservesColimitsOfShape (Discrete I)
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ⋙
              (derivedTensor (ModuleCat.{u + 1} C) X).flip.obj (G.obj M)) ∧
            PreservesColimitsOfShape (Discrete I)
              (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ⋙
                (derivedTensor (ModuleCat.{u + 1} C) Y).flip.obj M) ⋙ G) := by
  classical
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c
  have hunit : IsUnit (ℓ : k) := by
    apply Ne.isUnit
    rw [ne_eq, CharP.cast_eq_zero_iff k p]
    intro hd
    rcases hℓ.eq_one_or_self_of_dvd p hd with h | h
    · exact hp.ne_one h
    · exact hℓp h.symm
  obtain ⟨m, hm⟩ := hC
  have hcoeff : IsSmoothBaseChangeCoefficients (ℓ ^ m) C (Spec (.of k)) := by
    refine ⟨pow_pos hℓ.pos _, inferInstance, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hm
    · simpa only [Nat.cast_pow, map_pow, map_natCast] using
        (hunit.pow m).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hbc : ∀ E, DerivedCategory.isBoundedConstructible C X E →
      DerivedCategory.isBoundedConstructible C Y (F.obj E) := by
    intro E hE
    apply (boundedConstructible_iff C Y _).2
    apply boundedConstructible_obj_of_forall_singleFunctor C F ?_
      ((boundedConstructible_iff C X E).1 hE)
    intro Q hQ
    have hQ' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf Q).2 hQ
    have hfin := (finiteType_directImages_finiteConstructible k C (ℓ ^ m) hcoeff
      X Y f Q hQ').2.1
    let d := compactSupportAmplitudeCompactification k Y f
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (.of k))
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (.of k))
    have : IsNoetherian X := {}
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
      (Y ↘ Spec (.of k))
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of k))
    have : IsNoetherian Y := {}
    exact (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} C) Y).prop_of_iso
      ((rightDerivedLowerShriekOfCompactificationIso C d c).app _)
      ((boundedConstructible_iff C Y _).1 hfin)
  have htor : ∀ (a b : ℤ) (E : DerivedCategoryModule C X),
      DerivedCategory.hasTorAmplitudeIn C X a b E →
      DerivedCategory.hasTorAmplitudeIn C Y a (b + N) (F.obj E) := by
    intro a b E ht Q q hq
    let Q₀ := (_root_.DerivedCategory.singleFunctor _ 0).obj Q
    let D := (upperStar (ModuleCat.{u + 1} C) f).mapDerivedCategory
    let P := ((derivedTensor (ModuleCat.{u + 1} C) X).obj E).obj (D.obj Q₀)
    let eP : P ≅ ((derivedTensor (ModuleCat.{u + 1} C) X).obj E).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} C) f).obj Q)) :=
      ((derivedTensor (ModuleCat.{u + 1} C) X).obj E).mapIso
        (((upperStar (ModuleCat.{u + 1} C) f).mapDerivedCategorySingleFunctor 0).app Q)
    have hP (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj P) :=
      (ht _ i hi).of_iso ((_root_.DerivedCategory.homologyFunctor _ i).mapIso eP)
    have hPa : _root_.DerivedCategory.IsGE P a :=
      (_root_.DerivedCategory.isGE_iff _ a).2 fun i hi ↦ hP i (.inl hi)
    have hPb : _root_.DerivedCategory.IsLE P b :=
      (_root_.DerivedCategory.isLE_iff _ b).2 fun i hi ↦ hP i (.inr hi)
    have hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (F.obj P)) := by
      by_cases hab : a ≤ b
      · obtain ⟨ha, hb⟩ := hinterval a b hab P hPa hPb
        rcases hq with hq | hq
        · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha q hq
        · exact (_root_.DerivedCategory.isLE_iff _ (b + N)).1 hb q hq
      · have : _root_.DerivedCategory.TStructure.t.IsGE P a := hPa
        have : _root_.DerivedCategory.TStructure.t.IsLE P b := hPb
        exact (_root_.DerivedCategory.homologyFunctor _ q).map_isZero
          (F.map_isZero (_root_.DerivedCategory.TStructure.t.isZero P b a (by omega)))
    have := hprojection E Q₀
    let e : ((derivedTensor (ModuleCat.{u + 1} C) Y).obj (F.obj E)).obj Q₀ ≅
        F.obj P :=
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).app (F.obj E)).app Q₀ ≪≫
      asIso (compactSupportProjectionMapOfCompactification C c E Q₀) ≪≫
      F.mapIso (((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).app (D.obj Q₀)).app E)
    exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
  obtain ⟨hX, hsmallX, hcompactX, S, E, hE, hdetect⟩ :=
    finiteRing_compactGenerators ℓ hℓ hunit (X ↘ Spec (.of k)) ⟨m, hm⟩
  obtain ⟨hY, hsmallY, hcompactY, -⟩ :=
    finiteRing_compactGenerators ℓ hℓ hunit (Y ↘ Spec (.of k)) ⟨m, hm⟩
  let := hX
  let := hY
  let := hsmallY
  have himage : ∀ (a b : ℤ) (K : DerivedCategoryModule C X),
      DerivedCategory.isBoundedConstructible C X K →
      DerivedCategory.hasTorAmplitudeIn C X a b K → IsCompactObject (F.obj K) := by
    intro a b K hK ht
    apply hcompactY _
    refine ⟨hbc K hK, min a b, max a b + N, ?_, ?_⟩
    · omega
    · apply htor
      intro Q q hq
      apply ht Q q
      rcases hq with hq | hq <;> omega
  have hcE (s : S) : IsCompactObject (E s) ∧ IsCompactObject (F.obj (E s)) := by
    obtain ⟨hbcE, a, b, hab, ht⟩ := hE s
    exact ⟨hcompactX _ ⟨hbcE, a, b, hab, ht⟩, himage a b _ hbcE ht⟩
  let PY : ObjectProperty (DerivedCategoryModule C Y) := fun K ↦ IsCompactObject K
  let : PY.IsStableUnderRetracts := (compactObjects_isThick).2
  have hGsum : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) G := by
    apply compactTests_rightAdjoint_preservesCoproducts F G adj (S × ℤ)
      (fun s ↦ (E s.1)⟦s.2⟧)
    · intro ⟨s, n⟩
      refine ⟨compact_shift _ (hcE s).1 n, ?_⟩
      exact PY.prop_of_iso ((F.commShiftIso n).app (E s)).symm
        (compact_shift _ (hcE s).2 n)
    · intro A B h hh
      exact hdetect A B h fun s n ↦ hh (s, n)
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  have hGtri : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  let := hGtri
  have hconst (T : Scheme.{u}) : ∀ I : Type v, PreservesColimitsOfShape (Discrete I)
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory := by
    intro I
    exact (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} C))
      |>.mapDerivedCategoryRightDerivedAdjunction.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have htensor (T : Scheme.{u}) (K : DerivedCategoryModule C T) :
      ∀ I : Type v, PreservesColimitsOfShape (Discrete I)
        ((derivedTensor (ModuleCat.{u + 1} C) T).flip.obj K) := by
    intro I
    have : PreservesColimitsOfShape (Discrete I)
        ((derivedTensor (ModuleCat.{u + 1} C) T).obj K) :=
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} C) K)
        |>.leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact preservesColimitsOfShape_of_natIso
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) T).app K)
  refine ⟨hX, hY, ?_, ?_, hGsum, inferInstance, hGtri, ?_,
    inferInstance, inferInstance, fun I ↦ ⟨hconst X I, hconst Y I⟩, ?_⟩
  · intro a b K hK ht
    exact ⟨hbc K hK, htor a b K ht, himage a b K hK ht⟩
  · exact ⟨S, E, fun s ↦ ⟨(hE s).1, (hE s).2, (hcE s).1, (hcE s).2⟩, hdetect⟩
  · intro n M
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      (adj.commShiftIso_hom_app_counit_app_shift ℤ n M).symm
  · intro M
    refine ⟨inferInstance, inferInstance, fun I ↦ ?_⟩
    let := hconst X I
    let := hconst Y I
    let := htensor X (G.obj M) I
    let := htensor Y M I
    let := hGsum I
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Etale
