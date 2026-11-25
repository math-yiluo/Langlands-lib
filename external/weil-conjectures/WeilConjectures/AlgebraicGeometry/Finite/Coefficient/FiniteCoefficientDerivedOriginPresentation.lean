/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

/-! # Finite coefficient derived origin in the site universe

Source: Stacks Project and the local-effectivity argument in amplification (c).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- The finite truncation argument only needs constructible comparison and full faithfulness.
-- Keep this local so that the unrelated perfect-duality and smooth-trace theory is not imported.
open ProEtale ProEtale.DerivedCategory in
open scoped CategoryTheory.Functor in
private theorem origin_boundedConstructible_isTriangulated
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulated := by
  let F := D(ν^*(X)[ModuleCat.{u + 1} Λ])
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₃ := by
    refine ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT ⟨A, hA, ⟨e₁⟩⟩ ⟨B, hB, ⟨e₂⟩⟩ ↦ ?_
    obtain ⟨f, hf⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map A B hB.1.1).2
      (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    obtain ⟨Z, g, h, hZ⟩ := Pretriangulated.distinguished_cocone_triangle f
    obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ T
      (F.map_distinguished _ hZ) hT (Arrow.isoMk e₁ e₂ (by
        have hf' : F.map f = e₁.hom ≫ T.mor₁ ≫ e₂.inv := hf
        change e₁.hom ≫ T.mor₁ = F.map f ≫ e₂.hom
        simp [hf']))
    exact ⟨Z, (Etale.DerivedCategory.boundedConstructible _ X).ext_of_isTriangulatedClosed₃ _
      hZ hA hB, ⟨Pretriangulated.Triangle.π₃.mapIso e⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K ⟨A, hA, ⟨e⟩⟩ ↦ ⟨A⟦n⟧,
      (Etale.DerivedCategory.boundedConstructible _ X).le_shift n _ hA,
      ⟨(F.commShiftIso n).app A ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  obtain ⟨Z, hZ, hZP⟩ := ObjectProperty.ContainsZero.exists_zero
    (P := Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X)
  exact { exists_zero := ⟨F.obj Z, F.map_isZero hZ,
    boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hZP⟩ }

open ProEtale ProEtale.DerivedCategory in
open scoped CategoryTheory.Functor in
private theorem origin_boundedConstructible_of_homology
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hH : ∀ n, ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅
        (_root_.DerivedCategory.homologyFunctor _ n).obj K)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  let := origin_boundedConstructible_isTriangulated X Λ
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅ G)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e ⟨F, hF, ⟨e'⟩⟩ ↦ ⟨F, hF, ⟨e' ≪≫ e⟩⟩⟩
  refine _root_.DerivedCategory.prop_of_bounded _ P (fun G ⟨F, hF, ⟨e⟩⟩ ↦ ?_) K hK hH
  exact ⟨_, Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
    ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩

private def restrictCancelIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : X.ProEtᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private abbrev coefficientEquivalence (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
  CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (restrictCancelIso X e.inv e.hom e.inv_hom_id).symm
    (restrictCancelIso X e.hom e.inv e.hom_inv_id)

private theorem coefficientEquivalence_isEquivalence (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence := by
  exact (coefficientEquivalence X e).isEquivalence_functor

private theorem finite_presentation_representative
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : DerivedCategory (pbcModules X (AdicCoefficients.coefficientRing X B))) :
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := discreteTopology_bot _
    letI : (SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison X B).hom).IsEquivalence :=
      coefficientEquivalence_isEquivalence X (AdicCoefficients.finiteRingComparison X B)
    ∀ K₀ : DerivedCategory (ProEtale.FiniteCoefficientModules X B),
      ProEtale.isBoundedConstructibleFiniteCoefficient X B K₀ →
      Nonempty ((SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison X B).hom).mapDerivedCategory.obj K₀ ≅ K) →
      ∃ C : CochainComplex (ProEtale.FiniteCoefficientModules X B) ℤ,
        ProEtale.isBoundedConstructibleFiniteCoefficient X B (DerivedCategory.Q.obj C) ∧
        Nonempty (DerivedCategory.Q.obj
          (((SheafOfModules.restrictScalars
            (AdicCoefficients.finiteRingComparison X B).hom).mapHomologicalComplex
              (.up ℤ)).obj C) ≅ K) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot _
  let F := SheafOfModules.restrictScalars
    (AdicCoefficients.finiteRingComparison X B).hom
  have : F.IsEquivalence :=
    coefficientEquivalence_isEquivalence X (AdicCoefficients.finiteRingComparison X B)
  intro K₀ hK₀ ⟨e⟩
  obtain ⟨C, ⟨eC⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q K₀
  refine ⟨C, ?_, ⟨(F.mapDerivedCategoryFactors.app C).symm ≪≫
    F.mapDerivedCategory.mapIso eC ≪≫ e⟩⟩
  obtain ⟨T, hT, ⟨eT⟩⟩ := hK₀
  exact ⟨T, hT, ⟨eT ≪≫ eC.symm⟩⟩

private theorem intrinsic_constructible_of_iso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    {M N : pbcModules X (adicLisseConstantRing X B)} (e : M ≅ N)
    (hM : IsConstructibleProEtaleCoefficientModuleSheaf X B M) :
    IsConstructibleProEtaleCoefficientModuleSheaf X B N := by
  obtain ⟨S, hn, hc, hS⟩ := hM
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨V, hV, hmodels⟩ := hS i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := hmodels U f hf
  exact ⟨L, hL, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (S.immersion i)
      (adicLisseConstantRing X B)).mapIso e.symm) ≪≫ eL⟩⟩

private theorem finite_etale_origin_realization
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B]
    (L : ProEtale.FiniteCoefficientEtaleDerivedCategory X B)
    (hL : Etale.DerivedCategory.isBoundedConstructible B X L) :
    ProEtale.isBoundedConstructibleFiniteCoefficient X B
      ((ProEtale.finiteCoefficientRealization X B).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L)) := by
  refine ⟨L, ?_, ⟨?_⟩⟩
  · refine ⟨?_, hL.2⟩
    intro i
    obtain ⟨S, hS⟩ := hL.1 i
    exact ⟨S, S.isConstructible_stratum, hS⟩
  · exact ((Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
      (ProEtale.finiteCoefficientRealization X B)).app L).symm

/-- A single finite-ring complex with bounded intrinsically constructible cohomology
has a bounded constructible etale presentation in the recorded coefficient universe.
The comparison `e` may be any constant-ring presentation isomorphism.

Source: Stacks Project, proetale.tex, Tag 09AL, lemma-compare-constructible-derived;
coefficient transport in step 1 of the local-effectivity argument
(blueprint: lem-weil-pbc-finite-coefficient-derived-origin-presentation).

Proof: transfer K through the exact equivalence from fixed-ring sheaves to the
recorded coefficient modules. Exactness and faithfulness reflect both cohomological
bounds. The single-sheaf intrinsic constructibility comparison identifies the
constructibility hypotheses on its cohomology. Descend each such sheaf and apply
the existing boundedConstructible_of_homology theorem, whose finite truncation
argument assembles a bounded constructible etale source. Convert its finite local
models and its bounds to the recorded essential-image predicate. Realize the source
and compose the derived comparison isomorphisms. Finally the proved helper
finite_presentation_representative extracts a cochain representative by essential
surjectivity of Q and transports it termwise through finiteRingComparison. No
small-ring replacement or derived universe transport is required. -/
theorem finiteCoefficient_constructibleDerived_origin_presentation
    (X : Scheme.{u}) [IsNoetherian X]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : adicLisseConstantRing X B ≅ AdicCoefficients.coefficientRing X B)
    (K : DerivedCategory (pbcModules X (AdicCoefficients.coefficientRing X B)))
    (hconstructible : ∀ q : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf X B
      ((pbcRestrict e.hom).obj ((DerivedCategory.homologyFunctor _ q).obj K)))
    (a b : ℤ) (_hab : a ≤ b)
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := discreteTopology_bot _
    ∃ C : CochainComplex (ProEtale.FiniteCoefficientModules X B) ℤ,
      ProEtale.isBoundedConstructibleFiniteCoefficient X B (DerivedCategory.Q.obj C) ∧
      Nonempty (DerivedCategory.Q.obj
        (((SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison X B).hom).mapHomologicalComplex
            (.up ℤ)).obj C) ≅ K) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot _
  let R := ProEtale.finiteCoefficientRealization X B
  let S := SheafOfModules.restrictScalars
    (AdicCoefficients.finiteRingComparison X B).hom
  have : S.IsEquivalence :=
    coefficientEquivalence_isEquivalence X (AdicCoefficients.finiteRingComparison X B)
  let F := R ⋙ S
  let J := F.mapDerivedCategory.objPreimage K
  let eJ : F.mapDerivedCategory.obj J ≅ K := F.mapDerivedCategory.objObjPreimageIso K
  have hJ : DerivedCategory.TStructure.t.bounded J := by
    apply F.bounded_of_bounded_mapDerivedCategory_obj
    refine ⟨⟨a, (DerivedCategory.isGE_iff _ a).2 ?_⟩,
      ⟨b, (DerivedCategory.isLE_iff _ b).2 ?_⟩⟩
    · intro i hi
      exact (hbounded i (Or.inl hi)).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso eJ)
    · intro i hi
      exact (hbounded i (Or.inr hi)).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso eJ)
  have hH (i : ℤ) : ProEtale.IsConstructible B
      ((DerivedCategory.homologyFunctor _ i).obj J) := by
    apply finiteCoefficient_intrinsic_constructible X B e
    let eH := (F.mapDerivedCategoryHomologyFunctorIso i).app J ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso eJ
    exact intrinsic_constructible_of_iso X B
      ((pbcRestrict e.hom).mapIso eH.symm) (hconstructible i)
  obtain ⟨L, hL, ⟨eL⟩⟩ :=
    origin_boundedConstructible_of_homology B hJ
      (fun i ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B (hH i))
  have hLP : Etale.DerivedCategory.isBoundedConstructible B X L := by
    refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hL.2 i), ?_⟩
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hL.1
    refine ⟨min c d, max c d, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff L c).1 hc i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff L d).1 hd i
        (lt_of_le_of_lt (le_max_right _ _) hi)
  apply finite_presentation_representative X B K
    (R.mapDerivedCategory.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L))
    (finite_etale_origin_realization X B L hLP)
  exact ⟨S.mapDerivedCategory.mapIso (R.mapDerivedCategory.mapIso eL) ≪≫
    (Functor.mapDerivedCategoryCompIso R S).app J ≪≫ eJ⟩

end AlgebraicGeometry.Scheme
