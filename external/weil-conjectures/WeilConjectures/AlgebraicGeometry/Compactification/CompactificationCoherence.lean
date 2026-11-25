/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonComposition
import WeilConjectures.Compactification.CategoryBaseChange

/-!
# Compactification coherence on the witnessed etale-origin domain

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations,
prop-compactification-coherence, order 1485
(blueprint: proposition-construction-independence-rf-shriek).

The candidates and their specified objectwise comparisons are written in the canonical
fixed-scalar presentation of the recorded finite coefficient module categories. The
forgetful functor retains every ambient morphism between the witnessed objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The recorded compact-support candidate restricted to witnessed bounded below
etale-origin objects, in the fixed-scalar presentation used by the recorded refinement
comparison. The coefficient equivalence is the same one as `refinementFixedObject`;
objects, maps, and witnesses are transported canonically, without a new choice of map.
Source: blueprint prop-compactification-coherence, displayed candidates and final scope
paragraph, order 1485 (blueprint: proposition-construction-independence-rf-shriek). -/
def compactificationOriginCandidate (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    RefinementFiniteLevelOrigin l E n hn X ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  etaleOriginForgetful X (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) ⋙
    (refinementCoefficientEquivalence X
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))).inverse ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) c

private theorem etale_properOpen_naturality (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    {L M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (k : L ⟶ M) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map k ≫
        Etale.properOpenComparison Λ f j₁ j₂ h M =
      Etale.properOpenComparison Λ f j₁ j₂ h L ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.map
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.map k) := by
  let A := ModuleCat.{u + 1} Λ
  let J₁ := (Etale.openImmersionLowerShriek A j₁).mapDerivedCategoryPlus
  let J₂ := (Etale.openImmersionLowerShriek A j₂).mapDerivedCategoryPlus
  let R := (Etale.lowerStar A f).rightDerivedFunctorPlus
  let s := Etale.properOpenSection f j₁ j₂ h
  let geom := Etale.properOpenSectionGeometry f j₁ j₂ h
  let : IsOpenImmersion s := geom.1
  let sq : ChosenCartesianSquare (Limits.pullback.fst f j₂)
      (Limits.pullback.snd f j₂) f j₂ :=
    { toCommSq := ⟨Limits.pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  let := Etale.isIso_derivedBaseChangeMapPlus_of_openImmersion Λ f j₂
    (Limits.pullback.fst f j₂) (Limits.pullback.snd f j₂) sq
  let S := (Etale.openImmersionLowerShriek A s).mapDerivedCategoryPlus
  let P := (Etale.lowerStar A (Limits.pullback.snd f j₂)).rightDerivedFunctorPlus
  let e := Etale.extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2 ≪≫
    Functor.isoWhiskerRight (Etale.upperStarIdDerivedPlus A X) S ≪≫
      Functor.leftUnitor S
  let r := Functor.isoWhiskerLeft J₁
    (asIso (Etale.derivedBaseChangeMapPlus A sq.toCommSq))
  let c := (Etale.clopenSectionDirectImage Λ (Limits.pullback.snd f j₂) s geom.2.1
    (Limits.pullback.lift_snd j₁ (𝟙 X) _)).choose
  let theta := r ≪≫ Functor.isoWhiskerRight e P ≪≫ c
  have he (N) : theta.app N = Etale.properOpenIdentification Λ f j₁ j₂ h N := by
    apply Iso.ext
    simp [theta, r, e, c, Etale.properOpenIdentification, J₁, S, P, A,
      Etale.rightDerivedLowerStarPlus, s]
  let a := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j₂
  let t : J₂ ⟶ J₁ ⋙ R :=
    Functor.whiskerRight theta.inv J₂ ≫ Functor.whiskerLeft (J₁ ⋙ R) a.counit
  have ht (N) : t.app N = Etale.properOpenComparison Λ f j₁ j₂ h N := by
    simp only [t, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    change J₂.map (theta.app N).inv ≫ _ = _
    rw [he]
    rfl
  have hn := t.naturality k
  simpa only [ht, Functor.comp_map] using hn

private theorem proEtale_properOpen_plus_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    {L M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (k : L ⟶ M) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.map k) ≫
        (properOpenProEtaleIsoPlus Λ f j₁ j₂ h M).hom =
      (properOpenProEtaleIsoPlus Λ f j₁ j₂ h L).hom ≫
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.map
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.map k)) := by
  let A := ModuleCat.{u + 1} Λ
  let J₁ := (Etale.openImmersionLowerShriek A j₁).mapDerivedCategoryPlus
  let R := (lowerStar A f).rightDerivedFunctorPlus
  let N := (comparisonUpperStar A T₂).mapDerivedCategoryPlus
  let e : (Etale.openImmersionLowerShriek A j₂).mapDerivedCategoryPlus ≅ J₁ ⋙
      (Etale.lowerStar A f).rightDerivedFunctorPlus := NatIso.ofComponents
    (fun L ↦ @asIso _ _ _ _ (Etale.properOpenComparison Λ f j₁ j₂ h L)
      (Etale.isIso_properOpenComparison Λ f j₁ j₂ h L))
    (fun {_ _} k ↦ etale_properOpen_naturality Λ f j₁ j₂ h k)
  let := isIso_comparisonDirectImagePlus Λ f
  let t := (properOpenSiteExtensionIso Λ j₂).symm ≪≫
    Functor.isoWhiskerRight e N ≪≫
    Functor.isoWhiskerLeft J₁
      (asIso (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange f A))) ≪≫
    Functor.isoWhiskerRight (properOpenSiteExtensionIso Λ j₁) R
  have ht (L) : t.app L = properOpenProEtaleIsoPlus Λ f j₁ j₂ h L := by
    apply Iso.ext
    rfl
  have hn := t.hom.naturality k
  simpa only [← Iso.app_hom, ht, Functor.comp_map] using hn

private theorem proEtale_properOpen_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    {L M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (k : L ⟶ M) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map k.hom) ≫
        (properOpenProEtaleIso Λ f j₁ j₂ h M).hom =
      (properOpenProEtaleIso Λ f j₁ j₂ h L).hom ≫
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategory.map
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map k.hom)) := by
  let A := ModuleCat.{u + 1} Λ
  let N := comparisonUpperStar A X
  let J₁ := openImmersionLowerShriek A j₁
  let J₂ := openImmersionLowerShriek A j₂
  let R := lowerStar A f
  let e : N.mapDerivedCategoryPlus ⋙ J₂.mapDerivedCategoryPlus ≅
      N.mapDerivedCategoryPlus ⋙ J₁.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus :=
    NatIso.ofComponents (properOpenProEtaleIsoPlus Λ f j₁ j₂ h)
    (fun {_ _} k ↦ proEtale_properOpen_plus_naturality Λ f j₁ j₂ h k)
  let t := Functor.isoWhiskerRight N.mapDerivedCategoryPlusCompatibility.symm
      J₂.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft N.mapDerivedCategoryPlus
      J₂.mapDerivedCategoryPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight e DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft (N.mapDerivedCategoryPlus ⋙ J₁.mapDerivedCategoryPlus)
      R.rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft N.mapDerivedCategoryPlus J₁.mapDerivedCategoryPlusCompatibility)
      R.rightDerivedFunctor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight N.mapDerivedCategoryPlusCompatibility J₁.mapDerivedCategory)
      R.rightDerivedFunctor
  have ht (L) : t.app L = properOpenProEtaleIso Λ f j₁ j₂ h L := by
    apply Iso.ext
    rfl
  have hn := t.hom.naturality k
  simpa only [← Iso.app_hom, ht, Functor.comp_map, ObjectProperty.ι_map] using hn

private theorem refinement_properOpen_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁ ⟶ c₂) (O P : EtaleOriginDerivedCategory X Λ) (k : O ⟶ P) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₂.i).mapDerivedCategory.map
        ((refinementCoefficientEquivalence X Λ).inverse.map
          ((etaleOriginForgetful X Λ).map k)) ≫ (refinementProperOpenIso Λ r P).hom =
      (refinementProperOpenIso Λ r O).hom ≫
        (lowerStar (ModuleCat.{u + 1} Λ) r.hom).rightDerivedFunctor.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.map
            ((refinementCoefficientEquivalence X Λ).inverse.map
              ((etaleOriginForgetful X Λ).map k))) := by
  let A := ModuleCat.{u + 1} Λ
  let N := (comparisonUpperStar A X).mapDerivedCategory
  let J₁ := (openImmersionLowerShriek A c₁.i).mapDerivedCategory
  let J₂ := (openImmersionLowerShriek A c₂.i).mapDerivedCategory
  let R := (lowerStar A r.hom).rightDerivedFunctor
  let q := refinementFixedWitnessIso X Λ O
  let q' := refinementFixedWitnessIso X Λ P
  let t : refinementFixedObject X Λ O ⟶ refinementFixedObject X Λ P :=
    (refinementCoefficientEquivalence X Λ).inverse.map
    ((etaleOriginForgetful X Λ).map k)
  obtain ⟨h, hh⟩ :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map O.2.L.obj P.2.L.obj
      P.2.L.property).2 (q.hom ≫ t ≫ q'.inv)
  let h' : O.2.L ⟶ P.2.L := ObjectProperty.homMk h
  have hnat := proEtale_properOpen_naturality Λ r.hom c₁.i c₂.i r.i_hom h'
  change J₂.map (N.map h) ≫ _ = _ ≫ R.map (J₁.map (N.map h)) at hnat
  change N.map h = q.hom ≫ t ≫ q'.inv at hh
  have ht : t ≫ q'.inv = q.inv ≫ N.map h := by
    rw [hh]
    simp
  have ht' : q.hom ≫ t = N.map h ≫ q'.hom := by
    rw [hh]
    simp [Category.assoc]
  change J₂.map t ≫ _ = _ ≫ R.map (J₁.map t)
  change J₂.map t ≫ (J₂.map q'.inv ≫ _ ≫ R.map (J₁.map q'.hom)) =
    (J₂.map q.inv ≫ _ ≫ R.map (J₁.map q.hom)) ≫ R.map (J₁.map t)
  rw [← J₂.map_comp_assoc, ht, J₂.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  congr 1
  rw [← R.map_comp, ← J₁.map_comp, ← ht', J₁.map_comp, R.map_comp]

private theorem composite_inverse_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P₁ P₀ : C ⥤ E) (R : C ⥤ D) (P₂ : D ⥤ E)
    (e₁ : P₁ ≅ P₀) (e₂ : P₀ ≅ R ⋙ P₂)
    {A B : C} {A' B' : D} (a : A' ≅ R.obj A) (b : B' ≅ R.obj B)
    (f : A ⟶ B) (g : A' ⟶ B') (h : g ≫ b.hom = a.hom ≫ R.map f) :
    P₁.map f ≫ ((e₁.app B) ≪≫ (e₂.app B) ≪≫ P₂.mapIso b.symm).hom =
      ((e₁.app A) ≪≫ (e₂.app A) ≪≫ P₂.mapIso a.symm).hom ≫ P₂.map g := by
  have hi : R.map f ≫ b.inv = a.inv ≫ g := by
    apply (cancel_epi a.hom).mp
    rw [← Category.assoc, ← h]
    simp [Category.assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc, e₁.hom.naturality f]
  simp only [Category.assoc]
  rw [e₂.hom.naturality_assoc f]
  simp only [Functor.comp_map, ← P₂.map_comp, hi]

private theorem refinement_comparison_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁ ⟶ c₂) (O P : EtaleOriginDerivedCategory X Λ) (k : O ⟶ P) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₁).map
        ((refinementCoefficientEquivalence X Λ).inverse.map
          ((etaleOriginForgetful X Λ).map k)) ≫ (refinementComparisonAtWitness Λ r P).hom =
      (refinementComparisonAtWitness Λ r O).hom ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₂).map
          ((refinementCoefficientEquivalence X Λ).inverse.map
            ((etaleOriginForgetful X Λ).map k)) := by
  let A := ModuleCat.{u + 1} Λ
  let J₁ := (openImmersionLowerShriek A c₁.i).mapDerivedCategory
  let J₂ := (openImmersionLowerShriek A c₂.i).mapDerivedCategory
  let R := (lowerStar A r.hom).rightDerivedFunctor
  let P₁ := (lowerStar A c₁.g).rightDerivedFunctor
  let P₀ := (lowerStar A (r.hom ≫ c₂.g)).rightDerivedFunctor
  let P₂ := (lowerStar A c₂.g).rightDerivedFunctor
  let t : refinementFixedObject X Λ O ⟶ refinementFixedObject X Λ P :=
    (refinementCoefficientEquivalence X Λ).inverse.map
      ((etaleOriginForgetful X Λ).map k)
  exact composite_inverse_naturality P₁ P₀ R P₂
    (eqToIso (congrArg (fun q ↦ (lowerStar A q).rightDerivedFunctor) r.hom_g.symm))
    (finiteDirectImageComposition Λ r.hom c₂.g)
    (refinementProperOpenIso Λ r O) (refinementProperOpenIso Λ r P)
    (J₁.map t) (J₂.map t) (refinement_properOpen_naturality Λ r O P k)

private theorem span_precomp {C D : Type*} [Category* C] [Category* D]
    (F : C → D) (theta : ∀ {a b : C}, (a ⟶ b) → (F a ≅ F b))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c),
      theta (r ≫ s) = theta r ≪≫ theta s)
    {a b d e : C} (r : d ⟶ a) (s : d ⟶ b) (q : e ⟶ d) :
    (theta r).symm ≪≫ theta s = (theta (q ≫ r)).symm ≪≫ theta (q ≫ s) := by
  rw [hcomp, hcomp]
  ext
  simp

private theorem span_independent {C D : Type*} [Category* C] [Category* D]
    [IsCofiltered C] (F : C → D)
    (theta : ∀ {a b : C}, (a ⟶ b) → (F a ≅ F b))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c),
      theta (r ≫ s) = theta r ≪≫ theta s)
    {a b d e : C} (r : d ⟶ a) (s : d ⟶ b) (r' : e ⟶ a) (s' : e ⟶ b) :
    (theta r).symm ≪≫ theta s = (theta r').symm ≪≫ theta s' := by
  obtain ⟨z, q, q', h₁, h₂⟩ := IsCofiltered.bowtie r r' s s'
  rw [span_precomp F theta hcomp r s q, span_precomp F theta hcomp r' s' q', h₁, h₂]

private theorem cofiltered_comparisons {C D : Type*} [Category* C] [Category* D]
    [IsCofiltered C] (F : C → D)
    (theta : ∀ {a b : C}, (a ⟶ b) → (F a ≅ F b))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c),
      theta (r ≫ s) = theta r ≪≫ theta s) :
    ∃ comparison : ∀ a b : C, F a ≅ F b,
      (∀ (a b d : C) (r : d ⟶ a) (s : d ⟶ b),
        comparison a b = (theta r).symm ≪≫ theta s) ∧
      (∀ a b c : C, comparison a b ≪≫ comparison b c = comparison a c) := by
  let comparison (a b : C) : F a ≅ F b :=
    (theta (IsCofiltered.minToLeft a b)).symm ≪≫
      theta (IsCofiltered.minToRight a b)
  have h (a b d : C) (r : d ⟶ a) (s : d ⟶ b) :
      comparison a b = (theta r).symm ≪≫ theta s :=
    span_independent F theta hcomp _ _ r s
  refine ⟨comparison, h, ?_⟩
  intro a b c
  let d := IsCofiltered.min (IsCofiltered.min a b) c
  let r : d ⟶ a := IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft a b
  let s : d ⟶ b := IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight a b
  let t : d ⟶ c := IsCofiltered.minToRight _ _
  rw [h a b d r s, h b c d s t, h a c d r t]
  ext
  simp

/-- The canonical refinement maps form natural isomorphisms, are unital and transitive,
and determine comparison isomorphisms independently of the common refinement and its
arrows. Every finite family has a common refinement, including the empty family; the
pairwise comparisons satisfy the cocycle law. The normalization by the recorded
`refinementComparisonIsomorphism` specifies the proper-composition map followed by
proper pushforward of the inverse proper-open map, rather than an arbitrary isomorphism.
The domain consists of bounded below etale-origin triples, with all ambient morphisms.

Source: blueprint prop-compactification-coherence, statement and proof paragraphs 1--4,
order 1485 (blueprint: proposition-construction-independence-rf-shriek).

Proof plan:
1. Finite type over the field makes X, Y and every proper compactification Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Refinements are proper, hence qcqs
   (definition-compactification-refinement and lem-weil-pbc-proper-fp-permanence).
2. In the defining etale proper-open map, derived open restriction, extension-zero
   base change, and restriction to the clopen section are natural. Compose their
   naturality squares and invert the restriction comparison; the adjunction counit
   gives naturality of the specified etale proper-open map
   (proposition-construction-independence-rf-shriek--7,
   proposition-construction-independence-rf-shriek--7,
   proposition-extension-zero-restriction-closed-subscheme--11,
   proposition-construction-independence-rf-shriek--7).
3. Transport this square using the natural extension-zero site comparison and the
   direct-image comparison; exactness descends the termwise construction to complexes
   and roofs (proposition-comparison-immersions--1,
   lem-weil-pbc-extension-by-zero-exact, def-sf-comparison-derived-pullback,
   theorem-comparison-direct-images--1, proposition-construction-independence-rf-shriek--7).
4. Conjugate by the retained alpha. Full faithfulness of comparison pullback lifts
   every ambient map between witnessed objects to an etale map, proving naturality
   for all domain morphisms. The identity map between two witnesses gives witness
   independence (def-sf-etale-origin-subcategory, theorem-bounded-below-cohomology-comparison).
5. Invert that proper-open isomorphism and apply the proper direct image after its
   canonical compositor. This is precisely refinementComparisonIsomorphism; naturality
   of its two factors gives theta (def-sf-refinement-comparison-isomorphism,
   lem-weil-derived-direct-image-composition, proposition-construction-independence-rf-shriek).
6. The proper-open identity and composition laws survive witness conjugation: cancel
   the intermediate witness maps and move the compositor past alpha by naturality.
   Associativity of the direct-image compositor then gives theta_id and theta_comp
   (proposition-construction-independence-rf-shriek--7,
   lem-weil-derived-direct-image-composition).
7. For d mapping to c1 and c2, put T12 = theta(d,c1)^(-1) followed by theta(d,c2).
   Transitivity cancels theta for any further refinement of d.
8. For two choices d,d', first take a common refinement and successively equalize
   the two resulting parallel arrows to c1 and to c2. The first equality survives
   the second precomposition. Step 7 identifies the resulting comparisons, including
   different choices of arrows (prop-compactification-refinement).
9. Use the finite-family clause of the same cofilteredness theorem. A single common
   refinement for three objects cancels the middle theta and proves the cocycle law.
   Nonemptiness handles the empty family and identities handle a singleton. All these
   equations are on the witnessed domain, never on arbitrary pro-etale complexes. -/
theorem compactification_coherence (K₀ : Type u) [Field K₀]
    (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : K₀))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ theta : ∀ (c₁ c₂ : Compactification f) (_r : c₁ ⟶ c₂),
        compactificationOriginCandidate l E n hn c₁ ≅
          compactificationOriginCandidate l E n hn c₂,
      (∀ (c₁ c₂ : Compactification f) (r : c₁ ⟶ c₂)
          (O : RefinementFiniteLevelOrigin l E n hn X),
        (theta c₁ c₂ r).app O =
          refinementComparisonIsomorphism K₀ l hl E n hn f r O) ∧
      (∀ c : Compactification f, theta c c (𝟙 c) = Iso.refl _) ∧
      (∀ (c₁ c₂ c₃ : Compactification f) (r : c₁ ⟶ c₂) (s : c₂ ⟶ c₃),
        theta c₁ c₃ (r ≫ s) = theta c₁ c₂ r ≪≫ theta c₂ c₃ s) ∧
      (∀ (m : ℕ) (c : Fin m → Compactification f),
        ∃ d : Compactification f, ∀ i : Fin m, Nonempty (d ⟶ c i)) ∧
      ∃ comparison : ∀ c₁ c₂ : Compactification f,
          compactificationOriginCandidate l E n hn c₁ ≅
            compactificationOriginCandidate l E n hn c₂,
        (∀ (c₁ c₂ d : Compactification f) (r₁ : d ⟶ c₁) (r₂ : d ⟶ c₂),
          comparison c₁ c₂ = (theta d c₁ r₁).symm ≪≫ theta d c₂ r₂) ∧
        (∀ c₁ c₂ c₃ : Compactification f,
          comparison c₁ c₂ ≪≫ comparison c₂ c₃ = comparison c₁ c₃)  := by
  classical
  have : IsCofiltered (Compactification f) :=
    Compactification.isCofiltered_of_field (X ↘ Spec (.of K₀))
      (Y ↘ Spec (.of K₀)) f (by simp)
  have hnat : ∀ (c₁ c₂ : Compactification f) (r : c₁ ⟶ c₂)
      (O P : RefinementFiniteLevelOrigin l E n hn X) (k : O ⟶ P),
      (compactificationOriginCandidate l E n hn c₁).map k ≫
          (refinementComparisonIsomorphism K₀ l hl E n hn f r P).hom =
        (refinementComparisonIsomorphism K₀ l hl E n hn f r O).hom ≫
          (compactificationOriginCandidate l E n hn c₂).map k := by
    let : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    let : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
    let : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
      discreteTopology_bot _
    intro c₁ c₂ r O P k
    exact refinement_comparison_naturality
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) r O P k
  have hcomponent : ∀ (c₁ c₂ c₃ : Compactification f)
      (r : c₁ ⟶ c₂) (s : c₂ ⟶ c₃) (O : RefinementFiniteLevelOrigin l E n hn X),
      refinementComparisonIsomorphism K₀ l hl E n hn f (r ≫ s) O =
        refinementComparisonIsomorphism K₀ l hl E n hn f r O ≪≫
          refinementComparisonIsomorphism K₀ l hl E n hn f s O := by
    let : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    let : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
    let : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
      discreteTopology_bot _
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K₀))
    have : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K₀))
    intro c₁ c₂ c₃ r s O
    have : IsLocallyNoetherian c₁.Z := LocallyOfFiniteType.isLocallyNoetherian c₁.g
    have : CompactSpace c₁.Z := QuasiCompact.compactSpace_of_compactSpace c₁.g
    have : IsNoetherian c₁.Z := ⟨⟩
    have : IsLocallyNoetherian c₂.Z := LocallyOfFiniteType.isLocallyNoetherian c₂.g
    have : CompactSpace c₂.Z := QuasiCompact.compactSpace_of_compactSpace c₂.g
    have : IsNoetherian c₂.Z := ⟨⟩
    have : IsLocallyNoetherian c₃.Z := LocallyOfFiniteType.isLocallyNoetherian c₃.g
    have : CompactSpace c₃.Z := QuasiCompact.compactSpace_of_compactSpace c₃.g
    have : IsNoetherian c₃.Z := ⟨⟩
    exact refinementComparisonAtWitness_comp
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) r s O
  let theta (c₁ c₂ : Compactification f) (r : c₁ ⟶ c₂) :
      compactificationOriginCandidate l E n hn c₁ ≅
        compactificationOriginCandidate l E n hn c₂ :=
    NatIso.ofComponents (refinementComparisonIsomorphism K₀ l hl E n hn f r)
      (fun {O P} k ↦ hnat c₁ c₂ r O P k)
  have hcomp (c₁ c₂ c₃ : Compactification f) (r : c₁ ⟶ c₂) (s : c₂ ⟶ c₃) :
      theta c₁ c₃ (r ≫ s) = theta c₁ c₂ r ≪≫ theta c₂ c₃ s := by
    apply Iso.ext
    ext O
    simpa [theta] using congrArg Iso.hom (hcomponent c₁ c₂ c₃ r s O)
  refine ⟨theta, ?_, ?_, hcomp, ?_, ?_⟩
  · intro c₁ c₂ r O
    rfl
  · intro c
    apply Iso.ext
    apply (cancel_epi (theta c c (𝟙 c)).hom).mp
    have h := congrArg Iso.hom (hcomp c c c (𝟙 c) (𝟙 c))
    simpa only [Category.id_comp, Iso.trans_hom, Iso.refl_hom, Category.comp_id]
      using h.symm
  · intro m c
    obtain ⟨d, hd⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image c)
    exact ⟨d, fun i ↦ hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  · exact cofiltered_comparisons (compactificationOriginCandidate l E n hn)
      (fun {_ _} r ↦ theta _ _ r) (fun {_ _ _} r s ↦ hcomp _ _ _ r s)

end AlgebraicGeometry.ProEtale
