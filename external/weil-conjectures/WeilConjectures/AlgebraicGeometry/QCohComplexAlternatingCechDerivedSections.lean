/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.KInjectiveAlternatingCechAugmentationQuasiIso

/-! # Alternating Čech cochains compute derived sections of quasi-coherent complexes

Source: Stacks, Cohomology, Lemma 08C2 and lemma-alternating-cech-complex-complex;
Cohomology of Schemes, Lemma 01XB; Perfect, Lemma 08D2
(blueprint: lem-sc-qcoh-complex-alternating-cech-derived-sections).
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def sectionsDerivedUnit
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{v}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor :=
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  (Functor.isoWhiskerLeft (S.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso D)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      S.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      S.rightDerivedFunctor).hom

private lemma sectionsDerivedUnit_iso
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{v}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [J.IsKInjective] :
    (sectionsDerivedUnit X).app J =
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorObjQIso J).inv := by
  simp [sectionsDerivedUnit, Functor.rightDerivedFunctorObjQIso]

/-- The canonical comparison exists, every comparison is invertible, and comparisons are
natural among complexes of quasi-coherent modules. No boundedness of F or G is assumed.
Source: Stacks, Cohomology, lemma-alternating-cech-complex-complex, Lemma 08C2;
Cohomology of Schemes, Lemma 01XB; Perfect, Lemma 08D2
(blueprint: lem-sc-qcoh-complex-alternating-cech-derived-sections).

Proof:
1. Insertion of a cover index contracts the augmented alternating Čech complex locally.
   The finite cover bounds the Čech direction, even for an unbounded coefficient complex.
2. Each nonempty intersection is affine. The affine quasi-coherent derived equivalence
   (lem-pc-affine-qcoh-derived-equivalence) and acyclic section comparison
   (lem-sc-qcoh-acyclic-derived-sections-comparison) identify its termwise sections with
   derived sections, naturally in the complex and restriction maps.
3. Take a functorial K-injective resolution with injective terms
   (prop-pur-kinjective-resolutions-exist). K-injective restriction to opens
   (lem-sc-derived-k-injective-restrict-open) and the derived-functor computation
   (def-pc-ringed-spaces-derived-direct-image) show that the maps of intersection section
   complexes are quasi-isomorphisms. Filter the Čech totals by Čech degree. Their finite
   graded pieces are shifted products of these quasi-isomorphisms. Spectral comparison
   (thm-sp-spectral-object-yields, lem-sp-page-induction) and finite filtration induction
   (lem-sp-finite-filtration-induction) show the induced map of totals is a quasi-isomorphism.
4. For the injective-term resolution, injective Čech acyclicity
   (lem-weil-pbc-module-injective-open-cover-cech-acyclic) and alternating comparison
   (lem-pc-alternating-cech-computes) make the augmented section rows exact. The finite
   staircase chase makes the cone of the section-to-total augmentation acyclic.
   Invert this augmentation in the derived category and compose with the map of totals.
5. Resolution comparisons between K-injectives are unique up to homotopy
   (lem-weil-pbc-kinjective-hom-derived, lem-sc-kinjective-quasi-iso-comparison). Additive
   Čech totalization preserves homotopies; this gives the equation defining every
   comparison, its resolution independence, and the naturality square. In particular,
   compare any K-injective resolution with the injective-term resolution from step 3.
   Their comparison is a homotopy equivalence, so sections and Čech totalization carry
   it to isomorphisms after localization. Naturality transports the canonical equation
   to every K-injective resolution, without requiring its terms to be injective. The same
   construction gives zero total and derived sections for the empty cover or zero complex.
-/
theorem qcoh_complex_alternating_cech_derived_sections
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k)))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{v}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    (∃ β : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F), IsAlternatingCechDerivedComparison U F β) ∧
    (∀ β : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F), IsAlternatingCechDerivedComparison U F β → IsIso β) ∧
    (∀ (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (_hG : ∀ n : ℤ, (G.X n).IsQuasicoherent) (g : F ⟶ G)
      (βF : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj F))
      (βG : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj G) ⟶
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj G)),
      IsAlternatingCechDerivedComparison U F βF →
      IsAlternatingCechDerivedComparison U G βG →
      DerivedCategory.Q.map ((alternatingCechTotalFunctor U).map g) ≫ βG =
        βF ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
          (DerivedCategory.Q.map g)) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let A := S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let B := alternatingCechTotalFunctor U ⋙ DerivedCategory.Q
  let D := DerivedCategory.Q ⋙ S.rightDerivedFunctor
  let a : A ⟶ B := Functor.whiskerRight (alternatingCechAugmentation U) DerivedCategory.Q
  let b : A ⟶ D := sectionsDerivedUnit X
  let ai := Functor.whiskerLeft I a
  let d := Functor.whiskerRight η D
  have hη (K : CochainComplex C ℤ) : QuasiIso (η.app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
  have hai : IsIso ai := by
    have (K : CochainComplex C ℤ) : IsIso (ai.app K) := by
      change IsIso (DerivedCategory.Q.map ((alternatingCechAugmentation U).app (I.obj K)))
      have := kInjective_alternatingCech_augmentation_quasiIso X r U hU (I.obj K)
      infer_instance
    exact NatIso.isIso_of_isIso_app ai
  have haI (K : CochainComplex C ℤ) : IsIso (a.app (I.obj K)) := by
    change IsIso (ai.app K)
    infer_instance
  have hd : IsIso d := by
    have (K : CochainComplex C ℤ) : IsIso (d.app K) := by
      have := hη K
      change IsIso (S.rightDerivedFunctor.map (DerivedCategory.Q.map (η.app K)))
      infer_instance
    exact NatIso.isIso_of_isIso_app d
  -- Invert the augmentation on the functorial resolution and then undo RΓ(Qη).
  let β : B ⟶ D := Functor.whiskerRight η B ≫ inv ai ≫
    Functor.whiskerLeft I b ≫ inv d
  -- The comparison extends the ordinary-to-derived sections unit on every complex.
  have hab (K : CochainComplex C ℤ) : a.app K ≫ β.app K = b.app K := by
    have := haI K
    apply (cancel_mono (d.app K)).mp
    simp only [β, NatTrans.comp_app, NatIso.isIso_inv_app]
    change (a.app K ≫
        (B.map (η.app K) ≫ inv (a.app (I.obj K)) ≫ b.app (I.obj K) ≫ inv (d.app K))) ≫
          d.app K = b.app K ≫ d.app K
    calc
      _ = (a.app K ≫ B.map (η.app K)) ≫ inv (a.app (I.obj K)) ≫
          b.app (I.obj K) := by simp [Category.assoc]
      _ = (A.map (η.app K) ≫ a.app (I.obj K)) ≫ inv (a.app (I.obj K)) ≫
          b.app (I.obj K) := by rw [a.naturality]; rfl
      _ = A.map (η.app K) ≫ b.app (I.obj K) := by simp [Category.assoc]
      _ = b.app K ≫ d.app K := b.naturality (η.app K)
  have hcomp (K : CochainComplex C ℤ) : IsAlternatingCechDerivedComparison U K (β.app K) := by
    intro J _ i _
    have haJ : IsIso (a.app J) := by
      have := kInjective_alternatingCech_augmentation_quasiIso X r U hU J
      change IsIso (DerivedCategory.Q.map ((alternatingCechAugmentation U).app J))
      infer_instance
    have hbJ : b.app J = (S.rightDerivedFunctorObjQIso J).inv :=
      sectionsDerivedUnit_iso X J
    have he : β.app J ≫ (S.rightDerivedFunctorObjQIso J).hom ≫ a.app J = 𝟙 _ := by
      apply (cancel_epi (a.app J)).mp
      simp only [← Category.assoc, hab J, hbJ, Iso.inv_hom_id,
        Category.id_comp, Category.comp_id]
    change β.app K ≫ D.map i ≫ (S.rightDerivedFunctorObjQIso J).hom ≫ a.app J = B.map i
    rw [← Category.assoc, ← Category.assoc, ← β.naturality i]
    simp only [Category.assoc, he, Category.comp_id]
  have hβiso : IsIso (β.app F) := by
    have := hη F
    have := qcoh_alternatingCech_resolution_quasiIso X r U hU hAffine F (I.obj F) hF
      (η.app F)
    have hl : IsIso ((Functor.whiskerRight η B).app F) := by
      change IsIso (DerivedCategory.Q.map ((alternatingCechTotalFunctor U).map (η.app F)))
      infer_instance
    have hb : IsIso ((Functor.whiskerLeft I b).app F) := by
      change IsIso ((sectionsDerivedUnit X).app (I.obj F))
      rw [sectionsDerivedUnit_iso]
      infer_instance
    dsimp only [β, NatTrans.comp_app]
    infer_instance
  -- One resolution equation determines the comparison, since its three factors are iso.
  have unique (K : CochainComplex C ℤ)
      (γ : B.obj K ⟶ D.obj K) (hγ : IsAlternatingCechDerivedComparison U K γ) :
      γ = β.app K := by
    have := hη K
    have he := hγ (I.obj K) (η.app K)
    have heβ := hcomp K (I.obj K) (η.app K)
    have ha := haI K
    have : IsIso (D.map (η.app K)) := by
      change IsIso (S.rightDerivedFunctor.map (DerivedCategory.Q.map (η.app K)))
      infer_instance
    apply (cancel_mono (D.map (η.app K))).mp
    apply (cancel_mono ((S.rightDerivedFunctorObjQIso (I.obj K)).hom)).mp
    apply (cancel_mono (a.app (I.obj K))).mp
    simpa only [a, D, S, Functor.comp_map, Functor.whiskerRight_app, Category.assoc]
      using he.trans heβ.symm
  refine ⟨⟨β.app F, hcomp F⟩, ?_, ?_⟩
  · intro γ hγ
    rw [unique F γ hγ]
    exact hβiso
  · intro G _ g βF βG hβF hβG
    rw [unique F βF hβF, unique G βG hβG]
    exact β.naturality g

end AlgebraicGeometry
