/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorAssociatorModelSquare

/-! # Representative constraints for exact ringed tensor comparison

Source: Stacks Project, Tags 0FPT, 06YU and 0G7D
(blueprint: lem-sf-ringed-forget-tensor-associator-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep the chosen internal-Hom and localization constructions behind their APIs.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite SheafOfModules.monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

private theorem left_square {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ X' ⊗ Y') (j' : W' ⟶ V' ⊗ Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ j') :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      eW ≫ j' ≫ (i' ▷ Z') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (V, Z)) (Y := (X ⊗ Y, Z)) (i, 𝟙 Z)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, tensorHom_id] at hn
  calc
    _ = F.map j ≫ μ.hom.app (V, Z) ≫
        ((F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY)) ⊗ₘ eZ) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (V, Z) ≫ ((eV ≫ i') ⊗ₘ eZ) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ)) ≫ (i' ▷ Z') := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

private theorem right_square {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ Y' ⊗ Z') (j' : W' ⟶ X' ⊗ V')
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ j') :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      eW ≫ j' ≫ (X' ◁ i') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (X, V)) (Y := (X, Y ⊗ Z)) (𝟙 X, i)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, id_tensorHom] at hn
  calc
    _ = F.map j ≫ μ.hom.app (X, V) ≫
        (eX ⊗ₘ (F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ))) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← id_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ (eV ≫ i')) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV)) ≫ (X' ◁ i') := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

private theorem left_model_square {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' I K O : A}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (t : V' ⟶ I) (s : W' ⟶ K) (q : K ⟶ O)
    (i' : I ⟶ X' ⊗ Y') (j₀ : K ⟶ V' ⊗ Z') (j' : O ⟶ I ⊗ Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ t ≫ i')
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ s ≫ j₀)
    (hn : q ≫ j' = j₀ ≫ (t ▷ Z')) :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      (eW ≫ s ≫ q) ≫ (j' ≫ (i' ▷ Z')) := by
  rw [left_square F μ i j eX eY eZ eV eW (t ≫ i') (s ≫ j₀) hi hj]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← reassoc_of% hn]

private theorem right_model_square {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' I K O : A}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (t : V' ⟶ I) (s : W' ⟶ K) (q : K ⟶ O)
    (i' : I ⟶ Y' ⊗ Z') (j₀ : K ⟶ X' ⊗ V') (j' : O ⟶ X' ⊗ I)
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ t ≫ i')
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ s ≫ j₀)
    (hn : q ≫ j' = j₀ ≫ (X' ◁ t)) :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      (eW ≫ s ≫ q) ≫ (j' ≫ (X' ◁ i')) := by
  rw [right_square F μ i j eX eY eZ eV eW (t ≫ i') (s ≫ j₀) hi hj]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hn]

private theorem associativity_transport
    {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (l : V ≅ (X ⊗ Y) ⊗ Z) (r : W ≅ X ⊗ (Y ⊗ Z)) (a : V ⟶ W)
    (l' : V' ⟶ (X' ⊗ Y') ⊗ Z') (r' : W' ⟶ X' ⊗ (Y' ⊗ Z')) (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hB : l.hom ≫ (α_ X Y Z).hom = a ≫ r.hom)
    (hA : l' ≫ (α_ X' Y' Z').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
      (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a') :
    F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  apply (cancel_epi (F.map l.hom)).1
  apply (cancel_mono (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom))).1
  calc
    _ = F.map a ≫ F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) := by
      rw [← F.map_comp_assoc, hB, F.map_comp]
      simp only [Category.assoc]
    _ = F.map a ≫ eW ≫ r' := by rw [hR]
    _ = eV ≫ a' ≫ r' := by rw [reassoc_of% hC]
    _ = eV ≫ l' ≫ (α_ X' Y' Z').hom := by rw [hA]
    _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) ≫
          (α_ X' Y' Z').hom := by rw [reassoc_of% hL]
    _ = _ := by
      erw [associator_naturality]
      simp only [Category.assoc]
      rfl

private theorem tensor_associativity_of_whiskers
    {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (X Y Z : B)
    (h : F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom) :
    F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (𝟙 (F.obj X) ⊗ₘ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ⊗ₘ 𝟙 (F.obj Z)) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  simpa only [id_tensorHom, tensorHom_id] using h

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

private theorem coefficient_total_eq :
    coefficientTotalTensor.{r, c, v} J R = SheafOfModules.KFlatTotalTensorModel.total R := by
  rfl

private theorem ringed_tensor_both_naturality
    [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
    (T : CoefficientTensorModels.{r, c, v, wb} J R S)
    (β : @SymmetricCategory _ _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, r, wb} J R S T β)
    (P Q P' Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hP' : P'.IsKFlatIndependentCoefficients) (hQ' : Q'.IsKFlatIndependentCoefficients)
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map (f, g)) ≫
        (T.iso J R S P' Q' hP' hQ').hom =
      (T.iso J R S P Q hP hQ).hom ≫
        S.tensor.map (DerivedCategory.Q.map f, DerivedCategory.Q.map g) := by
  have h := coh.tensorIso_naturality P Q P' Q' (Or.inl hP) (Or.inl hP') f g
  rw [coh.tensorIso_both P Q hP hQ, coh.tensorIso_both P' Q' hP' hQ'] at h
  exact h

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

attribute [local irreducible] coefficientTotalTensor tensorSummand

include cB cA
-- Preserve the original instance assumptions in the public declaration.
set_option linter.unusedSectionVars false
/-- Associativity on the image of flat-term K-flat representatives.
This only concerns three specified complexes, not arbitrary derived objects, and
constructs neither a unit comparison nor any other structural constraint.

Source: Stacks Project, sites-cohomology.tex, Tag 0FPT, via Tag 06YU;
step 2 of lem-sf-ringed-forget-tensor-coherence
(blueprint: lem-sf-ringed-forget-tensor-associator-representatives).

Proof: total tensors of the three complexes have flat terms and are K-flat by
lem-pur-kflat-total-tensor-model, so the given representative square applies to
both inner pairs and both outer pairs. Rewrite both derived associators by their
associator_model equations, replacing tensorIso by T.iso using tensorIso_both.
Naturality of T.iso and of the exact-functor localization factor moves the four
chain comparison maps next to these associators. Cancel the resulting model
isomorphisms. It remains to compare the two total-complex maps. Precompose with
the inverse outer comparison and restrict to each triple coproduct summand.
The summand hypothesis and naturality of the underived comparison identify the
two restrictions with u.coherence.associativity. The structural model maps have
these same restrictions: detect equality using the sheafification universal
property and local pure-tensor generators, then the coproduct universal property.
Apply localization and undo the cancellations. No claim about generation by
global pure tensors is used. -/
theorem ringed_forget_tensor_associator_representatives
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom)
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (hQ : Q.IsKFlatIndependentCoefficients)
    (fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p))
    (hN : N.IsKFlatIndependentCoefficients)
    (fN : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (N.X p)) :
    U.mapDerivedCategory.map (SB.monoidal.associator (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj N)).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P,
          SB.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            U.mapDerivedCategory.obj
              (SB.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N))))
          (Y := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            SA.tensor.obj (U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q),
              U.mapDerivedCategory.obj (DerivedCategory.Q.obj N))))
          (𝟙 _, μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) =
      μ.hom.app (SB.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
        DerivedCategory.Q.obj N) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj
            (SB.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)),
              U.mapDerivedCategory.obj (DerivedCategory.Q.obj N)))
          (Y := (SA.tensor.obj (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)),
              U.mapDerivedCategory.obj (DerivedCategory.Q.obj N)))
          (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q), 𝟙 _) ≫
        (SA.monoidal.associator (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
          (U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q))
          (U.mapDerivedCategory.obj (DerivedCategory.Q.obj N))).hom := by
  let := SB.monoidal
  let := SA.monoidal
  apply tensor_associativity_of_whiskers U.mapDerivedCategory μ
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj N)
  let V := U.mapHomologicalComplex (.up ℤ)
  let B := coefficientTotalTensor.{r, c, v} J R
  let A := coefficientTotalTensor.{s, d, vd} J' R'
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQ := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ
  have hQN := coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN
  have fPQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (PQ.X i) := by
    dsimp only [PQ, B]
    rw [coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R P Q hP hQ fP fQ).2.1
  have fQN : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (QN.X i) := by
    dsimp only [QN, B]
    rw [coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R Q N hQ hN fQ fN).2.1
  have hUP := (hU P hP fP).1
  have hUQ := (hU Q hQ fQ).1
  have hUN := (hU N hN fN).1
  have hUPQ := (hU PQ hPQ fPQ).1
  have hUQN := (hU QN hQN fQN).1
  have hAPQ := coefficientTotalTensor_isKFlat.{s, d, vd} J' R' (V.obj P) (V.obj Q) hUP hUQ
  have hAQN := coefficientTotalTensor_isKFlat.{s, d, vd} J' R' (V.obj Q) (V.obj N) hUQ hUN
  obtain ⟨aB, haB, heB⟩ := cB.associator_model P Q N hP hQ hN
  obtain ⟨aA, haA, heA⟩ := cA.associator_model (V.obj P) (V.obj Q) (V.obj N) hUP hUQ hUN
  have hc : V.map aB.hom ≫ chain.hom.app (P, QN) ≫
        A.map (X := (V.obj P, V.obj QN))
          (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
          (𝟙 (V.obj P), chain.hom.app (Q, N)) =
      chain.hom.app (PQ, N) ≫
        A.map (X := (V.obj PQ, V.obj N))
          (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
          (chain.hom.app (P, Q), 𝟙 (V.obj N)) ≫ aA.hom := by
    exact ringed_associator_model_square J R J' R' U u chain summand P Q N aB aA haB haA
  rw [show cB.tensorIso PQ N (Or.inr hN) = TB.iso J R SB PQ N hPQ hN from
      cB.tensorIso_both PQ N hPQ hN,
    cB.tensorIso_both P QN hP hQN] at heB
  rw [show cA.tensorIso (A.obj (V.obj P, V.obj Q)) (V.obj N) (Or.inr hUN) =
      TA.iso J' R' SA _ _ hAPQ hUN from cA.tensorIso_both _ _ hAPQ hUN,
    cA.tensorIso_both (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN] at heA
  let bPQ := TB.iso J R SB P Q hP hQ
  let bQN := TB.iso J R SB Q N hQ hN
  let bL := TB.iso J R SB PQ N hPQ hN
  let bR := TB.iso J R SB P QN hP hQN
  let aPQ := TA.iso J' R' SA (V.obj P) (V.obj Q) hUP hUQ
  let aQN := TA.iso J' R' SA (V.obj Q) (V.obj N) hUQ hUN
  let aL := TA.iso J' R' SA (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN
  let aR := TA.iso J' R' SA (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN
  let aL₀ := TA.iso J' R' SA (V.obj PQ) (V.obj N) hUPQ hUN
  let aR₀ := TA.iso J' R' SA (V.obj P) (V.obj QN) hUP hUQN
  let lB := bL ≪≫ whiskerRightIso bPQ (DerivedCategory.Q.obj N)
  let rB := bR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj P) bQN
  let lA := aL ≪≫ whiskerRightIso aPQ (DerivedCategory.Q.obj (V.obj N))
  let rA := aR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj (V.obj P)) aQN
  let e := U.mapDerivedCategoryFactors
  let tPQ := DerivedCategory.Q.map (chain.hom.app (P, Q))
  let tQN := DerivedCategory.Q.map (chain.hom.app (Q, N))
  let tL := DerivedCategory.Q.map (chain.hom.app (PQ, N))
  let tR := DerivedCategory.Q.map (chain.hom.app (P, QN))
  let eL := e.hom.app (B.obj (PQ, N)) ≫ tL ≫
    DerivedCategory.Q.map (A.map (X := (V.obj PQ, V.obj N))
      (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
      (chain.hom.app (P, Q), 𝟙 (V.obj N)))
  let eR := e.hom.app (B.obj (P, QN)) ≫ tR ≫
    DerivedCategory.Q.map (A.map (X := (V.obj P, V.obj QN))
      (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
      (𝟙 (V.obj P), chain.hom.app (Q, N)))
  have hB : lB.hom ≫ (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom = DerivedCategory.Q.map aB.hom ≫ rB.hom := by
    simpa only [lB, rB, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom,
      Category.assoc] using heB
  have hA : lA.hom ≫ (α_ (DerivedCategory.Q.obj (V.obj P))
        (DerivedCategory.Q.obj (V.obj Q)) (DerivedCategory.Q.obj (V.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ rA.hom := by
    simpa only [lA, rA, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom,
      Category.assoc] using heA
  have hmPQ := hμ P Q hP hQ hUP hUQ fP fQ
  have hmQN := hμ Q N hQ hN hUQ hUN fQ fN
  have hmL := hμ PQ N hPQ hN hUPQ hUN fPQ fN
  have hmR := hμ P QN hP hQN hUP hUQN fP fQN
  have hnL := ringed_tensor_both_naturality J' R' SA TA βA cA
    (V.obj PQ) (V.obj N) (A.obj (V.obj P, V.obj Q)) (V.obj N) hUPQ hUN hAPQ hUN
    (chain.hom.app (P, Q)) (𝟙 (V.obj N))
  have hnR := ringed_tensor_both_naturality J' R' SA TA βA cA
    (V.obj P) (V.obj QN) (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hUQN hUP hAQN
    (𝟙 (V.obj P)) (chain.hom.app (Q, N))
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnL
  erw [tensorHom_id] at hnL
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnR
  erw [id_tensorHom] at hnR
  have hL := left_model_square U.mapDerivedCategory μ bPQ.hom bL.hom
    (e.hom.app P) (e.hom.app Q) (e.hom.app N) (e.hom.app PQ)
    (e.hom.app (B.obj (PQ, N))) tPQ tL
    (DerivedCategory.Q.map (A.map (X := (V.obj PQ, V.obj N))
      (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
      (chain.hom.app (P, Q), 𝟙 (V.obj N))))
    aPQ.hom aL₀.hom aL.hom hmPQ hmL hnL
  have hR := right_model_square U.mapDerivedCategory μ bQN.hom bR.hom
    (e.hom.app P) (e.hom.app Q) (e.hom.app N) (e.hom.app QN)
    (e.hom.app (B.obj (P, QN))) tQN tR
    (DerivedCategory.Q.map (A.map (X := (V.obj P, V.obj QN))
      (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
      (𝟙 (V.obj P), chain.hom.app (Q, N))))
    aQN.hom aR₀.hom aR.hom hmQN hmR hnR
  have hC : U.mapDerivedCategory.map (DerivedCategory.Q.map aB.hom) ≫ eR =
      eL ≫ DerivedCategory.Q.map aA.hom := by
    have hf := e.hom.naturality aB.hom
    change U.mapDerivedCategory.map (DerivedCategory.Q.map aB.hom) ≫
        e.hom.app (B.obj (P, QN)) = e.hom.app (B.obj (PQ, N)) ≫
          DerivedCategory.Q.map (V.map aB.hom) at hf
    dsimp only [eL, eR]
    rw [reassoc_of% hf]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ e.hom.app (B.obj (PQ, N)) ≫ DerivedCategory.Q.map f) hc
  exact associativity_transport U.mapDerivedCategory μ lB rB (DerivedCategory.Q.map aB.hom)
    lA.hom rA.hom (DerivedCategory.Q.map aA.hom) (e.app P) (e.app Q) (e.app N)
    eL eR hB hA hL hR hC

end CategoryTheory.RingedForgetTensorTransposition
