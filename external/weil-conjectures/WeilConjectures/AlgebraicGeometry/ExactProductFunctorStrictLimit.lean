/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent

/-!
# Canonical strict derived-limit comparison for exact product-preserving functors

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md,
final proof paragraph; Stacks Project, Tags 0940, 0941 and 07KC
(auxiliary; not a blueprint node).

The tower functor is Mathlib's actual postcomposition by `F`, on both complexes and
localizations. All Roos, resolution, triangle and augmentation clauses concern the same
natural isomorphism `lambda`. The signed coordinates are `(x,y)=(u,-v)` in Mathlib's
shifted-cone coordinates `(u,v)`, giving `d(x,y)=(dx,(1-s)x-dy)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid repeatedly traversing the complete comparison specification.
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uC vC r uD vD s wA wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section
variable {A : Type*} {B : Type*} [Category* A] [Category* B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

omit [Abelian A] [Abelian B] in
private theorem natProducts (F : A ⥤ B) (h : ∀ M : ℕ → A, IsIso (piComparison F M)) :
    PreservesLimitsOfShape (Discrete ℕ) F where
  preservesLimit {K} := by
    have := h (fun n ↦ K.obj ⟨n⟩)
    have : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
      PreservesProduct.of_iso_comparison F (K.obj ∘ Discrete.mk)
    exact preservesLimit_of_iso_diagram F Discrete.natIsoFunctor.symm

omit [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B] in
private theorem infiniteProducts (F : A ⥤ B) [PreservesLimitsOfShape (Discrete ℕ) F]
    (T : Type) [Countable T] [Infinite T] : PreservesLimitsOfShape (Discrete T) F := by
  let := Classical.choice (nonempty_denumerable T)
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence (Denumerable.eqv T).symm) F

omit [Abelian B] [HasCountableProducts B] in
private theorem natProducts_preservesTowers (F : A ⥤ B) [PreservesFiniteLimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] : PreservesLimitsOfShape ℕᵒᵖ F := by
  let T := Σ p : ℕᵒᵖ × ℕᵒᵖ, p.1 ⟶ p.2
  have : Infinite T := Infinite.of_injective
    (fun n : ℕ ↦ (⟨(op n, op n), 𝟙 _⟩ : T)) (by
      intro i j h
      exact congrArg (fun t : T ↦ t.1.1.unop) h)
  have : Infinite ℕᵒᵖ := Infinite.of_injective op op_injective
  have : PreservesLimitsOfShape (Discrete ℕᵒᵖ) F := infiniteProducts F _
  have : PreservesLimitsOfShape (Discrete T) F := infiniteProducts F _
  exact preservesLimit_of_preservesEqualizers_and_product F

end

private theorem normalizedIso_identity {A : Type*} [Category* A]
    {X Y Z : A} (e : X ≅ Y) (t : Z ≅ Y) (f : X ⟶ Z)
    (h : t.inv = e.inv ≫ f) : f ≫ t.hom = e.hom := by
  apply (cancel_mono t.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

private theorem signedSwap_naturality {A : Type*} [Category* A] [Preadditive A]
    [HasBinaryBiproducts A] {X Y X' Y' V V' : A}
    (a : X ⟶ X') (b : Y ⟶ Y') (v : V ⟶ V')
    (c : V ⟶ X ⊞ Y) (c' : V' ⟶ X' ⊞ Y')
    (h : v ≫ c' = c ≫ biprod.map a b) :
    v ≫ c' ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _) =
      c ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _) ≫ biprod.map b a := by
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [Category.assoc]

private theorem signedSwap_lift {A : Type*} [Category* A] [Preadditive A]
    [HasBinaryBiproducts A] {X Y V : A} (f : V ⟶ Y) :
    biprod.lift (0 : V ⟶ X) f ≫ (biprod.braiding _ _).hom ≫
      biprod.map (𝟙 _) (-𝟙 _) = biprod.lift f 0 := by
  apply biprod.hom_ext <;> simp [Category.assoc]

-- The interface contains several universe-polymorphic product and cone choices.
private theorem signedRoosComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (LA : DerivedCategory.{wA}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
        DerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ))) :
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ⥤ CochainComplex
      (ringedSiteModules.{max uC vC r} R) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      ,
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA Y p).hom = (chiA X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) := by
  obtain ⟨HA, hAobj, chiA0, CA, eA, rhoA, aA, evA, hAc, hAm, _, _, _, hAn⟩ :=
    strictRoosComparison.{uC, vC, r, wA} J R hcomm LA etaA _hLA
  let thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA} :=
    (eA ≪≫ Functor.isoWhiskerLeft _ rhoA).symm
  let chiA := fun X p ↦ chiA0 X p ≪≫ biprod.braiding _ _ ≪≫
    (biprod.mapIso (Iso.refl _) {
      hom := -𝟙 _
      inv := -𝟙 _
      hom_inv_id := by simp
      inv_hom_id := by simp })
  refine ⟨HA, hAobj, chiA, thetaA, ?_, ?_, ?_⟩
  · intro X p
    dsimp only [chiA, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
    rw [hAc]
    simp
  · intro X Y f p
    dsimp only [chiA, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
    convert! signedSwap_naturality _ _ _ _ _ (hAm f p) using 1
  · intro I _ hIinj
    obtain ⟨iota, eps, dI, hiota, _, hqi, heps, hdI, hf, _⟩ :=
      hAn I I (𝟙 I) hIinj
    refine ⟨iota, hqi, ?_, ?_⟩
    · intro p
      dsimp only [chiA, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
      rw [← Category.assoc, ← Category.assoc, hiota]
      simpa only [biprod.mapIso_hom, Iso.refl_hom, Category.assoc] using
        signedSwap_lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1))
    · have hdI' : dI.hom = etaA.app I := by simpa using hdI
      have hf' : thetaA.inv.app I = eps.inv ≫ etaA.app I := by
        simpa [thetaA, hdI'] using hf
      calc
        etaA.app I ≫ thetaA.hom.app I = eps.hom :=
          normalizedIso_identity eps (thetaA.app I) (etaA.app I) hf'
        _ = DerivedCategory.Q.map iota := heps

section StrictLimitSpecification
universe a b c d
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

/-- The full signed Roos specification for exact product-preserving functors.
This packages verbatim the witnesses and normalization equations of
`exactProductFunctorStrictLimit`, so specialization can retain a named predicate.
Source: Stacks 0940, 0941 and 07KC
(auxiliary; not a blueprint node). -/
def StrictLimitAssertions (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB) : Prop :=
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (chiB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X))
      (beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (limit I.asFunctor) ≅ limit
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I).asFunctor)
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB),
      -- The signed coordinates are pinned to the actual shifted cone, in both categories.
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      -- Roos maps are the product map on each signed coordinate.
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA Y p).hom = (chiA X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB Y p).hom = (chiB X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      -- K-injective normalization of the same thetaA and thetaB.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota) ∧
      -- The canonical product map, and its two-summand version kappa.
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psi X).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k))
          n)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA X p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f p =
          F.map ((chiA X p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)) ∧
      -- This square is lambda = thetaB inverse, kappa, F(thetaA), in Lean order.
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app X) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          X) ≫
            DerivedCategory.Q.{wB}.map (kappa X).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
              inferInstance⟩)).hom.app X) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) ∧
      -- Ordinary inverse limits are preserved, with the canonical projection normalization.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor (op n))) ∧
      -- Every pair of K-injective resolutions computes this same lambda.
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I) [QuasiIso q]
        [I.IsKInjective]
        (Jt : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (r :
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I ⟶ Jt) [QuasiIso r] [Jt.IsKInjective],
        ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.{wA}.obj
          X))
          (dJ : DerivedCategory.Q.{wB}.obj (limit Jt.asFunctor) ≅ LB.obj (DerivedCategory.Q.{wB}.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj I))),
          dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
          dJ.hom ≫ LB.map (DerivedCategory.Q.{wB}.map r) = etaB.app Jt ∧
          (F.mapDerivedCategory).map dI.hom ≫ lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              LB.map (DerivedCategory.Q.{wB}.map ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
            F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
              DerivedCategory.Q.{wB}.map (beta I).hom ≫
              DerivedCategory.Q.{wB}.map (lim.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) ≫ dJ.hom) ∧
      -- Only the coordinate-specified triangle maps occur in the triangle identities.
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        ∃ (p : HA.obj X ⟶ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n)))) (p' : HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X) ⟶ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
          (delta : (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ⟶ (HA.obj X)⟦(1 : ℤ)⟧)
          (delta' : (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))) ⟶ (HB.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj X))⟦(1 : ℤ)⟧),
          (∀ i : ℤ, p.f (i + 1) = (chiA X i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, p'.f (i + 1) = (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, delta.f i ≫ ((HA.obj X).shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
            (chiA X i).hom = -biprod.inr) ∧
          (∀ i : ℤ, delta'.f i ≫ ((HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).shiftFunctorObjXIso 1 i (i + 1)
            rfl).hom ≫
            (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X) i).hom = -biprod.inr) ∧
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫ DerivedCategory.Q.{wB}.map p' =
            (F.mapDerivedCategory).map (thetaA.hom.app X ≫ DerivedCategory.Q.{wA}.map p) ≫
              F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
                DerivedCategory.Q.{wB}.map (psi X).hom ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map delta ≫
            (DerivedCategory.Q.{wA}.commShiftIso (1 : ℤ)).hom.app (HA.obj X) ≫
              (thetaA.inv.app X)⟦(1 : ℤ)⟧') ≫
              (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (LA.obj
                (DerivedCategory.Q.{wA}.obj X)) ≫
              (lambda.hom.app (DerivedCategory.Q.{wA}.obj X))⟦(1 : ℤ)⟧' ≫
              (LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X))⟦(1 : ℤ)⟧' =
            F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
              DerivedCategory.Q.{wB}.map (psi X).hom ≫
              DerivedCategory.Q.{wB}.map delta' ≫ (DerivedCategory.Q.{wB}.commShiftIso (1 :
                ℤ)).hom.app (HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
              (thetaB.inv.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X))⟦(1 : ℤ)⟧') ∧
      -- The strict augmentation maps are pinned by (gamma,0), not arbitrary derived arrows.
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex
        (A) ℤ) (gamma : ∀ n : ℕ, Q ⟶ X.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj X) (b' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA X i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app X) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X))

end StrictLimitSpecification

-- The interface retains every signed-cone and resolution normalization law.
/-- The canonical comparison for exact additive countable-product-preserving module functors.

Source: the final paragraph of the blueprint proof of
lem-cbc-completed-extension-zero-comparison, refined by Stacks Project, Tags 0940,
0941 and 07KC (auxiliary; not a blueprint node).

Proof, following the nine steps of the blueprint node:
1. Apply situation-conventions to `F` and its postcomposition on
   towers. Levelwise exactness is lem-weil-tower-category-levelwise-abelian. Exact
   countable products identify termwise and derived products by
   lem-weil-derived-limit-products-core. The projection equations characterize phi.
2. Apply lem-weil-strict-roos-comparison in both categories. In Mathlib's shifted cone,
   use `(x,y)=(u,-v)` to obtain the displayed signed differential. Invert the normalized
   comparison to obtain thetaA and thetaB; the inverse-limit inclusion is `(iota,0)`.
3. Product projections give phi F(s)=s' phi and phi F(d)=d phi. Additivity gives the
   same identity for 1-s. On the two biproduct summands, phi therefore defines the chain
   isomorphism kappa; its inverse uses phi inverse on both summands.
4. Conjugate kappa by thetaA and thetaB to define lambda. Each factor is invertible.
   Product-projection naturality proves naturality on strict chain maps. The Roos
   descent and exact-functor localization extend it to quasi-isomorphism inverses and
   hence every derived morphism.
5. The first triangle map is projection to x. The connecting map is minus inclusion
   into y in these signed coordinates, with Mathlib's cone/shift convention from
   def-weil-abstract-derived-category. The diagonal kappa intertwines both maps; its
   shift uses F.mapDerivedCategory.commShiftIso. Conjugating gives the two equations.
6. An ordinary tower limit is the kernel of 1-s on its product. Exact F preserves
   this kernel, and phi identifies its defining endomorphisms, giving beta. Do this
   degreewise; the projection equations show beta commutes with differentials.
7. Resolve the source and image tower using prop-pur-kinjective-resolutions-exist
   on the small tower sites. For resolutions with injective terms the normalized
   inclusions satisfy iotaJ (lim r) betaI = H(r) kappaI F(iotaI): both first components
   have n-th projection r_n F(pr_n) and both second components are zero. Cancel the
   normalized quasi-isomorphisms from lem-weil-strict-roos-comparison. The computation
   of lem-weil-pbc-ringed-strict-tower-homotopy-limit gives the stated unit-normalized
   resolution formula. Naturality at q supplies the inverse of the derived F(q).
8. For arbitrary K-injective resolutions, refine them to ones with injective terms.
   By lem-weil-pbc-kinjective-hom-derived these refinements are homotopy equivalences;
   the comparison into a K-injective target exists and is unique up to homotopy.
   Additive F and ordinary limit preserve those homotopies. Naturality of beta
   transports step 7 back to the original resolutions. Every resulting formula
   equals the same lambda, proving independence of all resolution choices.
9. A strict augmentation has signed Roos map `(gamma,0)`. Its first projections
   after kappa are F(gamma_n), and its second component stays zero. The augmentation
   clause of lem-weil-strict-roos-comparison identifies these with the canonical
   derived-limit maps, giving the last equality for every compatible family. -/
theorem exactProductFunctorStrictLimit
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max uD vD s}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (S : Sheaf K RingCat.{max uD vD s})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S)]
    (F : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uD vD s} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_hphi : ∀ (M : ℕ → ringedSiteModules.{max uC vC r} R), IsIso (piComparison F M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤ DerivedCategory.{wA}
      (ringedSiteModules.{max uC vC r} R))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ⥤ DerivedCategory.{wB}
      (ringedSiteModules.{max uD vD s} S))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙
        LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uD vD s} S) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙
        LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) (ComplexShape.up ℤ))) :
    StrictLimitAssertions F LA LB etaA etaB := by
  unfold StrictLimitAssertions
  obtain ⟨HA, hAobj, chiA, thetaA, hAc, hAm, hAn⟩ :=
    signedRoosComparison.{uC, vC, r, wA} J R _hR LA etaA _hLA
  obtain ⟨HB, hBobj, chiB, thetaB, hBc, hBm, hBn⟩ :=
    signedRoosComparison.{uD, vD, s, wB} K S _hS LB etaB _hLB
  obtain ⟨psi, kappa, hpsi, hkappa, hknat⟩ :=
    exactProductFunctorRoosChainMaps.{uC, vC, r, uD, vD, s, wA, wB} J R K S _hR _hS F _hphi
      HA HB hAobj hBobj chiA chiB ⟨hAc, hBc⟩ ⟨hAm, hBm⟩
  have : PreservesLimitsOfShape (Discrete ℕ) F := natProducts F _hphi
  have : PreservesLimitsOfShape ℕᵒᵖ F := natProducts_preservesTowers F
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let beta := fun I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    preservesLimitIso Fc I.asFunctor
  have hbeta :
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor (op n))) := by
    intro I n
    exact preservesLimitIso_hom_π Fc I.asFunctor (op n)
  obtain ⟨lambda, hsquare, hres⟩ :=
    exactProductFunctorRoosDescent.{uC, vC, r, uD, vD, s, wA, wB} J R K S _hR _hS F _hphi
      LA LB etaA _hLA etaB _hLB HA HB hAobj hBobj chiA chiB thetaA thetaB
      psi kappa beta ⟨hAc, hBc⟩ ⟨hAm, hBm⟩ ⟨hAn, hBn⟩ hkappa hknat hbeta
  obtain ⟨htri, haug⟩ :=
    exactProductFunctorRoosCompatibility.{uC, vC, r, uD, vD, s, wA, wB} J R K S _hR _hS F _hphi
      LA LB etaA _hLA etaB _hLB HA HB hAobj hBobj chiA chiB thetaA thetaB
      psi kappa lambda ⟨hAc, hBc⟩ hpsi hkappa hsquare
  exact ⟨HA, HB, hAobj, hBobj, chiA, chiB, thetaA, thetaB, psi, kappa, beta,
    lambda, hAc, hBc, hAm, hBm, hAn, hBn, hpsi, hkappa, hsquare, hbeta, hres,
    htri, haug⟩

end CategoryTheory
