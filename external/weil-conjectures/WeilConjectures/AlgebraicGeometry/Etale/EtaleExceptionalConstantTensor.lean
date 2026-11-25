/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportUnboundedAmplitude
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportProjectionShiftUnit
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportCompactAdjointSums
import WeilConjectures.CategoryTheory.SmoothPurity.CoefficientActionAdjointGeneration
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorDirectSums

/-! # Constant coefficient tensor calculus for the exceptional adjoint

Source: Zheng, Theorem 2.18(2), Corollary 2.19, Construction 2.26 and Proposition 2.29(2)
(printed pp. 12, 14--16), specialized to schemes over an algebraically closed field
(blueprint: lem-pur-etale-exceptional-constant-tensor).

## Main definitions

- `exceptionalCoefficientTensor`: the existing tensor restricted to constant coefficients.
- `exceptionalConstantPullbackIso`: localization of the constant-sheaf pullback comparison.
- `exceptionalConstantProjectionMap`: the canonical compact-support projection composite.

## Main statements

- `exceptionalConstantTensor`: coefficient-uniform amplitude and the two canonical natural
  tensor isomorphisms for any fixed right adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2000

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

section ProjectionConstruction

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The canonical projection composite after a specified identification of coefficient pullback.
It applies signed symmetry, the compactification projection map, tensor of the identification,
and signed symmetry on the source. This generic constructor keeps these maps shared when
specialized to constant coefficient complexes.
Source: Zheng, Theorem 2.18(2) and Construction 2.26
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalProjectionConstruction
    {D : Type*} [Category D] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (H' : D ⥤ DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : H ⋙ (upperStar A f).leftDerivedFunctor ≅ H') (V : D)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A Y).obj (H.obj V)).obj
        ((rightDerivedLowerShriekOfCompactification A c).obj K) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        (((derivedTensor A X).obj (H'.obj V)).obj K) :=
  ((derivedTensorSymmetry A Y).hom.app (H.obj V)).app
      ((rightDerivedLowerShriekOfCompactification A c).obj K) ≫
    ((projectionMapOfCompactification A c).app K).app (H.obj V) ≫
    (rightDerivedLowerShriekOfCompactification A c).map
      (((derivedTensor A X).obj K).map (t.hom.app V) ≫
        ((derivedTensorSymmetry A X).hom.app K).app (H'.obj V))

end ProjectionConstruction

/-- Tensor by a termwise constant coefficient complex, as a bifunctor in the sheaf complex
and coefficient complex. This uses the existing constant-sheaf descent and derived tensor.
Source: Zheng, Theorem 2.18(2) and Proposition 2.29(2)
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalCoefficientTensor (C : Type (u + 1)) [CommRing C]
    (T : Scheme.{u}) :
    DerivedCategoryModule C T ⥤ DerivedCategory (ModuleCat.{u + 1} C) ⥤
      DerivedCategoryModule C T :=
  (derivedTensor (ModuleCat.{u + 1} C) T).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory

/-- The canonical pullback identification for termwise constant complexes. It is obtained
by descending the existing constant-sheaf pullback isomorphism through localization.
Source: Zheng, Theorem 2.18(2), constant-coefficient specialization
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalConstantPullbackIso (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} C) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Scheme.upperStarConstantSheafIso
      (ModuleCat.{u + 1} C) f)

/-- The actual compact-support projection map with the constant factor first. Compose the
signed symmetry, the existing compactification projection map, the canonical pullback of
constants, and the signed symmetry on the source. All factors are maps on derived categories.
Source: Zheng, Theorem 2.18(2), and Construction 2.26
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalConstantProjectionMap (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X) :
    ((exceptionalCoefficientTensor C Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).obj V ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj
        (((exceptionalCoefficientTensor C X).obj K).obj V) :=
  exceptionalProjectionConstruction (ModuleCat.{u + 1} C) c
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    (exceptionalConstantPullbackIso C f) V K

/-- Assemble an invertible natural transformation from the two mate naturality equations.
Source: the assembly step of `lem-pur-etale-exceptional-constant-tensor`.
(blueprint: lem-pur-etale-exceptional-constant-tensor).

The components are the specified coefficient-action mates. Naturality in the coefficient and
in the sheaf object gives a natural isomorphism; the component invertibility is supplied by
the final hypothesis. -/
private theorem exists_actionMateIso_of_naturality
    {D A B : Type*} [Category D] [Category A] [Category B]
    (TA : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) (Q : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F)
    (hV : ∀ (V W : D) (h : V ⟶ W) (M : B),
      (TA.obj (G.obj M)).map h ≫ coefficientActionAdjointMate TA TB adj Q W M =
        coefficientActionAdjointMate TA TB adj Q V M ≫ G.map ((TB.obj M).map h))
    (hM : ∀ (V : D) (M N : B) (h : M ⟶ N),
      (TA.map (G.map h)).app V ≫ coefficientActionAdjointMate TA TB adj Q V N =
        coefficientActionAdjointMate TA TB adj Q V M ≫ G.map ((TB.map h).app V))
    [∀ (V : D) (M : B), IsIso (coefficientActionAdjointMate TA TB adj Q V M)] :
    ∃ AQ : G ⋙ TA ≅ TB ⋙ (Functor.whiskeringRight D B A).obj G,
      ∀ V M, (AQ.hom.app M).app V = coefficientActionAdjointMate TA TB adj Q V M := by
  let AQ : G ⋙ TA ≅ TB ⋙ (Functor.whiskeringRight D B A).obj G :=
    NatIso.ofComponents
      (fun M ↦ NatIso.ofComponents
        (fun V ↦ asIso (coefficientActionAdjointMate TA TB adj Q V M))
        (fun h ↦ hV _ _ h M))
      (fun h ↦ NatTrans.ext (funext (fun V ↦ hM V _ _ h)))
  exact ⟨AQ, fun _ _ ↦ rfl⟩

private theorem adjunction_commShift_of_counit
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F : A ⥤ B} {G : B ⥤ A} [F.CommShift ℤ] [G.CommShift ℤ] (adj : F ⊣ G)
    (hε : ∀ (n : ℤ) (M : B), adj.counit.app (M⟦n⟧) =
      F.map ((G.commShiftIso n).hom.app M) ≫
        (F.commShiftIso n).hom.app (G.obj M) ≫ (adj.counit.app M)⟦n⟧') :
    adj.CommShift ℤ := by
  have hu (n : ℤ) (X : A) : (adj.unit.app X)⟦n⟧' =
      adj.unit.app (X⟦n⟧) ≫ G.map ((F.commShiftIso n).hom.app X) ≫
        (G.commShiftIso n).hom.app (F.obj X) := by
    apply (cancel_mono ((G.commShiftIso n).inv.app (F.obj X))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply (adj.homEquiv _ _).symm.injective
    simp only [adj.homEquiv_counit, Functor.map_comp, Category.assoc]
    have hc := Adjunction.CommShift.compatibilityCounit_left adj
      (F.commShiftIso n) (G.commShiftIso n) (hε n) X
    have hn := adj.counit.naturality ((F.commShiftIso n).hom.app X)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj,
      Functor.id_obj] at hn
    have ht : F.map (adj.unit.app (X⟦n⟧)) ≫
        adj.counit.app (F.obj (X⟦n⟧)) = 𝟙 _ := adj.left_triangle_components _
    have h := congrArg (fun q ↦ F.map (adj.unit.app (X⟦n⟧)) ≫ q) hn
    simp only [← Category.assoc] at h
    rw [ht, Category.id_comp] at h
    rw [← hc]
    dsimp
    rw [F.map_id, Category.id_comp]
    simpa only [Category.assoc] using h.symm
  apply Adjunction.CommShift.mk' adj ℤ
  constructor
  intro n
  ext X
  simpa only [NatTrans.comp_app, Functor.commShiftIso_id_hom_app,
    Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.id_obj, Functor.id_map, Category.id_comp, Category.assoc]
    using hu n X

private theorem mate_transport
    {D A B : Type*} [Category D] [Category A] [Category B]
    (TA TA' : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) (Q : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F)
    (b : TA ≅ TA') (V : D) (M : B) :
    (b.inv.app (G.obj M)).app V ≫ coefficientActionAdjointMate TA TB adj Q V M =
      coefficientActionAdjointMate TA' TB adj
        (Q ≪≫ Functor.isoWhiskerRight b ((Functor.whiskeringRight D A B).obj F)) V M := by
  change (b.inv.app (G.obj M)).app V ≫ adj.homEquiv _ _
      ((Q.inv.app (G.obj M)).app V ≫ (TB.map (adj.counit.app M)).app V) =
    adj.homEquiv _ _
      ((F.map ((b.inv.app (G.obj M)).app V) ≫ (Q.inv.app (G.obj M)).app V) ≫
        (TB.map (adj.counit.app M)).app V)
  rw [Category.assoc]
  exact (adj.homEquiv_naturality_left ((b.inv.app (G.obj M)).app V)
    ((Q.inv.app (G.obj M)).app V ≫ (TB.map (adj.counit.app M)).app V)).symm

private noncomputable def transportProjection
    {D A B : Type*} [Category D] [Category A] [Category B]
    (TA TA' : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) (F : A ⥤ B)
    (Q : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F) (b : TA ≅ TA') :=
  Q ≪≫ Functor.isoWhiskerRight b ((Functor.whiskeringRight D A B).obj F)

private theorem transportProjection_hom_app
    {D A B : Type*} [Category D] [Category A] [Category B]
    (TA TA' : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) (F : A ⥤ B)
    (Q : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F) (b : TA ≅ TA')
    (K : A) (V : D) :
    ((transportProjection TA TA' TB F Q b).hom.app K).app V =
      (Q.hom.app K).app V ≫ F.map ((b.hom.app K).app V) := rfl

private noncomputable def transportMate
    {D A B : Type*} [Category D] [Category A] [Category B]
    (TA TA' : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) (G : B ⥤ A)
    (AQ : G ⋙ TA ≅ TB ⋙ (Functor.whiskeringRight D B A).obj G) (b : TA ≅ TA') :=
  Functor.isoWhiskerLeft G b.symm ≪≫ AQ

private theorem transportMate_hom_app
    {D A B : Type*} [Category D] [Category A] [Category B]
    (TA TA' : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) (G : B ⥤ A)
    (AQ : G ⋙ TA ≅ TB ⋙ (Functor.whiskeringRight D B A).obj G) (b : TA ≅ TA')
    (M : B) (V : D) :
    ((transportMate TA TA' TB G AQ b).hom.app M).app V =
      (b.inv.app (G.obj M)).app V ≫ (AQ.hom.app M).app V := rfl

section ActionHelpers

attribute [local instance] Sheaf.monoidalCategory

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {D : Type*} [Category D]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

private noncomputable def action (T : Scheme.{u})
    (H : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  (derivedTensor A T).flip ⋙ (Functor.whiskeringLeft _ _ _).obj H

@[instance_reducible] private noncomputable instance action_obj_commShift [HasShift D ℤ]
    (T : Scheme.{u}) (H : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A))
    [H.CommShift ℤ] (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((action A T H).obj K).CommShift ℤ :=
  inferInstanceAs ((H ⋙ (derivedTensor A T).flip.obj K).CommShift ℤ)

private theorem action_obj_isTriangulated [HasShift D ℤ] [HasZeroObject D]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] (T : Scheme.{u})
    (H : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A)) [H.CommShift ℤ]
    [H.IsTriangulated] (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((action A T H).obj K).IsTriangulated := by
  dsimp [action]
  infer_instance

private theorem action_map_commShift [HasShift D ℤ] (T : Scheme.{u})
    (H : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A)) [H.CommShift ℤ]
    {K K' : DerivedCategory (Sheaf T.smallEtaleTopology A)} (g : K ⟶ K') :
    NatTrans.CommShift ((action A T H).map g) ℤ := by
  have : NatTrans.CommShift ((derivedTensor A T).flip.map g) ℤ :=
    Functor.CommShift₂.commShift_flip_map
      (G := curriedTensor (DerivedCategory (Sheaf T.smallEtaleTopology A))) (h := .int) g
  exact NatTrans.CommShift.whiskerLeft (F₁ := H)
    (G := (derivedTensor A T).flip.obj K) (G' := (derivedTensor A T).flip.obj K')
    (τ'' := (derivedTensor A T).flip.map g) (A := ℤ)

private noncomputable def actionIso (T : Scheme.{u})
    {H H' : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A)} (b : H ≅ H') :
    action A T H ≅ action A T H' :=
  Functor.isoWhiskerLeft (derivedTensor A T).flip
    ((Functor.whiskeringLeft _ _ _).mapIso b)

private noncomputable def actionUnit (T : Scheme.{u})
    (H : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A)) (R : D)
    (r : H.obj R ≅ 𝟙_ (DerivedCategory (Sheaf T.smallEtaleTopology A))) :
    (action A T H).flip.obj R ≅ 𝟭 _ :=
  (derivedTensor A T).mapIso r ≪≫ derivedTensorLeftUnitorNatIso A T

private theorem actionUnit_hom_app (T : Scheme.{u})
    (H : D ⥤ DerivedCategory (Sheaf T.smallEtaleTopology A)) (R : D)
    (r : H.obj R ≅ 𝟙_ (DerivedCategory (Sheaf T.smallEtaleTopology A)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (actionUnit A T H R r).hom.app K =
      ((derivedTensor A T).flip.obj K).map r.hom ≫
        (derivedTensorLeftUnitor A T K).hom := rfl

attribute [irreducible] actionUnit

private noncomputable def restrictedProjection
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c) :
    rightDerivedLowerShriekOfCompactification A c ⋙ action A Y H ≅
      action A X (H ⋙ (upperStar A f).leftDerivedFunctor) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (rightDerivedLowerShriekOfCompactification A c) :=
  Functor.isoWhiskerRight e ((Functor.whiskeringLeft _ _ _).obj H)

private theorem symmetry_inv_app
    (T : Scheme.{u}) (K L : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((derivedTensorSymmetry A T).inv.app K).app L =
      ((derivedTensorSymmetry A T).hom.app L).app K := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf T.smallEtaleTopology A)
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding K L).symm

private theorem restrictedProjection_shift [HasShift D ℤ]
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A)) [H.CommShift ℤ]
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c)
    (he : ∀ K, NatTrans.CommShift (e.hom.app K) ℤ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ) (V : D) :
    (((restrictedProjection A c H e).hom.app K).app (V⟦n⟧)) ≫
      (((action A X (H ⋙ (upperStar A f).leftDerivedFunctor)).obj K ⋙
        rightDerivedLowerShriekOfCompactification A c).commShiftIso n).hom.app V =
      (((action A Y H).obj
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).commShiftIso n).hom.app V ≫
      ((((restrictedProjection A c H e).hom.app K).app V))⟦n⟧' := by
  have h := he K
  change NatTrans.CommShift (e.hom.app K :
    (derivedTensor A Y).flip.obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K) ⟶
    ((upperStar A f).leftDerivedFunctor ⋙ (derivedTensor A X).flip.obj K) ⋙
      rightDerivedLowerShriekOfCompactification A c) ℤ at h
  have hs := congr_app (h.shift_comm n) (H.obj V)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hs
  have hn := (e.hom.app K).naturality ((H.commShiftIso n).hom.app V)
  change
    ((derivedTensor A Y).flip.obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K)).map
      ((H.commShiftIso n).hom.app V) ≫ (e.hom.app K).app ((H.obj V)⟦n⟧) =
      (e.hom.app K).app (H.obj (V⟦n⟧)) ≫
        (rightDerivedLowerShriekOfCompactification A c).map
          (((derivedTensor A X).flip.obj K).map
            ((upperStar A f).leftDerivedFunctor.map ((H.commShiftIso n).hom.app V))) at hn
  dsimp only [restrictedProjection, action, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    Functor.whiskeringLeft_obj_obj, Functor.comp_obj]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
  change
    (((derivedTensor A Y).flip.obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K)).commShiftIso n).hom.app
        (H.obj V) ≫ ((e.hom.app K).app (H.obj V))⟦n⟧' =
    (e.hom.app K).app ((H.obj V)⟦n⟧) ≫
      ((((upperStar A f).leftDerivedFunctor ⋙ (derivedTensor A X).flip.obj K) ⋙
        rightDerivedLowerShriekOfCompactification A c).commShiftIso n).hom.app
          (H.obj V) at hs
  simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp,
    Functor.comp_obj, Category.assoc] at hs
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simpa only [Functor.comp_obj, Category.assoc] using
    congrArg (fun t ↦ ((derivedTensor A Y).flip.obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K)).map
        ((H.commShiftIso n).hom.app V) ≫ t) hs.symm

private theorem projection_reindex
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c)
    (he : SupportProjectionCoherent A c e)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (L' : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (upperStar A f).leftDerivedFunctor.obj L ⟶ L') :
    (e.hom.app K).app L ≫ (rightDerivedLowerShriekOfCompactification A c).map
      (((derivedTensor A X).flip.obj K).map t) =
    ((derivedTensorSymmetry A Y).hom.app L).app
        ((rightDerivedLowerShriekOfCompactification A c).obj K) ≫
      ((projectionMapOfCompactification A c).app K).app L ≫
        (rightDerivedLowerShriekOfCompactification A c).map
          (((derivedTensor A X).obj K).map t ≫
            ((derivedTensorSymmetry A X).hom.app K).app L') := by
  rw [he.1]
  change
    (((derivedTensorSymmetry A Y).inv.app
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).app L ≫
      ((projectionMapOfCompactification A c).app K).app L ≫
        (rightDerivedLowerShriekOfCompactification A c).map
          (((derivedTensorSymmetry A X).hom.app K).app
            ((upperStar A f).leftDerivedFunctor.obj L))) ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).flip.obj K).map t) = _
  rw [symmetry_inv_app]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← ((derivedTensorSymmetry A X).hom.app K).naturality t]

private theorem projection_unit
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c)
    (he : ∀ K, (e.hom.app K).app (𝟙_ _) ≫ (supportProjectionTargetUnit A c K).hom =
      (derivedTensorLeftUnitor A Y
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom)
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (r : L ≅ 𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (e.hom.app K).app L ≫ ((supportProjectionTarget A c).obj K).map r.hom ≫
        (supportProjectionTargetUnit A c K).hom =
      ((supportProjectionSource A c).obj K).map r.hom ≫
        (derivedTensorLeftUnitor A Y
          ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom := by
  rw [← (e.hom.app K).naturality_assoc, he]

private theorem supportTarget_map
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : L ⟶ L') :
    ((supportProjectionTarget A c).obj K).map g =
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).flip.obj K).map
          ((upperStar A f).leftDerivedFunctor.map g)) := rfl

private theorem supportSource_map
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : L ⟶ L') :
    ((supportProjectionSource A c).obj K).map g =
      ((derivedTensor A Y).flip.obj
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).map g := rfl

private theorem supportTargetUnit_hom
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (supportProjectionTargetUnit A c K).hom =
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).flip.obj K).map (leftDerivedUpperStarUnitIso A f).hom ≫
          (derivedTensorLeftUnitor A X K).hom) := rfl

private theorem restrictedProjection_unit
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c)
    (he : ∀ K, (e.hom.app K).app (𝟙_ _) ≫ (supportProjectionTargetUnit A c K).hom =
      (derivedTensorLeftUnitor A Y
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom) (R : D)
    (r : H.obj R ≅ 𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((restrictedProjection A c H e).hom.app K).app R ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        ((actionUnit A X (H ⋙ (upperStar A f).leftDerivedFunctor) R
          ((upperStar A f).leftDerivedFunctor.mapIso r ≪≫
            leftDerivedUpperStarUnitIso A f)).hom.app K) =
      (actionUnit A Y H R r).hom.app
        ((rightDerivedLowerShriekOfCompactification A c).obj K) := by
  rw [actionUnit_hom_app, actionUnit_hom_app]
  have hh := projection_unit A c e he (H.obj R) r K
  rw [supportTarget_map, supportSource_map, supportTargetUnit_hom] at hh
  dsimp only [restrictedProjection, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] using hh

private theorem exists_restricted_generation
    (C : Type (u + 1)) [CommRing C]
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [HasCoproducts.{u + 1} (DerivedCategory (Sheaf X.smallEtaleTopology A))]
    [HasCoproducts.{u + 1} (DerivedCategory (Sheaf Y.smallEtaleTopology A))]
    (H : DerivedCategory (ModuleCat.{u + 1} C) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A)) [H.CommShift ℤ] [H.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) H]
    (r : H.obj ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
      (ModuleCat.of C (ULift.{0} C))) ≅
        𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c)
    (he : SupportProjectionCoherent A c e)
    (G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A))
    (adj : rightDerivedLowerShriekOfCompactification A c ⊣ G)
    [(rightDerivedLowerShriekOfCompactification A c).IsTriangulated]
    [G.CommShift ℤ] [adj.CommShift ℤ] [G.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
    [∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (I : Type (u + 1)),
      PreservesColimitsOfShape (Discrete I) ((derivedTensor A X).flip.obj K)]
    [∀ (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (I : Type (u + 1)),
      PreservesColimitsOfShape (Discrete I) ((derivedTensor A Y).flip.obj M)] :
    ∃ AQ : G ⋙ action A X (H ⋙ (upperStar A f).leftDerivedFunctor) ≅
      action A Y H ⋙ (Functor.whiskeringRight _ _ _).obj G,
      ∀ V M, (AQ.hom.app M).app V =
        coefficientActionAdjointMate (action A X (H ⋙ (upperStar A f).leftDerivedFunctor))
          (action A Y H) adj (restrictedProjection A c H e) V M := by
  let TA := action A X (H ⋙ (upperStar A f).leftDerivedFunctor)
  let TB := action A Y H
  let F := rightDerivedLowerShriekOfCompactification A c
  let Q := restrictedProjection A c H e
  have (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
    action_obj_isTriangulated A X (H ⋙ (upperStar A f).leftDerivedFunctor) K
  have (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :=
    action_obj_isTriangulated A Y H M
  have (K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)) (h : K ⟶ K') :=
    action_map_commShift A X (H ⋙ (upperStar A f).leftDerivedFunctor) h
  have (M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (h : M ⟶ M') :=
    action_map_commShift A Y H h
  have : (upperStar A f).leftDerivedFunctor.IsLeftAdjoint :=
    (derivedUpperStarLowerStarAdjunction A f).isLeftAdjoint
  have (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (TA.obj K) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      (H ⋙ (upperStar A f).leftDerivedFunctor ⋙ (derivedTensor A X).flip.obj K))
  have (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (TB.obj M ⋙ G) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      ((H ⋙ (derivedTensor A Y).flip.obj M) ⋙ G))
  let uX := actionUnit A X (H ⋙ (upperStar A f).leftDerivedFunctor) _
    ((upperStar A f).leftDerivedFunctor.mapIso r ≪≫ leftDerivedUpperStarUnitIso A f)
  let uY := actionUnit A Y H _ r
  obtain ⟨hV, hM, _, _, hI⟩ :=
    coefficientActionAdjointGeneration.{u + 1, 0, u + 1} C TA TB uX uY F G adj Q
    (fun K n V ↦ restrictedProjection_shift A c H e (fun K ↦ (he.2 K).1) K n V)
    (fun K ↦ restrictedProjection_unit A c H e (fun K ↦ (he.2 K).2.2.1) _ r K)
  have hi (V : DerivedCategory (ModuleCat.{u + 1} C))
      (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
      IsIso (coefficientActionAdjointMate TA TB adj Q V M) :=
    (hI M).2.2.2.2.2.2.2 V
  exact exists_actionMateIso_of_naturality TA TB adj Q hV hM

private theorem assemble_comparisons
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (H' : D ⥤ DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : H ⋙ (upperStar A f).leftDerivedFunctor ≅ H')
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c)
    (he : SupportProjectionCoherent A c e)
    (G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A))
    (adj : rightDerivedLowerShriekOfCompactification A c ⊣ G)
    (AQ : G ⋙ action A X (H ⋙ (upperStar A f).leftDerivedFunctor) ≅
      action A Y H ⋙ (Functor.whiskeringRight _ _ _).obj G)
    (hAQ : ∀ V M, (AQ.hom.app M).app V =
      coefficientActionAdjointMate (action A X (H ⋙ (upperStar A f).leftDerivedFunctor))
        (action A Y H) adj (restrictedProjection A c H e) V M) :
    ∃ P : rightDerivedLowerShriekOfCompactification A c ⋙ action A Y H ≅
        action A X H' ⋙ (Functor.whiskeringRight _ _ _).obj
          (rightDerivedLowerShriekOfCompactification A c),
      (∀ V K, (P.hom.app K).app V =
        exceptionalProjectionConstruction A c H H' t V K) ∧
      ∃ B : G ⋙ action A X H' ≅ action A Y H ⋙ (Functor.whiskeringRight _ _ _).obj G,
        ∀ V M, (B.hom.app M).app V = adj.homEquiv _ _
          ((P.inv.app (G.obj M)).app V ≫
            ((derivedTensor A Y).obj (H.obj V)).map (adj.counit.app M)) := by
  let b := actionIso A X t
  let Q := restrictedProjection A c H e
  let TA := action A X (H ⋙ (upperStar A f).leftDerivedFunctor)
  let TA' := action A X H'
  let TB := action A Y H
  let F := rightDerivedLowerShriekOfCompactification A c
  let P := transportProjection TA TA' TB F Q b
  let B := transportMate TA TA' TB G AQ b
  refine ⟨P, ?_, B, ?_⟩
  · intro V K
    unfold exceptionalProjectionConstruction
    rw [transportProjection_hom_app]
    exact projection_reindex A c e he K (H.obj V) (H'.obj V) (t.hom.app V)
  · intro V M
    rw [transportMate_hom_app, hAQ]
    change (b.inv.app (G.obj M)).app V ≫
      coefficientActionAdjointMate TA TB adj Q V M =
        coefficientActionAdjointMate TA' TB adj P V M
    exact mate_transport TA TA' TB adj Q b V M

end ActionHelpers

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- For a separated finite-type morphism over an algebraically closed field, the ordinary finite-
coefficient exceptional adjoint has coefficient-uniform cohomological amplitude and canonical
natural constant-coefficient tensor isomorphisms for every fixed right adjunction. No
boundedness or perfectness of the coefficient complex is required. Source: Zheng, Theorem
2.18(2), Corollary 2.19, Construction 2.26 and Proposition 2.29(2), printed pp. 12, 14–16
(blueprint: lem-pur-etale-exceptional-constant-tensor).

Proof (the complete ten-step proof of the DAG node):

1. A field is Noetherian, so $X,Y,\overline X$ are Noetherian by finite type over a Noetherian
   base, and hence quasi-compact and quasi-separated. Here $\overline X$ is finite type over $k$:
   on a finite affine cover of $Y$, take finite affine covers of the inverse images under the
   finite-type map $p_f$; a finite list of $k$-algebra generators for each base algebra, together
   with the chosen algebra generators upstairs, generates the upstairs algebra over $k$. Thus this
   assertion follows directly from the definition of finite type. Choose $d\ge0$ bounding the
   dimensions of the scheme-theoretic fibres of $f$, using quasi-compactness of $Y$. Extension of
   the residue field to an algebraic closure preserves the dimension of each finite-type fibre, so
   the same $d$ bounds the geometric fibres. This choice depends only on $f$. If $X$ or $Y$ is
   empty choose $d=0$; all compact-support values on an empty source are zero. In the rest of the
   proof any geometric fibre bound $d$ is allowed, and $N_f=2d$.

   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-
   separated, lem-fin-finite-type-fibre-dimension-bound, lem-kun-dimension-extension, def-weil-
   finite-type-morphism.

2. The termwise $j_!$ is exact and left adjoint to $j^*$, so its functor on the unbounded derived
   category is exact and preserves arbitrary coproducts. The total derived $Rp_{f,*}$ is exact by
   the K-injective derived-functor theorem and preserves arbitrary coproducts by the proper
   coproduct theorem. Thus $F=Rp_{f,*}j_!$ is exact and preserves arbitrary coproducts. Module
   sheaves have enough injectives; a bounded-below object in $D^{\ge b}$ has a K-injective
   representative with zero terms below $b$. Applying the additive $p_{f,*}$ termwise to such a
   representative shows that $Rp_{f,*}$, and therefore $F$, preserves this lower bound. For a
   sheaf $H$ on $X$, the compact-support cohomological-dimension theorem applies: $C$ is finite
   and its additive exponent is invertible since $\ell\ne p$. It gives $F(H)\in D^{[0,2d]}$, for
   arbitrary $H$, with no constructibility assumption.

   Uses: lemma-affine-space-etale-localization--4, situation-conventions, prop-weil-pbc-
   kinjective-resolutions-exist, lem-pc-right-derived-functor-triangulated, lem-amb-proper-
   coproducts, lem-weil-pbc-module-sheaves-enough-injectives, lem-weil-pbc-dplus-injective-
   representative, theorem-results-from-etale-theory--5.

3. Let $K\in D^{\le a}$. Replace it by a complex with zero terms in degrees $>a$, using good
   truncation. Its brutal lower subcomplexes $B_m=\sigma_{\ge a-m}K$, $m\ge0$, form an increasing
   sequence with termwise colimit $K$. Each $B_m$ has a finite filtration by its individual terms
   in their original degrees, so exactness of $F$ and the sheaf bound of step 2 give $F(B_m)\in
   D^{\le a+2d}$: at a filtration step the cohomology long exact sequence keeps the upper bound.
   The complex-colimit theorem identifies $K$ with the telescope of $(B_m)$, and the hocolimit-
   preservation theorem identifies $F(K)$ with a telescope of $(F(B_m))$. Coproducts are termwise
   in these derived categories, since module sheaves are Grothendieck abelian; their exactness
   means that a coproduct of objects in $D^{\le a+2d}$ is still in this subcategory. The telescope
   triangle and its long exact cohomology sequence therefore give $F(K)\in D^{\le a+2d}$. No
   convergence assertion for an unbounded spectral sequence is needed. Together with step 2, on
   bounded intervals this gives $F(D^{[r,s]})\subset D^{[r,s+2d]}$.

   Uses: def-sbc-standard-tstructure-derived-category,
   proposition-open-direct-image-preserves-finite, lem-kun-complex- colimit-hocolim,
   lem-kun-functor-preserves-hocolim, lem-weil-pbc-module-sheaves-grothendieck- abelian,
   lem-kun-grothendieck-derived-coproducts.

4. For any $L\in D(Y_{\mathrm{et}},C)$ and $K\in D(X_{\mathrm{et}},C)$ compose the proper
   projection isomorphism and the open-immersion tensor isomorphism: $$L\otimes^L Rp_{f,*}j_!K\
   \cong\ Rp_{f,*}(p_f^*L\otimes^L j_!K)\ \cong\ Rp_{f,*}j_!(j^*p_f^*L\otimes^L K)=F(f^*L\otimes^L
   K).$$ Both cited statements apply on the ordinary etale sites to arbitrary unbounded complexes
   and the given finite commutative ring $C$. The pullbacks here are termwise exact inverse images
   for the constant coefficient ring. Their composite is $f^*$, and $f^*V_Y=V_X$ because inverse
   image carries the constant ring and constant-module sheafification to the same constant
   coefficients. The composite is the compact-support projection map: the proper map is the counit
   projection map with the indicated tensor symmetries, and the open map is the extension-by-zero
   tensor map. In particular taking $L=V_Y$ proves the first displayed isomorphism in the
   statement. We retain the stronger formula for arbitrary $L$ for use in the next step.

   Uses: lemma-cohomology-projective-line-trace, lem-pur-etale-open-derived-tensor, prop-weil-pbc-
   inverse-image-modules-exact, def-weil-pbc-constant-sheaf.

5. Apply the compact-generation lemma to $X$ and $Y$; its hypotheses require finite type over the
   algebraically closed field and invertibility of $\ell$, not separatedness of either scheme over
   $k$. Let $(E_s)$ be its family on $X$, and include all integer shifts in the indexing set. To
   show that $F(E_s)$ is compact, first its cohomology is bounded constructible: the constructible
   sheaf finiteness theorem applies to each of the finitely many constructible cohomology sheaves
   of $E_s$, and the successive good-truncation triangles give a finite Postnikov filtration, and
   exactness of $F$ gives constructibility of $F(E_s)$: the long exact cohomology sequence
   expresses each new cohomology sheaf as an extension of a kernel and a cokernel of maps between
   constructible sheaves, which are constructible. Suppose $E_s$ has Tor amplitude $[r,s']$. For
   every module sheaf $N$ on $Y$, $f^*N$ is a sheaf and step 4 gives $$F(E_s)\otimes^L N\ \cong\
   F(E_s\otimes^L f^*N).$$ The input on the right lies in $D^{[r,s']}$, so steps 2–3 place the
   output in $D^{[r,s'+2d]}$. Thus $F(E_s)$ has finite Tor amplitude, and compactness on $Y$
   follows from the compact-generation lemma. This argument allows nonregular finite rings $C$; no
   assertion that every finite $C$-module is perfect is used.

   Uses: lem-pur-etale-finite-ring-compact-generators, theorem-results-from-etale-theory, def-kun-
   truncations, thm-constructible-serre.

6. The adjunction $F\dashv G$ is the fixed one in the item. The test family $(E_s[n])$ consists of
   compact objects, detects isomorphisms, and has compact images under $F$ by step 5. All
   categories have set-indexed coproducts and the required locally small Hom spaces. Apply the
   compact-test right-adjoint coproduct theorem to conclude that $G$ preserves arbitrary
   coproducts. Explicitly its comparison $\bigoplus_iGM_i\to G(\bigoplus_iM_i)$ induces, on
   testing with $E_s[n]$, the isomorphism $$\bigoplus_i\operatorname{Hom}(FE_s[n],M_i)\ \cong\
   \operatorname{Hom}(FE_s[n],\bigoplus_iM_i),$$ by adjunction and compactness of $FE_s[n]$.
   Detection makes the comparison an isomorphism.

   Uses: theorem-existence-exceptional-inverse-image--1,
   lem-pur-etale-finite-ring-compact-generators, lem-sc- compact-tests-right-adjoint-coproducts.

7. Equip $G$ with the unique shift structure compatible with the exact functor $F$ and its fixed
   adjunction. The adjunction-shift theorem supplies it, with the counit equation
   $$\epsilon_{M[n]}=\epsilon_M[n]\circ c_{F,n,GM}\circ F(c_{G,n,M}).$$ The triangulated-right-
   adjoint theorem then makes $G$ exact with this structure. The constant-complex functor
   $V\mapsto V_T$ is exact and preserves coproducts: the constant presheaf functor does so
   sectionwise, and sheafification is exact and preserves all colimits. Passing to complexes
   preserves shifts and cones; termwise coproducts compute derived coproducts. For fixed $M$ it
   follows that $$A_M(V)=V_X\otimes^L GM,\qquad B_M(V)=G(V_Y\otimes^L M)$$ are exact functors of
   $V\in D(C\text{-}\mathrm{Mod})$ and preserve arbitrary coproducts, by the exactness and direct-
   sum properties of derived tensor and by step 6.

   Uses: lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint,
   lem-weil-pbc-site-r-module-presheaf-sheafification-exact, lem-sf-exact-functor-derived-
   triangulated, lem-kun-grothendieck-derived-coproducts,
   proposition-open-direct-image-preserves-finite, proposition-open-direct-image-preserves-finite.

8. The projection isomorphism of step 4 is natural, unital and compatible with shifts in the
   coefficient variable $L$. For the proper factor this is the ringed-topos projection-mate
   exactness theorem. For the open factor use the canonical extension-by-zero tensor map of the
   cited open tensor theorem. The extension-by-zero stalk theorem identifies its stalk with the
   identity where the point lies in $X$ and with $0\to0$ outside $X$; the stalk-tensor theorem
   identifies the tensor factors. These are equalities on sheaf maps: exactness and conservativity
   of geometric stalks detect zero morphisms by applying the stalk functors to the image of their
   difference. Apply this degreewise to complexes. These maps commute with the tensor differential
   $d(x\otimes y)=dx\otimes y+(-1)^{\deg x}x\otimes dy$ and with the usual shift constraints. When
   factors are interchanged, the symmetry sends $x\otimes y$ to $(-1)^{\deg x\deg y}y\otimes x$,
   so the same coefficient-shift square still commutes. The tensor-unit map is the identity under
   the unit constraints. Composition preserves shift compatibility; thus, denoting step 4's
   coefficient projection map by $P$, the transformation $P^{-1}_{V,GM}$ commutes with coefficient
   shifts and has $P^{-1}_{C,GM}=1_{FGM}$ under tensor-unit identifications.

   Uses: lem-weil-pbc-ringed-projection-mate-exact, lem-pur-etale-open-derived-tensor, def-kun-
   derived-tensor, lem-kun-tensor-unit, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-
   pbc-extension-by-zero-stalks, lem-pod-etale-stalk-tensor-scalar, prop-weil-pbc-geometric-
   stalks-exact, lemma-weil-pbc-geometric-stalk-conservative.

9. Define $\alpha_{V,M}:A_M(V)\to B_M(V)$ by transposing $$F(V_X\otimes^L
   GM)\xrightarrow{P^{-1}_{V,GM}}V_Y\otimes^L FGM\xrightarrow{1\otimes\epsilon_M}V_Y\otimes^L M.$$
   Naturality of $P$, of $\epsilon$, and of the adjunction bijection proves naturality in $V,M$.
   For completeness the coefficient shift square for $\alpha$ is obtained by transposing its two
   sides under $F\dashv G$: after using the equation for $\epsilon$ in step 7, the two transposes
   are precisely the coefficient shift square for $P^{-1}$ from step 8 followed by
   $1\otimes\epsilon_M$. That square commutes, and the adjunction bijection is injective, so
   $\alpha$ is compatible with the specified shifts. Under $V=C$, step 8 identifies the transpose
   with $\epsilon_M$. The adjunction triangle identity says the transpose of $1_{GM}$ is
   $\epsilon_M$; hence $\alpha_{C,M}=1_{GM}$.

   Uses: theorem-existence-exceptional-inverse-image--1,
   lem-weil-pbc-adjunction-shift-compatibility-unique, lem-kun-tensor-unit.

10. Fix $M$ and let $\mathcal L_M$ consist of the coefficient complexes $V$ for which
   $\alpha_{V,M}$ is invertible. It contains $C$ by step 9. Exactness of both functors and the
   proved shift compatibility imply that it is closed under shifts, distinguished triangles and
   retracts by the generating-class invertibility theorem. It is also closed under arbitrary
   coproducts: under the coproduct comparisons for $A_M$ and $B_M$, naturality along every
   coprojection identifies $\alpha_{\oplus V_i,M}$ with $\oplus\alpha_{V_i,M}$, which is
   invertible if each summand is. The derived-module free-generation theorem therefore gives
   $\mathcal L_M=D(C\text{-}\mathrm{Mod})$. Thus the second displayed map in the item is an
   isomorphism for every unbounded $V$ and $M$. Both maps are constructed from functors, natural
   maps and the fixed adjunction on the derived categories; changing resolutions computes these
   same maps, rather than defining a new comparison. This follows for the first map from its
   proper projection and open tensor construction in step 4, and for the second from the
   bijectivity of transposition. The argument uses generation only to propagate invertibility,
   never to infer equality of transformations from their values on generators, and asserts no
   tensor formula for $G$ with a nonconstant sheaf complex.

   Uses: lemma-checking-isomorphisms-constructible-complexes--1,
   lem-pc-derived-module-free-generation, lem-amb- proper-coproducts-projection,
   lem-pur-etale-open-derived-tensor, thm-amb-etale-exceptional- adjoint.
-/
theorem exceptionalConstantTensor
    (k : Type u) [Field k] [IsAlgClosed k] (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    [CharP k p] (hne : ell ≠ p)
    {X Y : Scheme.{u}} (xk : X ⟶ Spec (.of k)) (yk : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType xk] [LocallyOfFiniteType yk]
    [QuasiCompact xk] [QuasiCompact yk]
    (f : X ⟶ Y) (hf : f ≫ yk = xk)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ Nf : ℕ, ∀ (c : Compactification f)
      (C : Type (u + 1)) [CommRing C] [Finite C],
      (∃ n : ℕ, ∀ z : C, (ell : C) ^ n * z = 0) →
      (∀ (a : ℤ) (K : DerivedCategoryModule C X),
        _root_.DerivedCategory.IsLE K a →
          _root_.DerivedCategory.IsLE
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
            (a + Nf)) ∧
      (∀ (d : ℕ),
        (∀ y : Y, topologicalKrullDim
          (pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
              (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y)) ≤
            (d : ℕ∞)) →
        ∀ (a : ℤ) (K : DerivedCategoryModule C X),
          _root_.DerivedCategory.IsLE K a →
            _root_.DerivedCategory.IsLE
              ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
              (a + 2 * (d : ℤ))) ∧
      (∀ (G : DerivedCategoryModule C Y ⥤ DerivedCategoryModule C X)
        (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ G),
        ∃ P :
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⋙
              exceptionalCoefficientTensor C Y ≅
            exceptionalCoefficientTensor C X ⋙
              (Functor.whiskeringRight _ _ _).obj
                (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c),
          (∀ (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X),
            (P.hom.app K).app V = exceptionalConstantProjectionMap C c V K) ∧
          ∃ A : G ⋙ exceptionalCoefficientTensor C X ≅
              exceptionalCoefficientTensor C Y ⋙ (Functor.whiskeringRight _ _ _).obj G,
            ∀ (V : DerivedCategory (ModuleCat.{u + 1} C)) (M : DerivedCategoryModule C Y),
              (A.hom.app M).app V = adj.homEquiv _ _
                ((P.inv.app (G.obj M)).app V ≫
                  ((derivedTensor (ModuleCat.{u + 1} C) Y).obj
                    ((constantSheaf Y.smallEtaleTopology
                      (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)).map
                    (adj.counit.app M))) := by
  classical
  let : X.Over (Spec (.of k)) := ⟨xk⟩
  let : Y.Over (Spec (.of k)) := ⟨yk⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType xk›
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType yk›
  have : QuasiCompact (X ↘ Spec (.of k)) := ‹QuasiCompact xk›
  have : QuasiCompact (Y ↘ Spec (.of k)) := ‹QuasiCompact yk›
  have : f.IsOver (Spec (.of k)) := ⟨hf⟩
  by_cases hc : Nonempty (Compactification f)
  · obtain ⟨c₀⟩ := hc
    obtain ⟨_, _, _, ⟨d, hd⟩, _⟩ :=
      compactSupport_unbounded_amplitude.{u, u + 1} k p
        (Fact.out : p.Prime).pos ell hne X Y f c₀
    refine ⟨2 * d, ?_⟩
    intro c C _ _ hC
    have hCpow : ∃ n : ℕ, (ell : C) ^ n = 0 := by
      obtain ⟨n, hn⟩ := hC
      exact ⟨n, by simpa using hn 1⟩
    have hCsmul : ∃ n : ℕ, (ell ^ n : ℕ) • (1 : C) = 0 := by
      simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hCpow
    obtain ⟨_, _, _, _, hFC⟩ :=
      compactSupport_unbounded_amplitude.{u, u + 1} k p
        (Fact.out : p.Prime).pos ell hne X Y f c
    obtain ⟨-, -, -, hamp⟩ := hFC C hCsmul
    refine ⟨(hamp d hd).1, fun d' hd' ↦ (hamp d' hd').1, ?_⟩
    intro G adj
    obtain ⟨e, he, heconst, hpull⟩ :=
      etaleSupportProjectionShiftUnit k p ell (Fact.out : p.Prime).pos
        (Fact.out : ell.Prime) hne C hCpow f c
    let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c
    have horiginal (K : DerivedCategoryModule C X) (L : DerivedCategoryModule C Y) :
        IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app L) := by
      have hi : IsIso ((e.hom.app K).app L) := inferInstance
      rw [he.1] at hi
      change IsIso
        (((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).inv.app (F.obj K)).app L ≫
          (((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app L ≫
            F.map (((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
              ((upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.obj L)))) at hi
      have := IsIso.of_isIso_comp_left
        (((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).inv.app (F.obj K)).app L)
        (((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app L ≫
          F.map (((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
            ((upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.obj L)))
      exact IsIso.of_isIso_comp_right _
        (F.map (((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
          ((upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.obj L)))
    have hprojection (K : DerivedCategoryModule C X) (L : DerivedCategoryModule C Y) :
        IsIso (compactSupportProjectionMapOfCompactification C c K L) := by
      have := horiginal K L
      unfold compactSupportProjectionMapOfCompactification
      infer_instance
    obtain ⟨hX, hY, _, _, hGcop,
      ⟨hGshift, hGtri, hCounit, hconstX, hconstY, hconstCop, _⟩⟩ :=
      support_compactImages_adjoint_sums.{u, u + 1} (k := k) p ell
        (Fact.out : p.Prime) (Fact.out : ell.Prime) hne f c C hCpow G adj
        (2 * (d : ℤ)) (by positivity) (hamp d hd).2 hprojection
    have := hX
    have := hY
    have := hconstX
    have := hconstY
    have (I : Type (u + 1)) := hGcop I
    have hAdjShift : adj.CommShift ℤ := adjunction_commShift_of_counit adj hCounit
    let H : DerivedCategory (ModuleCat.{u + 1} C) ⥤ DerivedCategoryModule C Y :=
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) H :=
      (hconstCop I).2
    have (K : DerivedCategoryModule C X) (I : Type (u + 1)) :
        PreservesColimitsOfShape (Discrete I)
          ((derivedTensor (ModuleCat.{u + 1} C) X).flip.obj K) :=
      (derivedTensor_preservesDirectSums C X K).2 I
    have (M : DerivedCategoryModule C Y) (I : Type (u + 1)) :
        PreservesColimitsOfShape (Discrete I)
          ((derivedTensor (ModuleCat.{u + 1} C) Y).flip.obj M) :=
      (derivedTensor_preservesDirectSums C Y M).2 I
    let r := H.mapIso ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).mapIso
        (ULift.moduleEquiv : ULift.{0} C ≃ₗ[C] C).toModuleIso) ≪≫
        supportConstantUnitIso (ModuleCat.{u + 1} C) Y
    obtain ⟨AQ, hAQ⟩ := exists_restricted_generation (ModuleCat.{u + 1} C) C c H r e he G adj
    have hFinal := assemble_comparisons (ModuleCat.{u + 1} C) c H
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
      (exceptionalConstantPullbackIso C f) e he G adj AQ hAQ
    simpa only [action, exceptionalCoefficientTensor, exceptionalConstantProjectionMap]
      using hFinal
  · exact ⟨0, fun c ↦ False.elim (hc ⟨c⟩)⟩

end AlgebraicGeometry.Etale
