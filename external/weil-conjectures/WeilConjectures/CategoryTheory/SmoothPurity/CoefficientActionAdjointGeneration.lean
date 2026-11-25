/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.LocalizingIsoLocus
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Generation for the specified coefficient-action adjoint mate

Source: Zheng, Six operations and Lefschetz–Verdier formula for Deligne–Mumford stacks,
Construction 2.26, printed p. 15; Stacks Project, More on Algebra, Tag 09PB
(blueprint: lem-pur-coefficient-action-adjoint-generation).

The actions are curried with the category variable first and the coefficient variable second.
The mate is defined by the fixed adjunction's hom equivalence, without any choice of map.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uD vD uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The specified transpose of inverse projection comparison followed by the counit.
Source: Zheng, Construction 2.26, printed p. 15
(blueprint: lem-pur-coefficient-action-adjoint-generation). -/
noncomputable def coefficientActionAdjointMate
    {D : Type uD} {A : Type uA} {B : Type uB}
    [Category.{vD} D] [Category.{vA} A] [Category.{vB} B]
    (TA : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G)
    (P : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F) (V : D) (M : B) :
    (TA.obj (G.obj M)).obj V ⟶ G.obj ((TB.obj M).obj V) :=
  adj.homEquiv _ _ ((P.inv.app (G.obj M)).app V ≫ (TB.map (adj.counit.app M)).app V)

/-- The full subcategory of coefficients where the specified transpose is invertible.
Source: Zheng, Construction 2.26, and Stacks Project, Tag 09PB
(blueprint: lem-pur-coefficient-action-adjoint-generation). -/
def coefficientActionAdjointIsoLocus
    {D : Type uD} {A : Type uA} {B : Type uB}
    [Category.{vD} D] [Category.{vA} A] [Category.{vB} B]
    (TA : A ⥤ D ⥤ A) (TB : B ⥤ D ⥤ B) {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G)
    (P : F ⋙ TB ≅ TA ⋙ (Functor.whiskeringRight D A B).obj F) (M : B) : ObjectProperty D :=
  fun V ↦ IsIso (coefficientActionAdjointMate TA TB adj P V M)

/-- The adjoint coefficient-action mate is natural, normalized at the ring, compatible with
all coefficient shifts, and invertible on the entire unbounded derived module category.
The explicit isomorphism locus contains the ring and is closed under isomorphisms, all
integer shifts, distinguished cones, retracts, and arbitrary set-indexed coproducts.

Source: Zheng, Construction 2.26, printed p. 15; blueprint
`lemma-checking-isomorphisms-constructible-complexes--1`; Stacks Project, More on Algebra, Tag 09PB
(blueprint: lem-pur-coefficient-action-adjoint-generation).

Proof:
1. Set q = inverse projection comparison followed by the action on the counit. The
   adjunction hom equivalence defines alpha. For each coefficient, `mateEquiv` with the
   adjunction on both horizontal sides gives naturality in M. Naturality of P and the
   action gives naturality in V after applying the injective adjunction hom equivalence.
2. At the degree-zero ring, projection normalization rewrites q as the counit composed
   with F of the A-unit, after the inverse B-unit. Naturality of the B-unit and transposition
   give alpha followed by G of the B-unit equal to the A-unit. Both units are invertible,
   so the ring lies in the isomorphism locus.
3. Write a and b for the action shift comparisons. Shift compatibility of P and naturality
   of b in the counit give b q(V[n]) = q(V)[n] c_F F(a). Compatibility of the adjunction
   shifts gives epsilon(Y[n]) F(c_G inverse) = epsilon(Y)[n] c_F. These equalities show
   that alpha(V[n]) followed by the composite B-shift and a followed by alpha(V)[n]
   have equal inverse adjuncts. Injectivity gives the stated shift equation.
4. For each M, apply `lemma-checking-isomorphisms-constructible-complexes--1` to the two exact,
   coproduct-preserving coefficient functors and the shift-compatible transformation from
   steps 1 and 3. Its locus is triangulated, coproduct-closed and retract-closed. Naturality
   at an isomorphism conjugates components, giving repleteness. Step 2 supplies the ring.
5. All shifts of the ring are consequently in the locus. Apply
   `lem-pc-derived-module-free-generation`: coproducts, distinguished cones and retracts
   generate every coefficient object. Thus the locus is top and each specified alpha is
   invertible. No determination of a transformation by its generator value is asserted. -/
theorem coefficientActionAdjointGeneration
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A] [IsTriangulated A]
    [HasZeroObject B] [HasShift B ℤ] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    [HasCoproducts.{max u v} A] [HasCoproducts.{max u v} B]
    (TA : A ⥤ DerivedCategory (ModuleCat.{max u v} R) ⥤ A)
    (TB : B ⥤ DerivedCategory (ModuleCat.{max u v} R) ⥤ B)
    [∀ K : A, (TA.obj K).CommShift ℤ] [∀ M : B, (TB.obj M).CommShift ℤ]
    [∀ K : A, (TA.obj K).IsTriangulated] [∀ M : B, (TB.obj M).IsTriangulated]
    [∀ (K L : A) (f : K ⟶ L), NatTrans.CommShift (TA.map f) ℤ]
    [∀ (M N : B) (f : M ⟶ N), NatTrans.CommShift (TB.map f) ℤ]
    (uA : TA.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
      (ModuleCat.of R (ULift.{v} R))) ≅ 𝟭 A)
    (uB : TB.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
      (ModuleCat.of R (ULift.{v} R))) ≅ 𝟭 B)
    (F : A ⥤ B) (G : B ⥤ A) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (adj : F ⊣ G) [adj.CommShift ℤ]
    (P : F ⋙ TB ≅ TA ⋙
      (Functor.whiskeringRight (DerivedCategory (ModuleCat.{max u v} R)) A B).obj F)
    (hshift : ∀ (K : A) (n : ℤ) (V : DerivedCategory (ModuleCat.{max u v} R)),
      (P.hom.app K).app (V⟦n⟧) ≫ ((TA.obj K ⋙ F).commShiftIso n).hom.app V =
        ((TB.obj (F.obj K)).commShiftIso n).hom.app V ≫ ((P.hom.app K).app V)⟦n⟧')
    (hunit : ∀ K : A,
      (P.hom.app K).app ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
        (ModuleCat.of R (ULift.{v} R))) ≫ F.map (uA.hom.app K) = uB.hom.app (F.obj K))
    [∀ M : B, (TB.obj M ⋙ G).IsTriangulated]
    [∀ (M : B) (I : Type (max u v)),
      PreservesColimitsOfShape (Discrete I) (TA.obj (G.obj M))]
    [∀ (M : B) (I : Type (max u v)),
      PreservesColimitsOfShape (Discrete I) (TB.obj M ⋙ G)] :
    (∀ (V W : DerivedCategory (ModuleCat.{max u v} R)) (h : V ⟶ W) (M : B),
      (TA.obj (G.obj M)).map h ≫ coefficientActionAdjointMate TA TB adj P W M =
        coefficientActionAdjointMate TA TB adj P V M ≫ G.map ((TB.obj M).map h)) ∧
    (∀ (V : DerivedCategory (ModuleCat.{max u v} R)) (M N : B) (h : M ⟶ N),
      (TA.map (G.map h)).app V ≫ coefficientActionAdjointMate TA TB adj P V N =
        coefficientActionAdjointMate TA TB adj P V M ≫ G.map ((TB.map h).app V)) ∧
    (∀ M : B,
      coefficientActionAdjointMate TA TB adj P
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
            (ModuleCat.of R (ULift.{v} R))) M ≫ G.map (uB.hom.app M) =
        uA.hom.app (G.obj M)) ∧
    (∀ (M : B) (n : ℤ) (V : DerivedCategory (ModuleCat.{max u v} R)),
      coefficientActionAdjointMate TA TB adj P (V⟦n⟧) M ≫
          ((TB.obj M ⋙ G).commShiftIso n).hom.app V =
        ((TA.obj (G.obj M)).commShiftIso n).hom.app V ≫
          (coefficientActionAdjointMate TA TB adj P V M)⟦n⟧') ∧
    (∀ M : B,
      coefficientActionAdjointIsoLocus TA TB adj P M
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))) ∧
      (∀ (V W : DerivedCategory (ModuleCat.{max u v} R)) (_ : V ≅ W),
        coefficientActionAdjointIsoLocus TA TB adj P M V →
          coefficientActionAdjointIsoLocus TA TB adj P M W) ∧
      (∀ (n : ℤ) (V : DerivedCategory (ModuleCat.{max u v} R)),
        coefficientActionAdjointIsoLocus TA TB adj P M V →
          coefficientActionAdjointIsoLocus TA TB adj P M (V⟦n⟧)) ∧
      (∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{max u v} R)),
        T ∈ Pretriangulated.distinguishedTriangles →
        coefficientActionAdjointIsoLocus TA TB adj P M T.obj₁ →
        coefficientActionAdjointIsoLocus TA TB adj P M T.obj₂ →
          coefficientActionAdjointIsoLocus TA TB adj P M T.obj₃) ∧
      (∀ (V W : DerivedCategory (ModuleCat.{max u v} R)) (_ : Retract V W),
        coefficientActionAdjointIsoLocus TA TB adj P M W →
          coefficientActionAdjointIsoLocus TA TB adj P M V) ∧
      (∀ (I : Type (max u v)) (V : I → DerivedCategory (ModuleCat.{max u v} R))
          (S : DerivedCategory (ModuleCat.{max u v} R)) (ι : ∀ i : I, V i ⟶ S),
        IsColimit (Cofan.mk S ι) →
        (∀ i : I, coefficientActionAdjointIsoLocus TA TB adj P M (V i)) →
          coefficientActionAdjointIsoLocus TA TB adj P M S) ∧
      coefficientActionAdjointIsoLocus TA TB adj P M = ⊤ ∧
      ∀ V : DerivedCategory (ModuleCat.{max u v} R),
        IsIso (coefficientActionAdjointMate TA TB adj P V M)) := by
  let q (M : B) : TA.obj (G.obj M) ⋙ F ⟶ TB.obj M :=
    P.inv.app (G.obj M) ≫ TB.map (adj.counit.app M)
  let α (M : B) : TA.obj (G.obj M) ⟶ TB.obj M ⋙ G :=
    (TA.obj (G.obj M)).rightUnitor.inv ≫
      Functor.whiskerLeft (TA.obj (G.obj M)) adj.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (q M) G
  have hα (M : B) (V : DerivedCategory (ModuleCat.{max u v} R)) :
      (α M).app V = coefficientActionAdjointMate TA TB adj P V M := by
    simp [α, q, coefficientActionAdjointMate, adj.homEquiv_unit]
  have hV : ∀ (V W : DerivedCategory (ModuleCat.{max u v} R)) (h : V ⟶ W) (M : B),
      (TA.obj (G.obj M)).map h ≫ coefficientActionAdjointMate TA TB adj P W M =
        coefficientActionAdjointMate TA TB adj P V M ≫ G.map ((TB.obj M).map h) := by
    intro V W h M
    simpa only [← hα, Functor.comp_map] using (α M).naturality h
  have hM : ∀ (V : DerivedCategory (ModuleCat.{max u v} R)) (M N : B) (h : M ⟶ N),
      (TA.map (G.map h)).app V ≫ coefficientActionAdjointMate TA TB adj P V N =
        coefficientActionAdjointMate TA TB adj P V M ≫ G.map ((TB.map h).app V) := by
    intro V M N h
    unfold coefficientActionAdjointMate
    apply adj.homEquiv_naturality_left_square
    have hp := congr_app (P.inv.naturality (G.map h)) V
    have ht := congr_app (TB.map_comp (F.map (G.map h)) (adj.counit.app N)) V
    have hc := congr_app (congrArg TB.map (adj.counit.naturality h)) V
    dsimp at hp ht hc
    rw [← Category.assoc, hp, Category.assoc, ← ht, hc]
    simp [Functor.map_comp, Category.assoc]
  have hU : ∀ M : B,
      coefficientActionAdjointMate TA TB adj P
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
            (ModuleCat.of R (ULift.{v} R))) M ≫ G.map (uB.hom.app M) =
        uA.hom.app (G.obj M) := by
    intro M
    rw [coefficientActionAdjointMate, ← adj.homEquiv_naturality_right]
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, adj.homEquiv_counit]
    have hu := uB.hom.naturality (adj.counit.app M)
    dsimp at hu
    rw [Category.assoc, hu]
    dsimp
    rw [← Category.assoc, ← hunit (G.obj M)]
    simp only [Category.assoc]
    simp
  let p (K : A) : TB.obj (F.obj K) ≅ TA.obj K ⋙ F := P.app K
  have hP (K : A) : NatTrans.CommShift (p K).hom ℤ := by
    constructor
    intro n
    ext V
    exact (hshift K n V).symm
  have hq (M : B) : NatTrans.CommShift (q M) ℤ := by
    have := hP (G.obj M)
    change NatTrans.CommShift ((p (G.obj M)).inv ≫ TB.map (adj.counit.app M)) ℤ
    infer_instance
  have hαshift (M : B) : NatTrans.CommShift (α M) ℤ := by
    have := hq M
    dsimp only [α]
    infer_instance
  have hs : ∀ (M : B) (n : ℤ) (V : DerivedCategory (ModuleCat.{max u v} R)),
      coefficientActionAdjointMate TA TB adj P (V⟦n⟧) M ≫
          ((TB.obj M ⋙ G).commShiftIso n).hom.app V =
        ((TA.obj (G.obj M)).commShiftIso n).hom.app V ≫
          (coefficientActionAdjointMate TA TB adj P V M)⟦n⟧' := by
    intro M n V
    have := hαshift M
    simpa only [hα] using (NatTrans.shift_app_comm (α M) n V).symm
  refine ⟨hV, hM, hU, hs, ?_⟩
  intro M
  have := hαshift M
  let : IsGrothendieckAbelian.{max u v} (ModuleCat.{max u v} R) :=
    IsGrothendieckAbelian.of_equivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{v} R ≃+* R)).symm
  let : Abelian.HasKInjectiveResolutions (ModuleCat.{max u v} R) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max u v}
  obtain ⟨htri, hcop, hret, _⟩ :=
    NatTrans.isoLocus_localizing.{max u v} ⊥ _ _ (α M)
  have : (α M).isoLocus.IsTriangulated := htri
  have : (α M).isoLocus.IsStableUnderRetracts := hret.some
  have hring : (α M).isoLocus
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
        (ModuleCat.of R (ULift.{v} R))) := by
    rw [NatTrans.isoLocus_iff, hα]
    have hi := hU M
    have : IsIso (coefficientActionAdjointMate TA TB adj P
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))) M ≫ G.map (uB.hom.app M)) := by
      rw [hi]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map (uB.hom.app M))
  have hcones : ∀ T, T ∈ Pretriangulated.distinguishedTriangles →
      (α M).isoLocus T.obj₁ → (α M).isoLocus T.obj₂ → (α M).isoLocus T.obj₃ :=
    fun T ht h₁ h₂ ↦ (α M).isoLocus.ext_of_isTriangulatedClosed₃ T ht h₁ h₂
  have hsum : ∀ (I : Type (max u v)) (V : I → DerivedCategory (ModuleCat.{max u v} R))
      (S : DerivedCategory (ModuleCat.{max u v} R)) (ι : ∀ i : I, V i ⟶ S),
      IsColimit (Cofan.mk S ι) → (∀ i : I, (α M).isoLocus (V i)) →
        (α M).isoLocus S := by
    intro I V S ι hc hV
    have := (hcop I).some
    exact (α M).isoLocus.prop_of_isColimit hc (fun i ↦ hV i.as)
  have hall : ∀ V, (α M).isoLocus V := by
    intro V
    apply derivedModuleFreeGeneration R V (α M).isoLocus
    · intro n
      exact (α M).isoLocus.le_shift n _ hring
    · exact fun V S ι hc hV ↦ hsum _ V S ι hc hV
    · exact hcones
    · exact fun r h ↦ (α M).isoLocus.prop_of_retract r h
  have hall' : ∀ V, coefficientActionAdjointIsoLocus TA TB adj P M V := by
    intro V
    simpa only [NatTrans.isoLocus_iff, hα, coefficientActionAdjointIsoLocus] using hall V
  refine ⟨hall' _, ?_, ?_, ?_, ?_, ?_, ?_, hall'⟩
  · exact fun _ W _ _ ↦ hall' W
  · exact fun n V _ ↦ hall' (V⟦n⟧)
  · exact fun T _ _ _ ↦ hall' T.obj₃
  · exact fun V _ _ _ ↦ hall' V
  · exact fun _ _ S _ _ _ ↦ hall' S
  · exact top_unique (fun V _ ↦ hall' V)

end CategoryTheory
