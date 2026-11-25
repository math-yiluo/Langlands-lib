/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit

/-!
# Ordinary etale projective-line adjunction for finite coefficients

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-adjunction.md,
thm-amb-p1-decomposition.md and def-amb-p1-trace.md; Stacks Project, Tag 03PL
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Etale

/-- Select the uniquely normalized root and coefficient-line pullback comparisons. -/
private theorem exists_twistTransport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Nonempty (OrdinaryFiniteTwistTransport A N hA) := by
  obtain ⟨r, c, p, hcover, hr, hc, hrest⟩ := Scheme.etaleFiniteTwistPullback A N hN hA
  exact ⟨{
    roots := r
    line := fun f hY ↦ c f hY (by simpa using hY.map f.appTop.hom) 1
    roots_normalization := hr
    line_normalization := fun f hY ↦ hc f hY (by simpa using hY.map f.appTop.hom)
  }⟩

/-- Represent the specified Kummer classes using the proved, bijective class comparison. -/
private theorem exists_chernFamily (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) :
    ∃ c : OrdinaryFiniteP1ChernFamily A N hA, OrdinaryFiniteP1ChernFamilySpec A N hA c := by
  classical
  have h (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
      ∃ c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
          (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
        ordinaryFiniteP1ChernSpec A N hA S
          (affineTraceProjectiveInvertible N S hS) c := by
    have : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    have : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    exact (existsUnique_ordinaryFiniteP1Chern A N hA S
      (affineTraceProjectiveInvertible N S hS)).exists
  choose c hc using h
  exact ⟨c, hc⟩

/-- Assemble the two component triangles with their specified actual counit. -/
@[irreducible]
private def adjunctionOfComponentTriangles {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (hF : ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 _)
    (hG : ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 _) : F ⊣ G :=
  Adjunction.mkOfUnitCounit {
    unit := η
    counit := ε
    left_triangle := by
      ext X
      simpa only [NatTrans.comp_app, NatTrans.id, Functor.comp_obj, Functor.id_obj,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Category.id_comp, Category.comp_id] using hF X
    right_triangle := by
      ext Y
      simpa only [NatTrans.comp_app, NatTrans.id, Functor.comp_obj, Functor.id_obj,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id] using hG Y
  }

/-- Unit equation for the irreducible component-triangle constructor. -/
private theorem adjunctionOfComponentTriangles_unit
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (hF : ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 _)
    (hG : ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 _) :
    (adjunctionOfComponentTriangles F G η ε hF hG).unit = η := by
  unfold adjunctionOfComponentTriangles
  rfl

/-- Counit equation for the irreducible component-triangle constructor. -/
private theorem adjunctionOfComponentTriangles_counit
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (hF : ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 _)
    (hG : ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 _) :
    (adjunctionOfComponentTriangles F G η ε hF hG).counit = ε := by
  unfold adjunctionOfComponentTriangles
  rfl

/-- A fixed counit determines its unit; the diagonal theorem chooses no arbitrary data. -/
private theorem existsUnique_componentUnit {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (ε : G ⋙ F ⟶ 𝟭 D)
    (h : ∃ η : 𝟭 C ⟶ F ⋙ G,
      (∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 _) ∧
      (∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 _)) :
    ∃! η : 𝟭 C ⟶ F ⋙ G,
      (∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 _) ∧
      (∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 _) := by
  obtain ⟨η, hF, hG⟩ := h
  refine ⟨η, ⟨hF, hG⟩, ?_⟩
  intro η' hη'
  let a := adjunctionOfComponentTriangles F G η ε hF hG
  let a' := adjunctionOfComponentTriangles F G η' ε hη'.1 hη'.2
  have ha : a' = a := Adjunction.ext_counit (by
    simp only [a', a, adjunctionOfComponentTriangles_counit])
  have hu := congrArg Adjunction.unit ha
  simpa only [a', a, adjunctionOfComponentTriangles_unit] using hu

/-- Inverting a commuting splitting square and projecting derives its trace square. -/
private theorem trace_baseChange_of_decomposition
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) {X Y Z : C} {X' Y' Z' : D}
    (b : (X ⊞ Y) ≅ Z) (b' : (X' ⊞ Y') ≅ Z')
    (a : F.obj X ⟶ X') (e : F.obj Y ⟶ Y') (k : F.obj Z ⟶ Z')
    (h : F.map b.hom ≫ k =
      biprod.lift (F.map biprod.fst ≫ a) (F.map biprod.snd ≫ e) ≫ b'.hom) :
    F.map (b.inv ≫ biprod.snd) ≫ e = k ≫ b'.inv ≫ biprod.snd := by
  apply (cancel_epi (F.map b.hom)).mp
  rw [← Functor.map_comp_assoc, b.hom_inv_id_assoc]
  symm
  calc
    F.map b.hom ≫ k ≫ b'.inv ≫ biprod.snd =
        (F.map b.hom ≫ k) ≫ b'.inv ≫ biprod.snd := by rw [Category.assoc]
    _ = _ := by rw [h, Category.assoc, b'.hom_inv_id_assoc, biprod.lift_snd]

/-- The second component of a splitting has normalized trace one. -/
private theorem trace_chern_of_decomposition
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (b : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (hb : b.hom = biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
      (ordinaryFiniteP1ChernPushforward A N hA S c)) :
    ordinaryFiniteP1ChernPushforward A N hA S c ≫ b.inv ≫ biprod.snd =
      𝟙 (ordinaryFiniteUnit A S) := by
  have hc : biprod.inr ≫ b.hom = ordinaryFiniteP1ChernPushforward A N hA S c := by
    rw [hb, biprod.inr_desc]
  rw [← hc, Category.assoc, b.hom_inv_id_assoc, biprod.inr_snd]

attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteTensor

/-- Ordinary etale projective-line duality, with the scalar-extended Kummer class,
normalized trace and actual counit, on the entire derived categories. The chosen
transport is fixed by its roots-of-unity and pure-tensor normalizations; the
record's counit equation uses precisely the ordered projection map.
Source: blueprint proposition-adjunction-projective-line--1, lemma-cohomology-projective-line-trace,
and lemma-cohomology-projective-line-trace; Stacks Project, Tag 03PL
(auxiliary; not a blueprint node).

Proof: obtain the roots and pure-tensor normalized transport from
lem-asd-etale-finite-twist-pullback. The comparison
lem-asd-ordinary-finite-class-comparison identifies the actual integral-generator
class map with sheaf cohomology, so the Kummer class has a unique Chern representative
on every Noetherian projective line. Apply lem-asd-ordinary-finite-p1-kummer-maps to
these representatives. Its specified two-component maps are invertible; use asIso,
whose hom is exactly that map. The diagonal result
lem-asd-ordinary-finite-p1-diagonal-unit supplies a natural unit and both component
triangle equations for the explicitly constructed inverse-projection trace counit.
Adjunction.mkOfUnitCounit builds the adjunction with that actual counit. Its
normalization is the proved inverse-projection equation. The Chern trace equation
follows by precomposing the splitting with its second injection and cancelling the
isomorphism. Finally use the decomposition square for its first base-change equation.
Precompose the trace square with the image of the splitting hom, cancel the inverse,
and use biprod.lift_snd; this derives the second equation without another geometric
assumption. The diagonal result supplies the third, actual-counit equation.
-/
theorem exists_ordinaryFiniteP1Adjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
        OrdinaryFiniteP1Datum A N hA t S hS), OrdinaryFiniteP1BaseChange A N hA t d := by
  classical
  obtain ⟨t⟩ := exists_twistTransport N hN A hA
  obtain ⟨c, hc⟩ := exists_chernFamily N A hA
  obtain ⟨hiso, hbc⟩ := ordinaryFiniteP1_kummer_maps N hN A hA t c hc
  let b (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
    letI := hiso S hS
    asIso (ordinaryFiniteP1KummerMap A N hA t c S hS)
  have hb (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
      (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS := rfl
  obtain ⟨hη, hεbc⟩ := ordinaryFiniteP1_diagonal_unit N hN A hA t c hc b hb hbc
  choose η htriangle using fun (S : Scheme.{u}) [IsNoetherian S]
      (hS : IsUnit (N : Γ(S, ⊤))) ↦
    (existsUnique_componentUnit (ordinaryFinitePushforward A (ProjectiveLine S ↘ S))
      (ordinaryFiniteP1Right A N hA S)
      (ordinaryFiniteP1TraceCounit A N hA S (b S hS)) (hη S hS)).exists
  let adj (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
      ordinaryFinitePushforward A (ProjectiveLine S ↘ S) ⊣ ordinaryFiniteP1Right A N hA S :=
    adjunctionOfComponentTriangles _ _ (η S hS)
      (ordinaryFiniteP1TraceCounit A N hA S (b S hS))
      (htriangle S hS).1 (htriangle S hS).2
  have hadjcounit (S : Scheme.{u}) [IsNoetherian S]
      (hS : IsUnit (N : Γ(S, ⊤))) :
      (adj S hS).counit = ordinaryFiniteP1TraceCounit A N hA S (b S hS) :=
    adjunctionOfComponentTriangles_counit _ _ _ _ _ _
  let d (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
      OrdinaryFiniteP1Datum A N hA t S hS := {
    invertible_on_projectiveLine := affineTraceProjectiveInvertible N S hS
    chern := c S hS
    chern_spec := hc S hS
    decomposition := b S hS
    decomposition_hom := hb S hS
    trace_chern := trace_chern_of_decomposition A N hA t S hS (c S hS) (b S hS)
      (hb S hS)
    adjunction := adj S hS
    counit_normalization := by
      unfold OrdinaryFiniteP1CounitNormalization
      rw [hadjcounit]
      exact ordinaryFiniteP1TraceCounit_projection A N hA S (b S hS)
  }
  refine ⟨t, d, ?_⟩
  intro S' S _ _ f hS hS'
  have hdecomp :
      (ordinaryFinitePullback A f).map (b S hS).hom ≫
          ordinaryFiniteP1Exchange A f
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteShiftedLinePullback A N hA t
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              (affineTraceProjectiveInvertible N S hS)).hom =
        ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫ (b S' hS').hom := by
    simpa only [hb] using hbc f hS hS'
  refine ⟨hdecomp, ?_, ?_⟩
  swap
  · simpa only [d, hadjcounit] using hεbc f hS hS'
  have htrace := trace_baseChange_of_decomposition (ordinaryFinitePullback A f)
    (b S hS) (b S' hS') (ordinaryFiniteShiftedLinePullback A N hA t f hS).hom
    (ordinaryFiniteUnitPullback A f).hom
    (ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          (affineTraceProjectiveInvertible N S hS)).hom)
    hdecomp
  simpa only [OrdinaryFiniteP1Datum.trace, Category.assoc] using htrace

end AlgebraicGeometry.Etale
