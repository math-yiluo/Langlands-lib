/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import WeilConjectures.CategoryTheory.FilteredColimitPreservesPullback
import WeilConjectures.CategoryTheory.ColimitSiteCoveringAxiomsHasPullbacks
import WeilConjectures.CategoryTheory.ColimitSiteCoveringAxiomsFiniteBaseChange
import WeilConjectures.CategoryTheory.ColimitSiteCoveringAxiomsFiniteComposition
import WeilConjectures.CategoryTheory.ColimitSiteCoveringAxiomsHasIsos

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
private theorem finite_pullback_cover
    {C : Type u} [SmallCategory C] (P : Precoverage C)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    {X Y : C} (R : Presieve X) (hR : R ∈ P X) (g : Y ⟶ X) :
    have := P.hasPullbacks_of_mem g hR
    R.pullbackArrows g ∈ P Y := by
  classical
  have := P.hasPullbacks_of_mem g hR
  let I := R.uncurry
  have : Finite I := hfinite X R hR
  let Z : I → C := fun i ↦ i.val.1
  let f : ∀ i : I, Z i ⟶ X := fun i ↦ i.val.2
  have heq : Presieve.ofArrows Z f = R := by
    apply le_antisymm
    · rintro _ _ ⟨i⟩
      exact i.property
    · intro T a ha
      exact Presieve.ofArrows.mk (⟨⟨T, a⟩, ha⟩ : I)
  have (i : I) : HasPullback (f i) g := R.hasPullback g i.property
  have hc := Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
    (J := P) f (heq ▸ hR) g
    (fun i ↦ pullback.snd (f i) g) (fun i ↦ pullback.fst (f i) g)
    (fun i ↦ (IsPullback.of_hasPullback (f i) g).flip)
  have hpb : Presieve.ofArrows (fun i ↦ pullback (f i) g)
      (fun i ↦ pullback.snd (f i) g) = R.pullbackArrows g := by
    apply le_antisymm
    · rintro _ _ ⟨i⟩
      exact Presieve.pullbackArrows.mk _ _ i.property
    · rintro _ _ ⟨T, a, ha⟩
      exact Presieve.ofArrows.mk (⟨⟨T, a⟩, ha⟩ : I)
  dsimp only
  rw [← hpb]
  exact hc

private theorem continuous_of_finite_pullbacks
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (U : C ⥤ D) (P : Precoverage C) (Q : Precoverage D)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ P X → R.map U ∈ Q (U.obj X))
    (hpres : ∀ (X Y Z : C) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U) :
    U.IsContinuous P.toGrothendieck Q.toGrothendieck := by
  constructor
  intro G
  have hG := G.property
  rw [isSheaf_iff_isSheaf_of_type] at hG
  rw [P.isSheaf_toGrothendieck_iff]
  intro X Y g R hR
  have := P.hasPullbacks_of_mem g hR
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate]
  have hT := finite_pullback_cover P hfinite R hR g
  let T := R.pullbackArrows g
  have : T.HasPairwisePullbacks := P.hasPairwisePullbacks_of_mem hT
  have : U.PreservesPairwisePullbacks T := by
    constructor
    intro Y Z f g hf hg
    exact hpres _ Y Z T hT f g hf
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  exact hG.isSheafFor_of_mem_precoverage (hcover _ T hT)

/-- The finite covering axioms for the transported precoverage.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-colimit-site-covering-axioms) -/
theorem colimit_site_covering_axioms
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)) :
        ∃ (_ : Q.HasIsos) (_ : Q.IsStableUnderFiniteComposition)
          (_ : Q.IsStableUnderFiniteBaseChange) (_ : Q.HasPullbacks), True := by
  refine ⟨colimit_site_covering_axioms_HasIsos J F P hfinite hcover
      hpullback V hobjects harrows Q hQ,
    colimit_site_covering_axioms_FiniteComposition J F P hfinite hcover
      hpullback V hobjects harrows Q hQ,
    colimit_site_covering_axioms_FiniteBaseChange J F P hfinite hcover
      hpullback V hobjects harrows Q hQ,
    colimit_site_covering_axioms_HasPullbacks J F P hfinite hcover
      hpullback V hobjects harrows Q hQ, trivial⟩

/-- Preservation of covering pullbacks and continuity for the transported precoverage.
Source: Stacks Project, Sites, Tags 09YL and 0A35.
(blueprint: lem-weil-pbc-colimit-site-covering-continuity) -/
theorem colimit_site_covering_continuity
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)) :
        (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor) ∧
          Nonempty (∀ j : J, (V.ι.app j).toFunctor.IsContinuous
            (P j).toGrothendieck Q.toGrothendieck) := by
  have _ := hcover
  have hpres : ∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (V.ι.app j).toFunctor := by
    intro j X Y Z R hR f g hf
    have := (P j).hasPullbacks_of_mem g hR
    have : HasPullback f g := R.hasPullback g hf
    exact filteredColimit_preservesPullback J F V hobjects harrows j f g
      (fun k a ↦ hpullback j k a X Y Z R hR f g hf)
  refine ⟨hpres, ⟨fun j ↦ ?_⟩⟩
  apply continuous_of_finite_pullbacks (V.ι.app j).toFunctor (P j) Q (hfinite j)
  · intro X R hR
    exact (hQ _ _).mpr ⟨j, X, R, rfl, hR, rfl⟩
  · exact hpres j

end CategoryTheory
