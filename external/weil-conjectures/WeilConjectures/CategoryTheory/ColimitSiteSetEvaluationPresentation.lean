/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.ColimitSiteStageSectionDiagram
import WeilConjectures.CategoryTheory.ColimitSiteSetSectionPresentation
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Colimits


/-! # General-object section functor presentation

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-evaluation-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem pullback_comp_iso
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (eh : f ⋙ g = h) :
    Nonempty (sheafPullback h (Type u) T R ≅
      sheafPullback f (Type u) T S ⋙ sheafPullback g (Type u) S R) := by
  subst h
  exact ⟨(sheafAdjunctionContinuous (f ⋙ g) (Type u) T R).leftAdjointUniq
    ((sheafAdjunctionContinuous f (Type u) T S).comp
      (sheafAdjunctionContinuous g (Type u) S R))⟩

private theorem arrow_precomp
    {C : Type*} [Category C] {X Y Z W : C}
    {f : X ⟶ Y} {g : X ⟶ Z} (h : Arrow.mk f = Arrow.mk g) (a : W ⟶ X) :
    Arrow.mk (a ≫ f) = Arrow.mk (a ≫ g) := by
  have e : Y = Z := congrArg Arrow.right h
  subst Z
  rw [Arrow.mk_inj] at h
  rw [h]

private theorem exists_unit_transition_nat
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (eh : f ⋙ g = h) (X : C) :
    ∃ (α : sheafPullback f (Type u) T S ⟶
        sheafPullback h (Type u) T R ⋙ g.sheafPushforwardContinuous (Type u) S R)
      (δ : sheafPullback f (Type u) T S ⋙ sheafToPresheaf S (Type u) ⋙
        (evaluation Dᵒᵖ (Type u)).obj (op (f.obj X)) ⟶
        sheafPullback h (Type u) T R ⋙ sheafToPresheaf R (Type u) ⋙
        (evaluation Eᵒᵖ (Type u)).obj (op (h.obj X))),
      (∀ (G : Sheaf T (Type u)) (Z : C),
        Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
          (op Z) ≫ (α.app G).hom.app (op (f.obj Z))) =
        Arrow.mk (((sheafAdjunctionContinuous h (Type u) T R).unit.app G).hom.app
          (op Z))) ∧
      ∀ G : Sheaf T (Type u), Arrow.mk (δ.app G) =
        Arrow.mk ((α.app G).hom.app (op (f.obj X))) := by
  subst h
  let A := sheafAdjunctionContinuous f (Type u) T S
  let H := sheafPullback (f ⋙ g) (Type u) T R
  let η : 𝟭 (Sheaf T (Type u)) ⟶ H ⋙
      g.sheafPushforwardContinuous (Type u) S R ⋙
      f.sheafPushforwardContinuous (Type u) T S :=
    (sheafAdjunctionContinuous (f ⋙ g) (Type u) T R).unit
  let α : sheafPullback f (Type u) T S ⟶
      H ⋙ g.sheafPushforwardContinuous (Type u) S R :=
    { app := fun G ↦ (A.homEquiv G _).symm (η.app G)
      naturality := by
        intro G G' m
        apply (A.homEquiv G _).injective
        rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
        simpa using η.naturality m }
  let δ : sheafPullback f (Type u) T S ⋙ sheafToPresheaf S (Type u) ⋙
      (evaluation Dᵒᵖ (Type u)).obj (op (f.obj X)) ⟶
      H ⋙ sheafToPresheaf R (Type u) ⋙
      (evaluation Eᵒᵖ (Type u)).obj (op ((f ⋙ g).obj X)) :=
    { app := fun G ↦ (α.app G).hom.app (op (f.obj X))
      naturality := by
        intro G G' m
        exact congrArg (fun k ↦ k.hom.app (op (f.obj X))) (α.naturality m) }
  refine ⟨α, δ, ?_, fun _ ↦ rfl⟩
  intro G Z
  have he := (A.homEquiv G
    ((g.sheafPushforwardContinuous (Type u) S R).obj (H.obj G))).apply_symm_apply
      (η.app G)
  rw [A.homEquiv_unit] at he
  exact congrArg (fun k ↦ Arrow.mk (k.hom.app (op Z))) he

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section formula, adjunction paragraph, and final left-exactness paragraph.
(blueprint: lem-weil-pbc-colimit-site-set-evaluation-presentation).

Proof: At t : Under i evaluate the stage inverse image along F(t.hom) at
F(t.hom)(U). Transpose the unit at t' through the adjunction at t to obtain
the refinement map; Under.w identifies the composite restriction functor.
Injectivity of the hom equivalence proves identities and composition, and its
naturality proves functoriality in the source sheaf. This constructs L. Each
L followed by evaluation is a stage inverse image followed by sheaf sections,
hence preserves finite limits. Objectwise detection gives preservation by L.
Use the unit-transposed maps to the inverse image along V i as its colimit
cocone. The specified-transition section formula identifies this cocone as a
colimit for every sheaf G. Explicitly compare its diagram with the diagram D
in that formula using the objectwise section isomorphisms; the transition
equation proves naturality of the comparison. Transport the colimit structure
along this diagram isomorphism and the section isomorphism of cocone points.
The universal property gives the map from L followed by colim to evaluation
of V i inverse image. Coprojection equations and naturality of the unit
transposes prove this map natural in G. Its components are isomorphisms
because the cocones are colimits, hence it is a natural isomorphism.
The under category is filtered because J is filtered. Empty source stages
have no U, while empty covers are included in the existing section formula.
-/
private theorem source_evaluation_presentation
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
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (U : F.obj i) :
    ∃ (L : Sheaf (P i).toGrothendieck (Type u) ⥤ (Under i ⥤ Type u)),
          Nonempty (PreservesFiniteLimits L) ∧
          Nonempty ((sheafPullback (V.ι.app i).toFunctor (Type u)
            (P i).toGrothendieck Q.toGrothendieck ⋙
              sheafToPresheaf Q.toGrothendieck (Type u) ⋙
              (evaluation V.ptᵒᵖ (Type u)).obj
                (op ((V.ι.app i).toFunctor.obj U))) ≅ L ⋙ colim) := by
  classical
  obtain ⟨L, E, θ, hθ, hmL⟩ := colimit_site_stage_section_diagram J F P i U
  have hlim : PreservesFiniteLimits L := by
    apply preservesFiniteLimits_of_evaluation
    intro t
    let ev := (evaluation (F.obj t.right)ᵒᵖ (Type u)).obj
      (op ((F.map t.hom).toFunctor.obj U))
    let incl := sheafToPresheaf (P t.right).toGrothendieck (Type u)
    have : PreservesFiniteLimits (incl ⋙ ev) := comp_preservesFiniteLimits incl ev
    have : PreservesFiniteLimits
        (sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⋙ incl ⋙ ev) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso (E t).symm
  let T := sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck ⋙
    sheafToPresheaf Q.toGrothendieck (Type u) ⋙
    (evaluation V.ptᵒᵖ (Type u)).obj (op ((V.ι.app i).toFunctor.obj U))
  have hα (t : Under i) := exists_unit_transition_nat
    (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor (V.ι.app i).toFunctor
    (P i).toGrothendieck (P t.right).toGrothendieck Q.toGrothendieck
    (congrArg Cat.Hom.toFunctor (V.w t.hom)) U
  choose α δ hα hδ using hα
  let β (t : Under i) : L ⋙ (evaluation (Under i) (Type u)).obj t ⟶ T :=
    (E t).hom ≫ δ t
  have hsec (G : Sheaf (P i).toGrothendieck (Type u)) :=
    colimit_site_set_section_presentation J F P hfinite hcover hpullback
      V hobjects harrows Q hQ hVpullback i G
      (fun t ↦ (α t).app G) (fun t X ↦ hα t G X)
      (fun t t' b ↦ (θ t t' b).app G) (hθ G) U
  have hpoint (G : Sheaf (P i).toGrothendieck (Type u)) :
      ∃ ι : L.obj G ⟶ (Functor.const (Under i)).obj (T.obj G),
        (∀ t, ι.app t = (β t).app G) ∧
          Nonempty (IsColimit (Cocone.mk (T.obj G) ι)) := by
    obtain ⟨D, E', K, e, ⟨hK⟩, hι, hmD⟩ := hsec G
    have hn (t t' : Under i) (b : t ⟶ t') :
        D.map b ≫ (E' t' ≪≫ ((E t').app G).symm).hom =
          (E' t ≪≫ ((E t).app G).symm).hom ≫ (L.obj G).map b := by
      have hh := arrow_precomp (hmL G t t' b)
        ((E' t).hom ≫ ((E t).app G).inv)
      change Arrow.mk ((E' t).hom ≫ ((E t).app G).inv ≫
        ((E t).app G).hom ≫ _) = _ at hh
      simp only [Iso.inv_hom_id_assoc] at hh
      have hh' := (hmD t t' b).symm.trans hh
      have he := Arrow.mk_injective _ _ hh'
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [← Category.assoc, he]
      simp
    let q : D ≅ L.obj G := NatIso.ofComponents
      (fun t ↦ E' t ≪≫ ((E t).app G).symm) (fun {t t'} b ↦ hn t t' b)
    let s : Cocone (L.obj G) :=
      (Cocone.precompose q.inv).obj (K.extend e.hom)
    refine ⟨s.ι, ?_, ?_⟩
    · intro t
      have hh := arrow_precomp (hδ t G) (E' t).hom
      have he := Arrow.mk_injective _ _ ((hι t).trans hh.symm)
      change q.inv.app t ≫ (K.ι.app t ≫ e.hom) = _
      rw [he]
      simp [q, β]
    · change Nonempty (IsColimit s)
      exact ⟨(IsColimit.precomposeInvEquiv q (K.extend e.hom)).symm
        (hK.extendIso e.hom)⟩
  choose ι hβ hcolim using hpoint
  let s (G : Sheaf (P i).toGrothendieck (Type u)) := Cocone.mk (T.obj G) (ι G)
  let τ : L ⋙ colim ⟶ T :=
    { app := fun G ↦ colimit.desc (L.obj G) (s G)
      naturality := by
        intro G G' m
        apply colimit.hom_ext
        intro t
        simp only [Functor.comp_map]
        rw [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
        change (L.map m).app t ≫ (ι G').app t = (ι G).app t ≫ T.map m
        rw [hβ, hβ]
        exact (β t).naturality m }
  have hτ (G : Sheaf (P i).toGrothendieck (Type u)) : IsIso (τ.app G) := by
    change IsIso (colimit.desc (L.obj G) (s G))
    exact ((colimit.isColimit (L.obj G)).nonempty_isColimit_iff_isIso_desc).mp
      (hcolim G)
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact ⟨L, ⟨hlim⟩, ⟨(asIso τ).symm⟩⟩


/-- Source: Stacks Project, Sites, Tag 0A35, general-object section construction and
final left-exactness paragraph.
(blueprint: lem-weil-pbc-colimit-site-set-evaluation-presentation).

Proof: Represent Y by an object X of some stage j, using joint surjectivity
of the object colimit. Choose a common stage k receiving i and j, and transport
X to U in F(k). Cocone naturality identifies V(k)(U) with Y. The helper
source_evaluation_presentation constructs the section diagram over Under k,
proves its finite-limit preservation objectwise and proves its natural colimit
formula from the specified-transition section-presentation theorem. Compose
this diagram with inverse image from stage i to k. This preserves finite limits
by the transition hypothesis. Composition of the inverse-image adjunctions and
uniqueness of left adjoints identify V(i) inverse image with the composite
through k. Whisker this isomorphism by sections at Y and compose it with the
source-stage formula to obtain the required natural isomorphism. Under k is
small and filtered. An empty limit category has no Y. An empty source stage
causes no extra case: the transition hypothesis supplies finite-limit
preservation, including terminal objects, for the composite used here.
-/
theorem colimit_site_set_evaluation_presentation
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
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (Y : V.pt) :
    ∃ (A : Type u) (c : SmallCategory A), letI := c
      ∃ (hf : IsFiltered A), letI := hf
        ∃ (L : Sheaf (P i).toGrothendieck (Type u) ⥤ (A ⥤ Type u)),
          Nonempty (PreservesFiniteLimits L) ∧
          Nonempty ((sheafPullback (V.ι.app i).toFunctor (Type u)
            (P i).toGrothendieck Q.toGrothendieck ⋙
              sheafToPresheaf Q.toGrothendieck (Type u) ⋙
              (evaluation V.ptᵒᵖ (Type u)).obj (op Y)) ≅ L ⋙ colim) := by
  classical
  obtain ⟨j, X, hX⟩ := Types.jointly_surjective (F ⋙ Cat.objects) hobjects Y
  let k := IsFiltered.max i j
  let a : i ⟶ k := IsFiltered.leftToMax i j
  let b : j ⟶ k := IsFiltered.rightToMax i j
  let U : F.obj k := (F.map b).toFunctor.obj X
  have hU : (V.ι.app k).toFunctor.obj U = Y := by
    change (F.map b ≫ V.ι.app k).toFunctor.obj X = Y
    rw [V.w b]
    exact hX
  obtain ⟨L, ⟨hL⟩, ⟨e⟩⟩ := source_evaluation_presentation
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback k U
  let B := sheafPullback (F.map a).toFunctor (Type u)
    (P i).toGrothendieck (P k).toGrothendieck
  have : PreservesFiniteLimits L := hL
  have hBL : PreservesFiniteLimits (B ⋙ L) := comp_preservesFiniteLimits B L
  obtain ⟨ec⟩ := pullback_comp_iso
    (F.map a).toFunctor (V.ι.app k).toFunctor (V.ι.app i).toFunctor
    (P i).toGrothendieck (P k).toGrothendieck Q.toGrothendieck
    (congrArg Cat.Hom.toFunctor (V.w a))
  refine ⟨Under k, inferInstance, inferInstance, B ⋙ L, ⟨hBL⟩, ?_⟩
  rw [← hU]
  exact ⟨Functor.isoWhiskerRight ec
      (sheafToPresheaf Q.toGrothendieck (Type u) ⋙
        (evaluation V.ptᵒᵖ (Type u)).obj (op ((V.ι.app k).toFunctor.obj U))) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft B e ≪≫
      (Functor.associator B L colim).symm⟩

end CategoryTheory
