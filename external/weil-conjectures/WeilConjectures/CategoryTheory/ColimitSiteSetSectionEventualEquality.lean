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
public import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionDiagram
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionEvaluation
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionSheaf
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Connected
import WeilConjectures.CategoryTheory.FilteredColimitCategories

/-! # Equal stage-section images become equal after one refinement.

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-section-eventual-equality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem raw_comparison_iso
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    (P : GrothendieckTopology C) (Q : GrothendieckTopology D)
    (R : GrothendieckTopology E)
    [f.IsContinuous P Q] [g.IsContinuous Q R] [h.IsContinuous P R]
    (eh : f ⋙ g = h)
    (G : Sheaf P (Type u))
    (B : Eᵒᵖ ⥤ Type u)
    (β : ((sheafPullback f (Type u) P Q).obj G).obj ⟶ g.op ⋙ B)
    [B.IsLeftKanExtension β]
    (γ : B ⟶ ((sheafPullback h (Type u) P R).obj G).obj)
    (α : (sheafPullback f (Type u) P Q).obj G ⟶
      (g.sheafPushforwardContinuous (Type u) Q R).obj
        ((sheafPullback h (Type u) P R).obj G))
    (hγ : β ≫ Functor.whiskerLeft g.op γ = α.hom)
    (hα : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) P Q).unit.app G).hom.app
        (op X) ≫ α.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h (Type u) P R).unit.app G).hom.app
        (op X))) :
    IsIso ((presheafToSheaf R (Type u)).map γ) := by
  subst h
  let A := sheafAdjunctionContinuous f (Type u) P Q
  let A' := sheafAdjunctionContinuous g (Type u) Q R
  let AH := sheafAdjunctionContinuous (f ⋙ g) (Type u) P R
  let S := (sheafPullback f (Type u) P Q).obj G
  let H := (sheafPullback (f ⋙ g) (Type u) P R).obj G
  let raw := g.op.leftKanExtension S.obj
  let eB : B ≅ raw := B.leftKanExtensionUnique β raw (g.op.leftKanExtensionUnit S.obj)
  let δ := ((A.comp A').leftAdjointUniq AH).app G
  let κ := (A'.homEquiv S H).symm α
  have hκ : κ = δ.hom := by
    apply ((A.comp A').homEquiv G H).injective
    have hδ : (A.comp A').homEquiv G H δ.hom = AH.unit.app G :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app (A.comp A') AH G
    rw [hδ]
    change A.homEquiv G _ (A'.homEquiv S H κ) = AH.unit.app G
    rw [Equiv.apply_symm_apply, A.homEquiv_unit]
    ext X x
    exact congrArg (fun k ↦ k x) (Arrow.mk_injective _ _ (hα X.unop))
  have : IsIso κ := by rw [hκ]; infer_instance
  have heB : β ≫ Functor.whiskerLeft g.op eB.hom = g.op.leftKanExtensionUnit S.obj := by
    exact B.descOfIsLeftKanExtension_fac β raw (g.op.leftKanExtensionUnit S.obj)
  have heγ : eB.hom ≫ (g.op.leftKanExtension S.obj).descOfIsLeftKanExtension
      (g.op.leftKanExtensionUnit S.obj) H.obj α.hom = γ := by
    apply B.hom_ext_of_isLeftKanExtension β
    simp only [Functor.whiskerLeft_comp, ← Category.assoc, heB]
    rw [Functor.descOfIsLeftKanExtension_fac]
    exact hγ.symm
  let d := raw.descOfIsLeftKanExtension
    (g.op.leftKanExtensionUnit S.obj) H.obj α.hom
  have hd : (presheafToSheaf R (Type u)).map d ≫
      (sheafificationAdjunction R (Type u)).counit.app H = κ := by
    apply (A'.homEquiv S H).injective
    rw [Equiv.apply_symm_apply]
    dsimp [A', sheafAdjunctionContinuous]
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
    apply (fullyFaithfulSheafToPresheaf Q (Type u)).map_injective
    simp only [Iso.refl_hom, NatTrans.id_app, Functor.id_map]
    rw [Adjunction.comp_unit_app]
    change g.op.leftKanExtensionUnit S.obj ≫
      Functor.whiskerLeft g.op (toSheafify R raw) ≫
        Functor.whiskerLeft g.op (((presheafToSheaf R (Type u)).map d ≫
          (sheafificationAdjunction R (Type u)).counit.app H).hom) = α.hom
    rw [← Functor.whiskerLeft_comp]
    have ht : toSheafify R raw ≫
        (((presheafToSheaf R (Type u)).map d ≫
          (sheafificationAdjunction R (Type u)).counit.app H).hom) = d := by
      change toSheafify R raw ≫ sheafifyMap R d ≫
        ((sheafificationAdjunction R (Type u)).counit.app H).hom = d
      rw [← toSheafify_naturality_assoc]
      have hh := (sheafificationAdjunction R (Type u)).right_triangle_components H
      change toSheafify R H.obj ≫
        ((sheafificationAdjunction R (Type u)).counit.app H).hom = 𝟙 _ at hh
      rw [hh, Category.comp_id]
    rw [ht]
    exact raw.descOfIsLeftKanExtension_fac (g.op.leftKanExtensionUnit S.obj) H.obj α.hom
  have : IsIso ((presheafToSheaf R (Type u)).map d) := by
    have : IsIso ((presheafToSheaf R (Type u)).map d ≫
        (sheafificationAdjunction R (Type u)).counit.app H) := by
      rw [hd]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((sheafificationAdjunction R (Type u)).counit.app H)
  rw [← heγ, Functor.map_comp]
  infer_instance

private theorem raw_colimit_comparison_iso
    {I C : Type u} [SmallCategory I] [IsConnected I] [SmallCategory C]
    (Q : GrothendieckTopology C)
    (B : I ⥤ (Cᵒᵖ ⥤ Type u)) (T : Cᵒᵖ ⥤ Type u)
    (γ : B ⟶ (Functor.const I).obj T)
    [∀ t : I, IsIso ((presheafToSheaf Q (Type u)).map (γ.app t))] :
    IsIso ((presheafToSheaf Q (Type u)).map
      (colimit.desc B (Cocone.mk T γ))) := by
  let L := presheafToSheaf Q (Type u)
  let c := Cocone.mk T γ
  let τ : B ⋙ L ⟶ (Functor.const I).obj (L.obj T) :=
    { app := fun t ↦ L.map (γ.app t)
      naturality := by
        intro t t' b
        change L.map (B.map b) ≫ L.map (γ.app t') = L.map (γ.app t)
        rw [← L.map_comp]
        simp }
  have hτ (t : I) : IsIso (τ.app t) :=
    inferInstanceAs (IsIso (L.map (γ.app t)))
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  have ht : IsColimit (L.mapCocone c) := by
    have hh := (IsColimit.precomposeHomEquiv (asIso τ)
      (constCocone I (L.obj T))).symm (isColimitConstCocone I (L.obj T))
    refine IsColimit.ofIsoColimit hh (Cocone.ext (Iso.refl _) ?_)
    intro t
    simp [τ, c, Cocone.precompose, constCocone]
  let hs := isColimitOfPreserves L (colimit.isColimit B)
  have he : hs.desc (L.mapCocone c) = L.map (colimit.desc B c) := by
    apply hs.hom_ext
    intro t
    rw [hs.fac]
    change L.map (γ.app t) = L.map (colimit.ι B t) ≫ L.map (colimit.desc B c)
    rw [← L.map_comp, colimit.ι_desc]
  have hi : IsIso (hs.desc (L.mapCocone c)) :=
    hs.nonempty_isColimit_iff_isIso_desc.mp ⟨ht⟩
  rw [he] at hi
  exact hi

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-set-section-eventual-equality).

Equal stage-section images become equal after one refinement.

Proof: Construct the sheaf on the limit site from filtered colimits of stage
inverse-image sections over presentations of each object, as in Tag 0A35.
Finite presentations admit common refinements, and parallel refinements are
equalized by filteredness and eventual object and arrow equality. Lifting
restriction arrows defines the presheaf; lifting finite covers and preserving
covering pullbacks identifies its sheaf equalizers with filtered colimits of
stage equalizers. Commutation with finite limits, including empty products,
makes it a sheaf. Stage adjunctions identify maps from it to H with maps from
G to restriction of H along V i: transpose at every presentation in one
direction, and use the identity presentation and unit in the other. Uniqueness
of adjuncts proves these are inverse, giving the unit-compatible isomorphism
with the limit inverse image. Presentations coming from U are final over
V i U by common-stage lifting and eventual equality, so the evaluated set
colimit is indexed by Under i. If K.ι.app t x = K.ι.app t y, apply e.hom and hι.
The resulting stage sections E t x and E t y have equal images in this set
colimit, because hα identifies α with its coprojections. The same-stage equality
criterion for filtered colimits gives one b : t to t' at which they agree.
Uniqueness under hθ identifies this refinement map with θ. The transition
identity hm translates that equality into equality after applying E t' to
D.map b x and D.map b y. Cancel the isomorphism E t' to get the desired equality.
This claims only eventual equality for two given representatives; it neither
constructs a diagram nor asserts that every section has a representative.
-/
theorem colimit_site_set_section_eventual_equality
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
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (U : F.obj i)
    (D : Under i ⥤ Type u)
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (K : Cocone D)
    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
          (op ((V.ι.app i).toFunctor.obj U)))
    (hι : ∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U))))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) :
    ∀ (t : Under i) (x y : D.obj t), K.ι.app t x = K.ι.app t y →
      ∃ (t' : Under i) (b : t ⟶ t'), D.map b x = D.map b y := by
  classical
  obtain ⟨B, β, γ, hβ, hβmap, hγ⟩ := colimit_site_raw_section_diagram
    J F P V Q i G α hα θ hθ
  have hB := colimit_site_raw_section_isSheaf J F P hfinite hcover hpullback
    V hobjects harrows Q hQ hVpullback i G θ hθ B β hβ hβmap
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let φ : colimit B ⟶ H.obj := colimit.desc B (Cocone.mk H.obj γ)
  have hγiso (t : Under i) :
      IsIso ((presheafToSheaf Q.toGrothendieck (Type u)).map (γ.app t)) := by
    have : (B.obj t).IsLeftKanExtension (β t) := hβ t
    apply raw_comparison_iso (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor
      (V.ι.app i).toFunctor (P i).toGrothendieck (P t.right).toGrothendieck
      Q.toGrothendieck (congrArg Cat.Hom.toFunctor (V.w t.hom)) G
      (B.obj t) (β t) (γ.app t) (α t)
    · ext X x
      exact congrArg (fun k ↦ k x) (hγ t X.unop)
    · exact hα t
  have : IsConnected (Under i) := IsFiltered.isConnected (Under i)
  have : IsIso ((presheafToSheaf Q.toGrothendieck (Type u)).map φ) :=
    raw_colimit_comparison_iso Q.toGrothendieck B H.obj γ
  have : IsIso (sheafifyMap Q.toGrothendieck φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf Q.toGrothendieck (Type u)).map
      ((presheafToSheaf Q.toGrothendieck (Type u)).map φ)))
  have : IsIso (toSheafify Q.toGrothendieck (colimit B)) :=
    isIso_toSheafify Q.toGrothendieck hB
  have : IsIso (toSheafify Q.toGrothendieck H.obj) :=
    isIso_toSheafify Q.toGrothendieck H.property
  have : IsIso (φ ≫ toSheafify Q.toGrothendieck H.obj) := by
    rw [toSheafify_naturality]
    infer_instance
  have : IsIso φ :=
    IsIso.of_isIso_comp_right φ (toSheafify Q.toGrothendieck H.obj)
  obtain ⟨R, q, ⟨hR⟩, hRq⟩ := colimit_site_raw_section_evaluation
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap U D E H.obj γ
    (fun t ↦ (α t).hom) hγ hm
  intro t x y hxy
  have heq : K.ι.app t ≫ e.hom =
      R.ι.app t ≫ q.hom ≫ φ.app (op ((V.ι.app i).toFunctor.obj U)) :=
    Arrow.mk_injective _ _ ((hι t).trans (hRq t).symm)
  have hxy' : (R.ι.app t ≫ q.hom ≫
      φ.app (op ((V.ι.app i).toFunctor.obj U))) x =
      (R.ι.app t ≫ q.hom ≫
        φ.app (op ((V.ι.app i).toFunctor.obj U))) y := by
    rw [← heq]
    exact congrArg e.hom hxy
  have hRxy : R.ι.app t x = R.ι.app t y := by
    apply (q.toEquiv.injective)
    apply ((asIso (φ.app (op ((V.ι.app i).toFunctor.obj U)))).toEquiv.injective)
    exact hxy'
  exact (Types.FilteredColimit.isColimit_eq_iff' hR x y).mp hRxy

end CategoryTheory
