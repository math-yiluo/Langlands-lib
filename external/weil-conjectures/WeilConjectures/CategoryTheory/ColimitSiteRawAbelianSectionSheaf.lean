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
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import all WeilConjectures.CategoryTheory.ColimitSiteRawSectionSheaf
import WeilConjectures.CategoryTheory.ColimitSiteRawAbelianStageRestriction
import WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Filtered.Final

/-! # ColimitSiteRawAbelianSectionSheaf

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs; abelian colimits
as in Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-sheaf).

Proof: Fix an object Y of the limit category. A presentation is a stage t
above i, an object W at that stage, and an equality V_t(W) = Y. Refinements
transport W along the stage functor and the equality along the cocone equation.
The object-colimit hypothesis supplies a presentation, and eventual equality in
the object colimit gives common refinements. Equalizing parallel stage arrows
makes this category filtered. Adjunction uniqueness under hθ identifies all
refinement maps on the section groups and proves their coherence.

Compute each left Kan extension by its pointwise abelian colimit. Its elements
are finite sums of generators (W, x, f : Y → V_t(W)), modulo linearity and
restriction relations. Lift the finitely many f and their endpoints to a common
stage using harrows and hobjects. Restrict the transported sections there.
They now belong to one presentation group, so their sum is a single section.
Lift the finitely many relations witnessing any equality in the same manner;
Kan relations become restriction, linearity or transition identities. Eventual
arrow equality and hβmap make these identities hold at one refinement. This
identifies (colimit B)(Y) with the filtered presentation colimit, naturally in Y;
lifting two composable arrows verifies naturality and the presheaf laws.

For a Q-cover use hQ to choose an equality-transported image of a stage cover.
Its finite indexing set is the set of distinct arrows of that cover, by hfinite;
repeated image arrows cause no problem since their local sections agree. Lift
any finite family of local representatives and its pairwise overlap equations
to one later stage. Covering pullbacks exist and hpullback and hVpullback
identify their images with the limit-site pullbacks. The lifted matching data
therefore form the finite product/equalizer diagram for the transported cover,
which remains covering by hcover. Filtered abelian colimits commute with finite
products and equalizers. The stage sheaf equalizers thus give the equalizer for
the limit covering. With an empty cover the stage equalizer is the zero group,
so existence and uniqueness hold as well. Finite base change makes pullbacks
of finite covers covering, and finite composition and isomorphism covers extend
this condition to Q.toGrothendieck. This proves sheafness only; no comparison
with the canonical inverse image or zero-detection is used.
-/
theorem colimit_site_raw_abelian_section_isSheaf
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
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
 :
    Presheaf.IsSheaf Q.toGrothendieck (colimit B) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u})]
  have hQfinite : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y → Finite R.uncurry := by
    intro Y R hR
    obtain ⟨j, X, S, rfl, hS, rfl⟩ := (hQ Y R).mp hR
    have : Finite S.uncurry := hfinite j X S hS
    exact finite_map_cover (V.ι.app j).toFunctor S
  apply isSheaf_of_finite_cover_conditions Q hQfinite
  intro Y R hR
  obtain ⟨j, X, S, rfl, hS, rfl⟩ := (hQ Y R).mp hR
  obtain ⟨k, _, _, D, ⟨q⟩, _⟩ := colimit_site_raw_abelian_stage_restriction
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap j
  let D₀ := D ⋙ sheafToPresheaf (P j).toGrothendieck AddCommGrpCat.{u}
  let W := (Functor.whiskeringRight (F.obj j)ᵒᵖ AddCommGrpCat.{u} (Type u)).obj
    (forget AddCommGrpCat.{u})
  have hD : ∀ t : Under k, Presieve.IsSheafFor ((D₀ ⋙ W).obj t) S := by
    intro t
    have hs : Presieve.IsSheaf (P j).toGrothendieck
        ((D.obj t).obj ⋙ forget AddCommGrpCat.{u}) := by
      rw [← isSheaf_iff_isSheaf_of_type, ← Presheaf.isSheaf_iff_isSheaf_forget]
      exact (D.obj t).property
    exact hs.isSheafFor_of_mem_precoverage hS
  let : S.HasPairwisePullbacks := (P j).hasPairwisePullbacks_of_mem hS
  have hf : S.uncurry.Finite := Set.finite_coe_iff.mp (hfinite j X S hS)
  have hc := finitePresieve_isSheafFor_filteredColimit (D₀ ⋙ W)
    (W.mapCocone (colimit.cocone D₀))
    (isColimitOfPreserves W (colimit.isColimit D₀)) S hf hD
  have hs := Presieve.isSheafFor_iso (W.mapIso q) hc
  let vj := (V.ι.app j).toFunctor
  let : vj.PreservesPairwisePullbacks S := by
    constructor
    intro Z T f g hf hg
    exact hVpullback j X Z T S hS f g hf
  exact (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    vj ((colimit B) ⋙ forget AddCommGrpCat.{u}) S).mp hs

end CategoryTheory
