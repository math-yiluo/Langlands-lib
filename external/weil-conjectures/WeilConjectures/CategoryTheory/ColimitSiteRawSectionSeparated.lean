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

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.CategoryTheory.ColimitSiteRawStageRestriction
import WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit
import Mathlib.CategoryTheory.Filtered.Final

/-! # Raw sections: separated on stage-image covers

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-separated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
finite-cover matching-family calculation, with the raw Kan presentation explicit.
(blueprint: lem-weil-pbc-colimit-site-raw-section-separated).

Proof: First compute raw sections by the pointwise Kan formula. A generator is
represented by a stage section and an arrow from the object in the limit site
to the image of its stage object. Move that arrow, its endpoints, and the stage
section to a common stage receiving i and the stage of the object, using the
object and arrow set-colimit hypotheses, and restrict the section along the
lifted arrow. This represents the generator at the lifted object. For any
finite chain of Kan relations, lift its arrows and equations to a later common
stage. Naturality of beta and hβmap identify each lifted relation with section
restriction or transport by theta. Conversely these operations are Kan
relations. Thus two representatives agree precisely when they agree after
further stage refinement. The unit condition hθ identifies theta with the
adjunction transpose of the unit at the target stage; uniqueness of transposes
makes these transports compatible with composition and with the stage sheaves.

For two sections with the same restrictions on the image of a stage cover R,
put their representatives at a common stage receiving that stage and i.
Enumerate the distinct arrows of R, a finite set by hfinite. The finitely many
equalities of restrictions hold at a single further stage by the equality
criterion just established and filteredness. hcover makes the transported R
a stage cover. The stage inverse-image sheaf is separated for this cover,
so the two represented sections are equal there. Their raw colimit classes
are therefore equal. Applying this to two amalgamations gives the assertion.
For the empty cover the stage sheaf has at most one section, so the same
argument applies without any restriction equalities to lift.
-/
theorem colimit_site_raw_section_isSeparatedFor
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
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
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
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (j : J) (X : F.obj j) (R : Presieve X) (hR : R ∈ P j X) :
    Presieve.IsSeparatedFor (colimit B) (R.map (V.ι.app j).toFunctor) := by
  obtain ⟨k, _, _, D, ⟨q⟩, _⟩ := colimit_site_raw_stage_restriction
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap j
  let D₀ := D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)
  have hD : ∀ t : Under k, Presieve.IsSheafFor (D₀.obj t) R := by
    intro t
    have hs :=
      (isSheaf_iff_isSheaf_of_type (P j).toGrothendieck (D.obj t).obj).mp
        (D.obj t).property
    exact hs.isSheafFor R ((P j).generate_mem_toGrothendieck hR)
  let : R.HasPairwisePullbacks := (P j).hasPairwisePullbacks_of_mem hR
  have hf : R.uncurry.Finite := Set.finite_coe_iff.mp (hfinite j X R hR)
  have hc := finitePresieve_isSheafFor_filteredColimit D₀
    (colimit.cocone D₀) (colimit.isColimit D₀) R hf hD
  have hs := (Presieve.isSheafFor_iso q hc).isSeparatedFor
  intro z x y hx hy
  apply hs.ext
  intro Y f hf
  exact (hx ((V.ι.app j).toFunctor.map f) ⟨hf⟩).trans
    (hy ((V.ι.app j).toFunctor.map f) ⟨hf⟩).symm

end CategoryTheory
