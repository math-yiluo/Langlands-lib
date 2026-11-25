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
import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.ColimitSiteFiniteSectionColimitPresentation
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Zero detection for source sections with finite covering axioms

Source: Stacks Project, Sites, Tag 0A35, the section formula and its adjunction
paragraph; Modules on Sites, Tag 03CO, abelian extension.
(blueprint: lem-weil-pbc-colimit-site-finite-unit-zero-detection).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, equation-compute-pullback-to-limit
and the presentation, sheaf-condition and adjunction paragraphs; abelian extension
by Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-finite-unit-zero-detection).

Proof: Fix a source-stage sheaf H and source object X. For a limit object Y,
use presentations by stage objects above j. The object and arrow set colimit
properties lift any finite family of objects, arrows and equations to one
stage. Filteredness and eventual equality make the category of presentations
filtered, equalize parallel refinements, and make the category above a given
presentation final. Take filtered abelian colimits of the stage inverse images
of H. Lifting restriction arrows and their equations defines a presheaf,
independent of lifts. Every Q-cover is a transported finite stage cover by hQ;
hVpullback identifies its covering pullbacks. The matching-family equalizer
is a finite limit of stage section groups, so filtered colimits preserve it.
This gives a sheaf, including the zero group for an empty cover. Only finite
indexed covering composition and base change are used. A morphism from this
sheaf to any sheaf T is a compatible family of stage maps. Transposing these
maps through the stage adjunctions gives exactly one map H to V(j)-restriction
of T. The identity presentation and unit give the inverse assignment. Thus
uniqueness of left adjoints identifies the constructed sheaf with V(j) inverse
image, compatibly with the unit. At V(j)(X), the presentations carrying X
forward are final. The section z is represented by the identity inverse-image
unit, and its image is the V(j) unit applied to z. Its equality with zero in
the filtered colimit is witnessed at a later stage. The refinement map out of
the identity presentation is the adjunction unit for d : j to k, by uniqueness
of adjuncts. All maps and transports are additive, so the other representative
is zero. This proves the asserted unit vanishing. If H is zero, d may be the
identity; an empty source stage has no X. No arbitrary section of an inverse
image, or family of supplied comparison maps, occurs in this assertion.
-/
theorem colimit_site_finite_unit_zero_detection
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
    (j : J) (H : Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (X : F.obj j) (z : H.obj.obj (op X))
    (hz : ((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).unit.app H).hom.app (op X) z = 0) :
    ∃ (k : J) (d : j ⟶ k),
      ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).unit.app H).hom.app (op X) z = 0 := by
  obtain ⟨D, e, c, β, α, ⟨hc⟩, hstage, hlimit⟩ :=
    colimit_site_finite_section_colimit_presentation
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback j H X
  let i : Under j := Under.mk (𝟙 j)
  have hrep : c.ι.app i (e.app i z) = c.ι.app i 0 := by
    apply ((ConcreteCategory.isIso_iff_bijective β.hom).mp inferInstance).1
    have hu := ConcreteCategory.congr_hom (hlimit i) z
    change β.hom (c.ι.app i (e.app i z)) = _ at hu
    rw [map_zero, map_zero]
    exact hu.trans hz
  obtain ⟨a, f, hf⟩ := (hc.eq_iff' (e.app i z) 0).mp hrep
  have hn := ConcreteCategory.congr_hom (e.naturality f) z
  have he : e.app a z = 0 := by
    change e.app a z = D.map f (e.app i z) at hn
    rw [map_zero] at hf
    exact hn.trans hf
  refine ⟨a.right, a.hom, ?_⟩
  have hu := ConcreteCategory.congr_hom (hstage a) z
  change (α a).hom (e.app a z) = _ at hu
  rw [he, map_zero] at hu
  exact hu.symm

end CategoryTheory
