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
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Group.Subgroup.Lattice
import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionDiagram
import all WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImageRefinement
import WeilConjectures.CategoryTheory.ColimitSiteFiniteSectionEventualZero

/-! # A bound on the kernel of a colimit-site inverse-image unit

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem arrow_zero_iff {A B C : AddCommGrpCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (h : Arrow.mk f = Arrow.mk g) (x : A) : f x = 0 ↔ g x = 0 := by
  obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  subst C
  have he : f = g := by simpa using hf
  rw [he]

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section formula and its presentation, sheaf and adjunction paragraphs; abelian
interpretation in Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-abelian-unit-kernel-bound)

Proof: Transpose the canonical limit unit and each later-stage unit through the
source-stage adjunction. The transposes satisfy the unit equations by the
adjunction bijection. The existing section-diagram construction evaluates these
maps at X, producing a coherent abelian diagram D, its section identifications
E, and a cocone K identified with the limit inverse-image section group.

Send x through the unit for the identity transition and then through E inverse.
The limit-unit equation and the cocone equation show this element has zero K
image. Apply the finite section eventual-zero theorem, whose independent raw
Kan-extension route uses only the object and arrow colimits, finite covers and
covering pullbacks. It gives a later diagram transition killing this element.
The diagram transition equation and the stage-unit equation identify its zero
image with the later source-unit image of x. Thus x lies in one later kernel,
and hence in their supremum. Arrow equality transports zero across the endpoint
identifications. This proof does not choose an arbitrary group from existence:
the section-diagram theorem is proved and its data have the stated isomorphisms.

Edge cases: zero sections belong to every kernel; the constant identity diagram
has zero kernels; an empty source category has no X. No nonempty-cover assumption
or preservation of all limits by a transition is needed.
-/
theorem colimit_site_abelian_unit_kernel_bound
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
    (X : F.obj j) :
    (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).unit.app H).hom.app (op X)).hom.ker ≤
      ⨆ a : Under j,
        (((sheafAdjunctionContinuous (F.map a.hom).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P a.right).toGrothendieck).unit.app H).hom.app
            (op X)).hom.ker := by
  classical
  have hα (t : Under j) := exists_transition (P j).toGrothendieck
    (P t.right).toGrothendieck Q.toGrothendieck (F.map t.hom).toFunctor
    (V.ι.app t.right).toFunctor (V.ι.app j).toFunctor
    (congrArg Cat.Hom.toFunctor (V.w t.hom)) H
  let α := fun t ↦ (hα t).choose
  have hα' := fun t ↦ (hα t).choose_spec
  have hθ (t t' : Under j) (b : t ⟶ t') := exists_transition (P j).toGrothendieck
    (P t.right).toGrothendieck (P t'.right).toGrothendieck
    (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map t'.hom).toFunctor
    (by change (F.map t.hom ≫ F.map b.right).toFunctor = _
        rw [← F.map_comp, Under.w b]) H
  let θ := fun t t' b ↦ (hθ t t' b).choose
  have hθ' := fun t t' b ↦ (hθ t t' b).choose_spec
  obtain ⟨D, E, K, e, hK, hD⟩ := colimit_site_abelian_section_diagram
    J F P V Q j H α θ hα' hθ' X
  intro x hx
  let t : Under j := Under.mk (𝟙 j)
  let η := ((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
    (P j).toGrothendieck (P t.right).toGrothendieck).unit.app H).hom.app (op X)
  let y : D.obj t := (E t).inv (η x)
  have hy : (K.ι.app t).hom y = 0 := by
    have hey : (E t).hom y = η x := by simp [y]
    have hz := (arrow_zero_iff _ _ (hα' t X) x).mpr hx
    change (α t).hom.app _ (η x) = 0 at hz
    have he : e.hom (K.ι.app t y) = 0 :=
      (arrow_zero_iff _ _ (hK t) y).mpr (by
        change (α t).hom.app _ ((E t).hom y) = 0
        rwa [hey])
    have he' : e.hom (K.ι.app t y) = e.hom 0 := by rw [he, map_zero]
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 he'
  obtain ⟨t', b, hb⟩ := colimit_site_finite_section_eventual_zero
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
    j H α θ hα' hθ' X D E K e hK hD t y hy
  have hd := arrow_zero_iff _ _ (hD t t' b) y
  have hzero : (θ t t' b).hom.app _ (η x) = 0 := by
    have hey : (E t).hom y = η x := by simp [y]
    have hz := hd.mpr (by change (E t').hom (D.map b y) = 0; rw [hb, map_zero])
    change (θ t t' b).hom.app _ ((E t).hom y) = 0 at hz
    rwa [hey] at hz
  have hunit := (arrow_zero_iff _ _ (hθ' t t' b X) x).mp hzero
  exact AddSubgroup.mem_iSup_of_mem t' hunit

end CategoryTheory
