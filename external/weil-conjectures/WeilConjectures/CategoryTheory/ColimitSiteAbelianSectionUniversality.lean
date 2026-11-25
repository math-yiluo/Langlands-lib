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
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionRepresentatives
import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionEventualEquality

/-! # Universality of the abelian stage-section cocone

Source: Stacks Project, Sites, Tag 0A35, and Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem arrow_apply_heq
    {A B C : AddCommGrpCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    (h : Arrow.mk f = Arrow.mk g) (x : A) : HEq (f x) (g x) := by
  have hc : B = C := congrArg Arrow.right h
  subst C
  rw [(Arrow.mk_inj _ _).mp h]

private theorem arrow_kernel_iff
    {A B C : AddCommGrpCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    (h : Arrow.mk f = Arrow.mk g) (x y : A) : f x = f y ↔ g x = g y := by
  have hc : B = C := congrArg Arrow.right h
  subst C
  rw [(Arrow.mk_inj _ _).mp h]

/-- Source: Stacks Project, Sites, Tag 0A35, the presentation, sheaf equalizer,
and adjunction paragraphs; abelian-group extension via Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-abelian-section-universality).

Proof: Construct sections at a limit object from all its presentations above i.
Object and arrow colimit representatives put finitely many presentations and
restriction arrows at one stage. Eventual equality makes their refinements
filtered and makes restrictions independent of representatives. The category
above a fixed presentation is final, by common refinement and eventual equality,
so its filtered section colimit computes the same group. A Q-cover is the image
of a finite stage cover. Its covering pullbacks are preserved; filtered colimits
of abelian groups commute with the finite products and equalizers in its sheaf
condition. Thus these groups form a sheaf, including zero sections for empty
covers. Maps from this sheaf to H are compatible stage maps. Adjunction sends
them to maps G to V_i's restriction of H. The identity presentation and the unit
provide the inverse correspondence; uniqueness of adjuncts verifies both inverse
identities and naturality. This identifies the constructed sheaf with the
canonical inverse image, compatibly with units. At V_i U, finality identifies
its section colimit with the diagram on Under i. The two unit equations uniquely
determine α and θ; hD identifies D's transitions with these maps, and hK
identifies K's legs through e with the canonical coprojections. Transport the
colimit universal property along E and e to get IsColimit K. The forgetful
functor on abelian groups preserves filtered colimits and finite limits and
reflects isomorphisms, justifying the equalizer and comparison arguments.
There is no U at an empty source stage, so that case is vacuous. All objects in
this statement are supplied data; the conclusion only proves a universal property.
-/
theorem colimit_site_abelian_section_universality
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
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (U : F.obj i)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (E : ∀ t : Under i, D.obj t ≅
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G).obj.obj (op ((F.map t.hom).toFunctor.obj U)))
    (K : Cocone D) (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
      i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op ((V.ι.app i).toFunctor.obj U)))
    (hK : ∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj U))))
    (hD : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫ (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) : Nonempty (IsColimit K) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  classical
  let T := forget AddCommGrpCat.{u}
  have : ReflectsColimit D T := reflectsColimit_of_reflectsIsomorphisms D T
  apply Nonempty.intro
  apply isColimitOfReflects T
  apply Types.FilteredColimit.isColimitOf' (D ⋙ T) (T.mapCocone K)
  · intro x
    obtain ⟨t, y, hy⟩ := colimit_site_abelian_section_representatives
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback i G α hα U
      (e.hom x)
    let z := (E t).inv y
    have hz : HEq (e.hom (K.ι.app t z))
        ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) y) := by
      have hz := arrow_apply_heq (hK t) z
      change HEq (e.hom (K.ι.app t z))
        ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) ((E t).hom z)) at hz
      have hEz : (E t).hom z = y := Iso.inv_hom_id_apply (E t) y
      rw [hEz] at hz
      exact hz
    have hzx : K.ι.app t z = x := by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      exact eq_of_heq (hz.trans hy)
    exact ⟨t, z, hzx.symm⟩
  · intro t x y hxy
    have hαxy : (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) ((E t).hom x) =
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) ((E t).hom y) := by
      apply (arrow_kernel_iff (hK t) x y).mp
      change e.hom (K.ι.app t x) = e.hom (K.ι.app t y)
      exact congrArg e.hom hxy
    obtain ⟨t', b, hb⟩ := colimit_site_abelian_section_eventual_equality
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback i G
      α θ hα hθ U t ((E t).hom x) ((E t).hom y) hαxy
    refine ⟨t', b, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (E t').hom).1
    exact (arrow_kernel_iff (hD t t' b) x y).mp hb

end CategoryTheory
