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
import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits

import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionRepresentatives
import WeilConjectures.CategoryTheory.ColimitSiteFiniteSectionEventualZero

/-! # Bijectivity of the finite-site section comparison

Source: Stacks Project, Sites, Tag 0A35, independence of presentations and
identification by adjunction; abelian extension via Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-finite-section-comparison-bijective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem arrow_map_apply_heq
    {C : Type*} [Category C] (H : C ⥤ Type u)
    {A B B' : C} {f : A ⟶ B} {g : A ⟶ B'}
    (h : Arrow.mk f = Arrow.mk g) (x : H.obj A) :
    HEq (H.map f x) (H.map g x) := by
  have hb : B = B' := congrArg Arrow.right h
  subst B'
  rw [(Arrow.mk_inj _ _).mp h]

/-- Source: Stacks Project, Sites, Tag 0A35, the general-object presentation,
sheaf equalizer and adjunction paragraphs; Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-finite-section-comparison-bijective).

Proof: A presentation of a limit object Y is a triple (t, W, p), with
t : Under i, W in F(t.right), and p : V(t.right)(W) = Y. A refinement
b : t to t' satisfies F(b.right)(W) = W', with the corresponding endpoint
transports. The section group at this presentation is L_t(W), where
L_t = F(t.hom) inverse image of G. Use the unique adjunct of the stage
unit for every refinement, evaluated at W and transported at the endpoint,
as its transition map. Adjunct uniqueness gives identity and composition.

The presentation category is nonempty: lift Y to a stage using hobjects,
then choose a common stage with i. For two presentations, a common stage
in Under i followed by eventual equality of their object representatives
gives a common refinement with equal W. Parallel refinements are equalized
by filteredness. Define the section group at Y as this filtered colimit.
To restrict along f : Y to Y', lift f by harrows and move its stage, i,
and chosen endpoint presentations to a common stage. Eventual object
equality corrects the endpoints. Two such lifts agree after refinement
by harrows; naturality of the adjunct transition maps then proves that
restriction is independent of these choices. Lift finitely many arrows
together to prove the presheaf identity and composition laws. Thus this
construction defines an abelian presheaf. A Q-cover comes from a finite stage cover;
the covering pullbacks are preserved. Lift the finite matching-family data
and equations to a common stage. Filtered abelian colimits commute with the
finite products and equalizers expressing the sheaf condition, so this is a
sheaf. Empty covers give the zero group.

Maps from this sheaf to any sheaf T are compatible stage maps. The stage
adjunctions identify these with maps G to restriction of T along V i; the
identity presentation gives the reverse assignment. Uniqueness of adjuncts
and the colimit universal property give inverse natural correspondences.
The unique unit-compatible left-adjoint isomorphism identifies this sheaf
with the canonical inverse image. At V i U the carried-forward presentations
are final: lift representatives and arrows to common stages and equalize
using the object and arrow colimits. Thus the comparison from the stage
section colimit to the canonical inverse-image sections is an isomorphism.
The unit equations uniquely characterize α and θ, while hD and hK identify
the supplied diagram and cocone with this comparison via E and e. Hence
colimit.desc D K is bijective. This asserts only the comparison property of
supplied coherent data, and constructs none of the diagrams, maps or units
required by the parent theorem. Empty source stages have no U; identity and
constant diagrams reduce to the ordinary identity comparison.
-/
theorem colimit_site_finite_section_comparison_bijective
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
      Arrow.mk (D.map b ≫ (E t').hom)) : Function.Bijective (colimit.desc D K) := by
  have hzero := colimit_site_finite_section_eventual_zero
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
      i G α θ hα hθ U D E K e hK hD
  constructor
  · apply (injective_iff_map_eq_zero (colimit.desc D K).hom).2
    intro z hz
    obtain ⟨t, x, rfl⟩ := Concrete.colimit_exists_rep D z
    have hx : (K.ι.app t).hom x = 0 := by
      change (colimit.ι D t ≫ colimit.desc D K).hom x = 0 at hz
      rwa [colimit.ι_desc] at hz
    obtain ⟨t', b, hb⟩ := hzero t x hx
    calc
      (colimit.ι D t).hom x = (colimit.ι D t').hom ((D.map b).hom x) :=
        (colimit.w_apply D b x).symm
      _ = 0 := by rw [hb, map_zero]
  · intro y
    obtain ⟨t, x, hx⟩ := colimit_site_abelian_section_representatives
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
      i G α hα U (e.hom y)
    let z := (E t).inv x
    have hz : HEq (e.hom (K.ι.app t z))
        ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) x) := by
      have hz := arrow_map_apply_heq (forget AddCommGrpCat.{u}) (hK t) z
      change HEq (e.hom (K.ι.app t z))
        ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) ((E t).hom z)) at hz
      have hEz : (E t).hom z = x := Iso.inv_hom_id_apply (E t) x
      rw [hEz] at hz
      exact hz
    refine ⟨(colimit.ι D t).hom z, ?_⟩
    change (colimit.ι D t ≫ colimit.desc D K).hom z = y
    rw [colimit.ι_desc]
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    exact eq_of_heq (hz.trans hx)

end CategoryTheory
