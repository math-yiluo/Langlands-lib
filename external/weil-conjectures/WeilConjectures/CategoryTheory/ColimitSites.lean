/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredColimitCategories
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.ColimitSiteCoveringConstruction
import WeilConjectures.CategoryTheory.ColimitSiteSetInverseImage
import WeilConjectures.CategoryTheory.ColimitSiteAbelianInverseImage
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Filtered colimits of sites

Source: Stacks Project, Sites, Situation 0A34 and Lemmas 09YL, 0A35
(blueprint: lem-weil-pbc-colimit-of-sites).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Situation 0A34 and Lemmas 09YL, 0A35
(blueprint: lem-weil-pbc-colimit-of-sites).

We use the filtered opposite of Stacks' cofiltered index category. A cocone in `Cat`
whose object and arrow cocones are set colimits encodes the category in 09YL.
Covering presieves are precisely images of covering presieves at the stages.
Base change and composition are required only for finite indexed families, as in
Stacks 09YL; a finite presieve may also have an infinite repeated-index presentation.
The section formula is a colimit cocone, with all its maps characterized by the
adjunction units. Equality in `Arrow` includes endpoint equalities, so the formula
uses the strict functor and cocone identities without choosing transport proofs.

Proof:
1. Apply lem-weil-pbc-filtered-colimit-categories. Finite objects, arrows and
   relations lift to one stage; two lifts become equal at a further stage.
2. A finite covering and any finite further data lift together, even over a fixed
   stage, by filteredness and the equality criterion for filtered colimits of sets.
3. The image of a pullback along a covering arrow is a pullback: its Hom universal
   property is the filtered colimit of the stagewise Hom pullbacks, using
   lem-weil-pbc-filtered-colimits-commute-finite-limits.
4. Composite coverings lift to a common stage since the outer covering is finite;
   their composites cover there. Pullback coverings lift and cover by step 3.
5. Lift an isomorphism and its inverse equations to a stage to obtain the singleton
   covering axiom. Thus the union of image coverings is a site (09YL).
6. Steps 3 and 4 show that each canonical functor preserves coverings and their
   pullbacks. Precomposition therefore preserves sheaves, using
   lem-weil-pbc-site-continuous-pushforward-sheaf. Cocone naturality gives composition.
7. The constructed sheaf inverse image is left adjoint to precomposition
   (def-weil-pbc-sites-and-cohomology), hence preserves finite colimits by
   situation-conventions.
8. For a refinement, transpose the unit of inverse image at the refined stage
   through the original stage adjunction. The result is the transition morphism.
   Uniqueness of adjuncts gives identities, the cocycle equation and naturality.
9. For a limit-site object form the filtered colimit of these sections over all
   its stage presentations. The category of presentations is cofiltered, and the
   slice at any presentation is initial, by
   lem-weil-pbc-initial-functor-cofiltered-criterion. Finite lifting and eventual
   equality make restriction maps independent of the lifts; they form a presheaf.
10. Lift a finite covering to a stage. Its sheaf equalizer diagram remains an
    equalizer on taking filtered colimits, by
    lem-weil-pbc-filtered-colimits-commute-finite-limits, so this presheaf is a sheaf.
11. Maps from this sheaf to H are compatible families of maps from stage inverse
    images to stage restrictions of H. Adjunction identifies these with one map
    from the original sheaf to the canonical restriction of H. Thus the constructed
    sheaf is inverse image, by situation-conventions. Evaluating
    at the image of U gives exactly the colimit cocone asserted below.
12. The same formula at every object proves preservation of finite limits, using
    situation-conventions and commutation of filtered
    colimits with finite limits. Together with step 7 this is a morphism of sites.
    Steps 8--11 apply to abelian groups too: their filtered colimits and finite
    limits are computed on underlying sets, and every map is additive. -/
/- A filtered category has a nonempty object type. -/
theorem filtered_index_nonempty (J : Type u) [SmallCategory J] [IsFiltered J] :
    Nonempty J := by
  exact IsFiltered.nonempty

/-- Source: Stacks Project, Sites, Situation 0A34 and Lemmas 09YL, 0A35
(blueprint: lem-weil-pbc-colimit-of-sites-reduced).

We use the filtered opposite of Stacks' cofiltered index category. A cocone in `Cat`
whose object and arrow cocones are set colimits encodes the category in 09YL.
Covering presieves are precisely images of covering presieves at the stages.
Base change and composition are required only for finite indexed families, as in
Stacks 09YL; a finite presieve may also have an infinite repeated-index presentation.
The section formula is a colimit cocone, with all its maps characterized by the
adjunction units. Equality in `Arrow` includes endpoint equalities, so the formula
uses the strict functor and cocone identities without choosing transport proofs.

Proof:
1. Apply lem-weil-pbc-filtered-colimit-categories. Finite objects, arrows and
   relations lift to one stage; two lifts become equal at a further stage.
2. A finite covering and any finite further data lift together, even over a fixed
   stage, by filteredness and the equality criterion for filtered colimits of sets.
3. The image of a pullback along a covering arrow is a pullback: its Hom universal
   property is the filtered colimit of the stagewise Hom pullbacks, using
   lem-weil-pbc-filtered-colimits-commute-finite-limits.
4. Composite coverings lift to a common stage since the outer covering is finite;
   their composites cover there. Pullback coverings lift and cover by step 3.
5. Lift an isomorphism and its inverse equations to a stage to obtain the singleton
   covering axiom. Thus the union of image coverings is a site (09YL).
6. Steps 3 and 4 show that each canonical functor preserves coverings and their
   pullbacks. Precomposition therefore preserves sheaves, using
   lem-weil-pbc-site-continuous-pushforward-sheaf. Cocone naturality gives composition.
7. The constructed sheaf inverse image is left adjoint to precomposition
   (def-weil-pbc-sites-and-cohomology), hence preserves finite colimits by
   situation-conventions.
8. For a refinement, transpose the unit of inverse image at the refined stage
   through the original stage adjunction. The result is the transition morphism.
   Uniqueness of adjuncts gives identities, the cocycle equation and naturality.
9. For a limit-site object form the filtered colimit of these sections over all
   its stage presentations. The category of presentations is cofiltered, and the
   slice at any presentation is initial, by
   lem-weil-pbc-initial-functor-cofiltered-criterion. Finite lifting and eventual
   equality make restriction maps independent of the lifts; they form a presheaf.
10. Lift a finite covering to a stage. Its sheaf equalizer diagram remains an
    equalizer on taking filtered colimits, by
    lem-weil-pbc-filtered-colimits-commute-finite-limits, so this presheaf is a sheaf.
11. Maps from this sheaf to H are compatible families of maps from stage inverse
    images to stage restrictions of H. Adjunction identifies these with one map
    from the original sheaf to the canonical restriction of H. Thus the constructed
    sheaf is inverse image, by situation-conventions. Evaluating
    at the image of U gives exactly the colimit cocone asserted below.
12. The same formula at every object proves preservation of finite limits, using
    situation-conventions and commutation of filtered
    colimits with finite limits. Together with step 7 this is a morphism of sites.
    Steps 8--11 apply to abelian groups too: their filtered colimits and finite
    limits are computed on underlying sets, and every map is additive. -/
theorem exists_colimit_site_reduced
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
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)] :
    ∃ (V : Cocone F),
      Nonempty (IsColimit (Cat.objects.mapCocone V)) ∧
      Nonempty (IsColimit (Cat.arrows.mapCocone V)) ∧
      (∀ (n m : ℕ) (X : Fin n → V.pt) (A : Fin m → Arrow V.pt),
        ∃ (j : J) (Xj : Fin n → F.obj j) (Aj : Fin m → Arrow (F.obj j)),
          (∀ q : Fin n, (V.ι.app j).toFunctor.obj (Xj q) = X q) ∧
          (∀ p : Fin m, (V.ι.app j).toFunctor.mapArrow.obj (Aj p) = A p) ∧
          (∀ (p : Fin m) (q : Fin n), (A p).left = X q → (Aj p).left = Xj q) ∧
          (∀ (p : Fin m) (q : Fin n), (A p).right = X q → (Aj p).right = Xj q) ∧
          (∀ (p q r : Fin m) (h : (A p).right = (A q).left),
            Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
            ∃ hj : (Aj p).right = (Aj q).left,
              Arrow.mk ((Aj p).hom ≫ eqToHom hj ≫ (Aj q).hom) = Aj r) ∧
          (∀ (p : Fin m) (q : Fin n), A p = Arrow.mk (𝟙 (X q)) →
            Aj p = Arrow.mk (𝟙 (Xj q)))) ∧
      (∀ (D : Type u) [SmallCategory D] [FinCategory D] (d : D ⥤ V.pt),
        ∃ (j : J) (dj : D ⥤ F.obj j), dj ⋙ (V.ι.app j).toFunctor = d) ∧
      ∃ (Q : Precoverage V.pt),
        (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R) ∧
        ∃ (_ : Q.HasIsos) (_ : Q.IsStableUnderFiniteComposition)
          (_ : Q.IsStableUnderFiniteBaseChange) (_ : Q.HasPullbacks),
          (∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
            R.map (V.ι.app j).toFunctor ∈ Q ((V.ι.app j).toFunctor.obj X)) ∧
          (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor) ∧
          ∃ (_ : ∀ j : J, (V.ι.app j).toFunctor.IsContinuous
              (P j).toGrothendieck Q.toGrothendieck),
            (∀ j : J, Nonempty (PreservesFiniteLimits
              (sheafPullback (V.ι.app j).toFunctor (Type u)
                (P j).toGrothendieck Q.toGrothendieck))) ∧
            (∀ j : J, Nonempty (PreservesFiniteColimits
              (sheafPullback (V.ι.app j).toFunctor (Type u)
                (P j).toGrothendieck Q.toGrothendieck))) ∧
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck (Type u)),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ (Type u))
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor (Type u)
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) ∧
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u}),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ AddCommGrpCat.{u})
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) := by
  classical
  obtain ⟨s, L, hObj, hCompat, ⟨a, e, ⟨ha⟩, he⟩, hLift, hEqual, hFinite, hHom,
    hIso⟩ := exists_filteredColimit_category J F
  let O := colimit (F ⋙ Cat.objects)
  let : Category.{u} O := s
  let V : Cocone F :=
    { pt := Cat.of O
      ι :=
        { app := fun j ↦ (L j).toCatHom
          naturality := by
            intro j k f
            exact congrArg Functor.toCatHom (hCompat j k f) } }
  have hobjects : IsColimit (Cat.objects.mapCocone V) := by
    apply (colimit.isColimit (F ⋙ Cat.objects)).ofIsoColimit
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    ext X
    exact (hObj j X).symm
  have harrows : IsColimit (Cat.arrows.mapCocone V) := by
    apply ha.ofIsoColimit
    refine Cocone.ext e.toIso ?_
    intro j
    ext f
    exact he j f
  let Q : Precoverage V.pt :=
    { coverings := fun Y ↦ { R | ∃ (j : J) (X : F.obj j) (S : Presieve X)
        (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R } }
  have hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R := by
    intro Y R
    rfl
  obtain ⟨hisos, hcomp, hbase, hpb, hVpullback, ⟨hcontinuous⟩⟩ :=
    colimit_site_covering_construction J F P hfinite hcover hpullback V hobjects harrows Q hQ
  let : Q.HasIsos := hisos
  let : Q.IsStableUnderFiniteComposition := hcomp
  let : Q.IsStableUnderFiniteBaseChange := hbase
  let : Q.HasPullbacks := hpb
  have hVcover : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      R.map (V.ι.app j).toFunctor ∈ Q ((V.ι.app j).toFunctor.obj X) := by
    intro j X R hR
    exact (hQ _ _).mpr ⟨j, X, R, rfl, hR, rfl⟩
  let : ∀ j : J, (V.ι.app j).toFunctor.IsContinuous
    (P j).toGrothendieck Q.toGrothendieck := hcontinuous
  obtain ⟨hlimits, hsets⟩ := colimit_site_set_inverse_image J F P hfinite hcover
    hpullback V hobjects harrows Q hQ hVpullback
  have hgroups := colimit_site_abelian_inverse_image J F P hfinite hcover
    hpullback V hobjects harrows Q hQ hVpullback
  have hcolimits : ∀ j : J, Nonempty (PreservesFiniteColimits
      (sheafPullback (V.ι.app j).toFunctor (Type u)
        (P j).toGrothendieck Q.toGrothendieck)) := by
    intro j
    have := (sheafAdjunctionContinuous (V.ι.app j).toFunctor (Type u)
      (P j).toGrothendieck Q.toGrothendieck).leftAdjoint_preservesColimits
    exact ⟨inferInstance⟩
  exact ⟨V, ⟨hobjects⟩, ⟨harrows⟩, hLift, hFinite, Q, hQ, hisos, hcomp, hbase, hpb,
    hVcover, hVpullback, hcontinuous, hlimits, hcolimits, hsets, hgroups⟩

/-- (blueprint: lem-weil-pbc-colimit-of-sites) -/
theorem exists_colimit_site
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
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
 :
    ∃ (V : Cocone F),
      Nonempty (IsColimit (Cat.objects.mapCocone V)) ∧
      Nonempty (IsColimit (Cat.arrows.mapCocone V)) ∧
      (∀ (n m : ℕ) (X : Fin n → V.pt) (A : Fin m → Arrow V.pt),
        ∃ (j : J) (Xj : Fin n → F.obj j) (Aj : Fin m → Arrow (F.obj j)),
          (∀ q : Fin n, (V.ι.app j).toFunctor.obj (Xj q) = X q) ∧
          (∀ p : Fin m, (V.ι.app j).toFunctor.mapArrow.obj (Aj p) = A p) ∧
          (∀ (p : Fin m) (q : Fin n), (A p).left = X q → (Aj p).left = Xj q) ∧
          (∀ (p : Fin m) (q : Fin n), (A p).right = X q → (Aj p).right = Xj q) ∧
          (∀ (p q r : Fin m) (h : (A p).right = (A q).left),
            Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
            ∃ hj : (Aj p).right = (Aj q).left,
              Arrow.mk ((Aj p).hom ≫ eqToHom hj ≫ (Aj q).hom) = Aj r) ∧
          (∀ (p : Fin m) (q : Fin n), A p = Arrow.mk (𝟙 (X q)) →
            Aj p = Arrow.mk (𝟙 (Xj q)))) ∧
      (∀ (D : Type u) [SmallCategory D] [FinCategory D] (d : D ⥤ V.pt),
        ∃ (j : J) (dj : D ⥤ F.obj j), dj ⋙ (V.ι.app j).toFunctor = d) ∧
      ∃ (Q : Precoverage V.pt),
        (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R) ∧
        ∃ (_ : Q.HasIsos) (_ : Q.IsStableUnderFiniteComposition)
          (_ : Q.IsStableUnderFiniteBaseChange) (_ : Q.HasPullbacks),
          (∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
            R.map (V.ι.app j).toFunctor ∈ Q ((V.ι.app j).toFunctor.obj X)) ∧
          (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor) ∧
          ∃ (_ : ∀ j : J, (V.ι.app j).toFunctor.IsContinuous
              (P j).toGrothendieck Q.toGrothendieck),
            (∀ j : J, Nonempty (PreservesFiniteLimits
              (sheafPullback (V.ι.app j).toFunctor (Type u)
                (P j).toGrothendieck Q.toGrothendieck))) ∧
            (∀ j : J, Nonempty (PreservesFiniteColimits
              (sheafPullback (V.ι.app j).toFunctor (Type u)
                (P j).toGrothendieck Q.toGrothendieck))) ∧
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck (Type u)),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ (Type u))
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor (Type u)
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) ∧
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u}),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ AddCommGrpCat.{u})
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) := by
  exact exists_colimit_site_reduced (J := J) (F := F) P hfinite hcover hpullback

end CategoryTheory
