/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.FilteredColimitPreservesPullback

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
private theorem cocone_arrow_eq
    {J : Type u} [SmallCategory J] (F : J ⥤ Cat.{u, u}) (V : Cocone F)
    {j k : J} (a : j ⟶ k) {X Y : F.obj j} (f : Y ⟶ X) :
    Arrow.mk ((V.ι.app k).toFunctor.map ((F.map a).toFunctor.map f)) =
      Arrow.mk ((V.ι.app j).toFunctor.map f) := by
  exact congrArg (fun U ↦ Arrow.mk (U.toFunctor.map f)) (V.w a)

private theorem lift_arrow_above_stage
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) (X : F.obj j) {Y : V.pt} (g : Y ⟶ (V.ι.app j).toFunctor.obj X) :
    ∃ (k : J) (a : j ⟶ k) (Z : F.obj k)
      (g' : Z ⟶ (F.map a).toFunctor.obj X),
      Arrow.mk ((V.ι.app k).toFunctor.map g') = Arrow.mk g := by
  obtain ⟨i, b, hb⟩ := Types.jointly_surjective (F ⋙ Cat.arrows) harrows (Arrow.mk g)
  have he : (Cat.objects.mapCocone V).ι.app j X =
      (Cat.objects.mapCocone V).ι.app i b.right :=
    (congrArg Arrow.right hb).symm
  obtain ⟨k, a, c, h⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ Cat.objects) hobjects).mp he
  change (F.map a).toFunctor.obj X = (F.map c).toFunctor.obj b.right at h
  refine ⟨k, a, (F.map c).toFunctor.obj b.left,
    (F.map c).toFunctor.map b.hom ≫ eqToHom h.symm, ?_⟩
  rw [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
  exact (cocone_arrow_eq F V c b.hom).trans hb

private theorem hasPullback_of_arrow_eq
    {C : Type u} [SmallCategory C] {X Y Z X' Y' Z' : C}
    {f : Y ⟶ X} {g : Z ⟶ X} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'}
    (hf : Arrow.mk f' = Arrow.mk f) (hg : Arrow.mk g' = Arrow.mk g)
    [HasPullback f' g'] : HasPullback f g := by
  obtain ⟨hY, hX, hf⟩ := (Arrow.mk_eq_mk_iff f' f).mp hf
  subst Y'
  subst X'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f'
  obtain ⟨hZ, _, hg⟩ := (Arrow.mk_eq_mk_iff g' g).mp hg
  subst Z'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst g'
  infer_instance

/-- Then every member of every Q-cover has a pullback along every arrow into its target.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-colimit-site-covering-axioms-haspullbacks)

Proof: Fix a Q-cover R, a member f of R, and an arbitrary arrow g into
its target. Represent R by a stage covering S using hQ and f by a member of S
using the definition of Presieve.map. Represent g in the arrow colimit, move
its representative and S to a common stage, and enforce their common target
using eventual equality in the object colimit. The image of S remains covering
by hcover, and the representative of f is a member of that image. Thus stage
HasPullbacks supplies a pullback of the represented f and g. Every subsequent
transition preserves it by hpullback. Its image in the cocone category is a
pullback: represent a test cone's vertex and legs at a common later stage and
make its endpoint and cone equations hold there by eventual equality in the
object and arrow colimits. Preservation of the stage pullback gives a mediating
arrow whose cocone image factors the cone. For uniqueness represent any two
mediating arrows and make their factorization equations hold at a common later
stage; the preserved pullback there equates them. Their cocone images therefore
agree. This establishes a pullback of f and g after the endpoint transports.
Applying this argument to every R, g, and member f gives Q.HasPullbacks. There
is nothing to construct for an empty covering. -/
theorem colimit_site_covering_axioms_HasPullbacks
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
        Q.HasPullbacks := by
  have _ := hfinite
  constructor
  intro Y X R g hR
  constructor
  intro Z f hf
  obtain ⟨j, X₀, S, hX, hS, hSR⟩ := (hQ X R).mp hR
  subst X
  subst R
  cases hf with
  | of hf =>
    rename_i Y₀ f₀
    obtain ⟨k, a, Z₀, g₀, hg⟩ := lift_arrow_above_stage F V hobjects harrows j X₀ g
    let U := (F.map a).toFunctor
    let T := S.map U
    have hT : T ∈ P k (U.obj X₀) := hcover j k a X₀ S hS
    have := (P k).hasPullbacks_of_mem g₀ hT
    have : HasPullback (U.map f₀) g₀ := T.hasPullback g₀ (S.map_map hf)
    have : PreservesLimit (cospan (U.map f₀) g₀) (V.ι.app k).toFunctor :=
      filteredColimit_preservesPullback J F V hobjects harrows k (U.map f₀) g₀
        (fun l b ↦ hpullback k l b _ _ _ T hT (U.map f₀) g₀ (S.map_map hf))
    have := hasPullback_of_preservesPullback (V.ι.app k).toFunctor (U.map f₀) g₀
    exact hasPullback_of_arrow_eq (cocone_arrow_eq F V a f₀) hg

end CategoryTheory
