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

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem cocone_arrow_eq
    {J : Type u} [SmallCategory J] (F : J ⥤ Cat.{u, u}) (V : Cocone F)
    {j k : J} (a : j ⟶ k) {X Y : F.obj j} (f : X ⟶ Y) :
    Arrow.mk ((V.ι.app k).toFunctor.map ((F.map a).toFunctor.map f)) =
      Arrow.mk ((V.ι.app j).toFunctor.map f) := by
  exact congrArg (fun U ↦ Arrow.mk (U.toFunctor.map f)) (V.w a)

private theorem isIso_of_arrow_eq
    {C : Type u} [SmallCategory C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : Arrow.mk f = Arrow.mk g)
    [IsIso g] : IsIso f := by
  have : IsIso (Arrow.mk g).hom := ‹IsIso g›
  rw [← h] at this
  exact this

private theorem inverse_equations_of_arrow_eq
    {C : Type u} [SmallCategory C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : Y ⟶ X} {f' : X' ⟶ Y'} {g' : Y' ⟶ X'}
    (hf : Arrow.mk f' = Arrow.mk f) (hg : Arrow.mk g' = Arrow.mk g)
    (hfg : f ≫ g = 𝟙 X) (hgf : g ≫ f = 𝟙 Y) :
    f' ≫ g' = 𝟙 X' ∧ g' ≫ f' = 𝟙 Y' := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff f' f).mp hf
  subst X'
  subst Y'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f'
  have hg' : g' = g := Arrow.mk_injective _ _ hg
  subst g'
  exact ⟨hfg, hgf⟩

/-- Stage representation of an isomorphism in a filtered colimit category.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-filtered-colimit-iso-presieve-representation)

Proof: Represent the arrow and its inverse in the arrow colimit. Filteredness gives
one stage containing both representatives and all endpoint equalities. The two
inverse equations are equalities in the arrow colimit, hence become equalities at
a further common stage by the filtered colimit equality criterion. The resulting
stage arrow is an isomorphism; transporting its singleton along the target
identification gives the singleton of the original arrow.
-/
theorem filtered_colimit_iso_presieve_representation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    {S T : V.pt} (f : S ⟶ T) [IsIso f] :
    ∃ (j : J) (X : F.obj j) (R : Presieve X)
      (h : (V.ι.app j).toFunctor.obj X = T),
      R ∈ P j X ∧ h ▸ R.map (V.ι.app j).toFunctor = Presieve.singleton f := by
  obtain ⟨j, a, ha⟩ := Types.jointly_surjective (F ⋙ Cat.arrows) harrows (Arrow.mk f)
  change Arrow.mk ((V.ι.app j).toFunctor.map a.hom) = Arrow.mk f at ha
  have : IsIso ((V.ι.app j).toFunctor.map a.hom) := isIso_of_arrow_eq ha
  obtain ⟨i, c, hc⟩ := Types.jointly_surjective (F ⋙ Cat.arrows) harrows
    (Arrow.mk (inv ((V.ι.app j).toFunctor.map a.hom)))
  have he : (Cat.objects.mapCocone V).ι.app j a.left =
      (Cat.objects.mapCocone V).ι.app i c.right :=
    (congrArg Arrow.right hc).symm
  obtain ⟨k, t, d, h⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ Cat.objects) hobjects).mp he
  change (F.map t).toFunctor.obj a.left = (F.map d).toFunctor.obj c.right at h
  let Z := (F.map d).toFunctor.obj c.left
  let b := (F.map d).toFunctor.map c.hom ≫ eqToHom h.symm
  have hb : Arrow.mk ((V.ι.app k).toFunctor.map b) =
      Arrow.mk (inv ((V.ι.app j).toFunctor.map a.hom)) := by
    dsimp [b]
    rw [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
    exact (cocone_arrow_eq F V d c.hom).trans hc
  have he : (Cat.objects.mapCocone V).ι.app k Z =
      (Cat.objects.mapCocone V).ι.app k ((F.map t).toFunctor.obj a.right) := by
    exact (congrArg Arrow.left hb).trans
      (congrArg Arrow.right (cocone_arrow_eq F V t a.hom)).symm
  obtain ⟨l, s, hs⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hobjects Z
      ((F.map t).toFunctor.obj a.right)).mp he
  change (F.map s).toFunctor.obj Z =
    (F.map s).toFunctor.obj ((F.map t).toFunctor.obj a.right) at hs
  let U := (F.map s).toFunctor
  let X := U.obj ((F.map t).toFunctor.obj a.left)
  let Y := U.obj ((F.map t).toFunctor.obj a.right)
  let A := U.map ((F.map t).toFunctor.map a.hom)
  let B := eqToHom hs.symm ≫ U.map b
  have hA : Arrow.mk ((V.ι.app l).toFunctor.map A) =
      Arrow.mk ((V.ι.app j).toFunctor.map a.hom) :=
    (cocone_arrow_eq F V s ((F.map t).toFunctor.map a.hom)).trans
      (cocone_arrow_eq F V t a.hom)
  have hB : Arrow.mk ((V.ι.app l).toFunctor.map B) =
      Arrow.mk (inv ((V.ι.app j).toFunctor.map a.hom)) := by
    dsimp [B]
    rw [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp]
    exact (cocone_arrow_eq F V s b).trans hb
  have hAB := inverse_equations_of_arrow_eq hA hB
    (IsIso.hom_inv_id ((V.ι.app j).toFunctor.map a.hom))
    (IsIso.inv_hom_id ((V.ι.app j).toFunctor.map a.hom))
  have heq₁ : (Cat.arrows.mapCocone V).ι.app l (Arrow.mk (A ≫ B)) =
      (Cat.arrows.mapCocone V).ι.app l (Arrow.mk (𝟙 X)) := by
    change Arrow.mk ((V.ι.app l).toFunctor.map (A ≫ B)) =
      Arrow.mk ((V.ι.app l).toFunctor.map (𝟙 X))
    rw [Functor.map_comp, Functor.map_id, hAB.1]
  obtain ⟨m, r, hr⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' harrows
      (Arrow.mk (A ≫ B)) (Arrow.mk (𝟙 X))).mp heq₁
  change Arrow.mk ((F.map r).toFunctor.map (A ≫ B)) =
    Arrow.mk ((F.map r).toFunctor.map (𝟙 X)) at hr
  have hr₁ : (F.map r).toFunctor.map A ≫ (F.map r).toFunctor.map B = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using Arrow.mk_injective _ _ hr
  have heq₀₂ : Arrow.mk ((V.ι.app l).toFunctor.map (B ≫ A)) =
      Arrow.mk ((V.ι.app l).toFunctor.map (𝟙 Y)) := by
    rw [Functor.map_comp, Functor.map_id, hAB.2]
  have heq₂ : (Cat.arrows.mapCocone V).ι.app m
      (Arrow.mk ((F.map r).toFunctor.map (B ≫ A))) =
      (Cat.arrows.mapCocone V).ι.app m
        (Arrow.mk ((F.map r).toFunctor.map (𝟙 Y))) := by
    exact (cocone_arrow_eq F V r (B ≫ A)).trans
      (heq₀₂.trans (cocone_arrow_eq F V r (𝟙 Y)).symm)
  obtain ⟨n, q, hq⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' harrows
      (Arrow.mk ((F.map r).toFunctor.map (B ≫ A)))
      (Arrow.mk ((F.map r).toFunctor.map (𝟙 Y)))).mp heq₂
  change Arrow.mk ((F.map q).toFunctor.map
      ((F.map r).toFunctor.map (B ≫ A))) =
    Arrow.mk ((F.map q).toFunctor.map ((F.map r).toFunctor.map (𝟙 Y))) at hq
  let A' := (F.map q).toFunctor.map ((F.map r).toFunctor.map A)
  let B' := (F.map q).toFunctor.map ((F.map r).toFunctor.map B)
  have hq₂ : B' ≫ A' = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using Arrow.mk_injective _ _ hq
  have hq₁ : A' ≫ B' = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      congrArg (fun c ↦ (F.map q).toFunctor.map c) hr₁
  have : IsIso A' := ⟨⟨B', hq₁, hq₂⟩⟩
  have hA' : Arrow.mk ((V.ι.app n).toFunctor.map A') = Arrow.mk f :=
    (cocone_arrow_eq F V q ((F.map r).toFunctor.map A)).trans
      ((cocone_arrow_eq F V r A).trans (hA.trans ha))
  obtain ⟨hS, hT, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hA'
  subst S
  subst T
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  refine ⟨n, _, Presieve.singleton A', rfl,
    Precoverage.HasIsos.mem_coverings_of_isIso A', ?_⟩
  simpa only [Presieve.map_singleton] using congrArg Presieve.singleton hf

end CategoryTheory
