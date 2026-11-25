/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Tactic.FinCases

/-! Intermediate finite-lifting statement for filtered category colimits. -/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Finitely many equalities of representatives hold after a single refinement. -/
private theorem finite_stage_eq
    {J : Type u} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type u)
    (c : Cocone G) (hc : IsColimit c) (n : ℕ) (j : J)
    (x y : Fin n → G.obj j) (h : ∀ q, c.ι.app j (x q) = c.ι.app j (y q)) :
    ∃ (k : J) (f : j ⟶ k), ∀ q, G.map f (x q) = G.map f (y q) := by
  classical
  induction n generalizing j with
  | zero => exact ⟨j, 𝟙 j, fun q ↦ Fin.elim0 q⟩
  | succ n ih =>
    obtain ⟨k, f, hf⟩ := ih j (fun q ↦ x q.castSucc) (fun q ↦ y q.castSucc)
      (fun q ↦ h q.castSucc)
    have he : c.ι.app k (G.map f (x (Fin.last n))) =
        c.ι.app k (G.map f (y (Fin.last n))) := by
      have hh := h (Fin.last n)
      rw [← c.w f] at hh
      exact hh
    obtain ⟨l, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp he
    refine ⟨l, f ≫ g, ?_⟩
    intro q
    refine Fin.lastCases ?_ (fun q ↦ ?_) q
    · simpa only [G.map_comp, ConcreteCategory.comp_apply] using hg
    · simpa only [G.map_comp, ConcreteCategory.comp_apply] using
        congrArg (fun a ↦ G.map g a) (hf q)

/-- Equality of arrows respects composition, including the endpoint identifications. -/
private theorem arrow_comp_congr {C : Type u} [Category.{u} C]
    {W X Y W' X' Y' : C} (a : W ⟶ X) (p : X ⟶ Y)
    (a' : W' ⟶ X') (p' : X' ⟶ Y')
    (ha : Arrow.mk a = Arrow.mk a') (hp : Arrow.mk p = Arrow.mk p') :
    Arrow.mk (a ≫ p) = Arrow.mk (a' ≫ p') := by
  have hW := congrArg Arrow.left ha
  have hX := congrArg Arrow.right ha
  have hY := congrArg Arrow.right hp
  change W = W' at hW
  change X = X' at hX
  change Y = Y' at hY
  subst W' X' Y'
  have ea := Arrow.mk_injective _ _ ha
  have ep := Arrow.mk_injective _ _ hp
  rw [ea, ep]

/-- Two arrows into a specified stage object lift together above that stage. -/
private theorem lift_pair
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (ho : IsColimit (Cat.objects.mapCocone V))
    (ha : IsColimit (Cat.arrows.mapCocone V)) (j : J) (P : F.obj j)
    (W : V.pt) (a b : W ⟶ (V.ι.app j).toFunctor.obj P) :
    ∃ (k : J) (v : j ⟶ k) (W' : F.obj k)
      (a' b' : W' ⟶ (F.map v).toFunctor.obj P),
      Arrow.mk ((V.ι.app k).toFunctor.map a') = Arrow.mk a ∧
      Arrow.mk ((V.ι.app k).toFunctor.map b') = Arrow.mk b := by
  classical
  obtain ⟨i, A, B, hA, hB⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ ha (Arrow.mk a) (Arrow.mk b)
  let k := IsFiltered.max i j
  let r : i ⟶ k := IsFiltered.leftToMax i j
  let v : j ⟶ k := IsFiltered.rightToMax i j
  let A₀ : Arrow (F.obj k) := (F ⋙ Cat.arrows).map r A
  let B₀ : Arrow (F.obj k) := (F ⋙ Cat.arrows).map r B
  have hA₀ : (V.ι.app k).toFunctor.mapArrow.obj A₀ = Arrow.mk a :=
    (ConcreteCategory.congr_hom ((Cat.arrows.mapCocone V).w r) A).trans hA
  have hB₀ : (V.ι.app k).toFunctor.mapArrow.obj B₀ = Arrow.mk b :=
    (ConcreteCategory.congr_hom ((Cat.arrows.mapCocone V).w r) B).trans hB
  have hP : (V.ι.app k).toFunctor.obj ((F.map v).toFunctor.obj P) =
      (V.ι.app j).toFunctor.obj P :=
    ConcreteCategory.congr_hom ((Cat.objects.mapCocone V).w v) P
  let x : Fin 3 → F.obj k := ![A₀.left, A₀.right, B₀.right]
  let y : Fin 3 → F.obj k :=
    ![B₀.left, (F.map v).toFunctor.obj P, (F.map v).toFunctor.obj P]
  have hxy : ∀ q, (Cat.objects.mapCocone V).ι.app k (x q) =
      (Cat.objects.mapCocone V).ι.app k (y q) := by
    intro q
    fin_cases q
    · exact (congrArg Arrow.left hA₀).trans (congrArg Arrow.left hB₀).symm
    · exact (congrArg Arrow.right hA₀).trans hP.symm
    · exact (congrArg Arrow.right hB₀).trans hP.symm
  obtain ⟨l, t, ht⟩ := finite_stage_eq (F ⋙ Cat.objects)
    (Cat.objects.mapCocone V) ho 3 k x y hxy
  let A₁ := (F.map t).toFunctor.mapArrow.obj A₀
  let B₁ := (F.map t).toFunctor.mapArrow.obj B₀
  have hs : A₁.left = B₁.left := ht 0
  have htA : A₁.right = (F.map (v ≫ t)).toFunctor.obj P := by
    have hh := ht 1
    change (F.map t).toFunctor.obj A₀.right =
      (F.map t).toFunctor.obj ((F.map v).toFunctor.obj P) at hh
    simpa [A₁, B₁, F.map_comp] using hh
  have htB : B₁.right = (F.map (v ≫ t)).toFunctor.obj P := by
    have hh := ht 2
    change (F.map t).toFunctor.obj B₀.right =
      (F.map t).toFunctor.obj ((F.map v).toFunctor.obj P) at hh
    simpa [A₁, B₁, F.map_comp] using hh
  refine ⟨l, v ≫ t, A₁.left, A₁.hom ≫ eqToHom htA,
    eqToHom hs ≫ B₁.hom ≫ eqToHom htB, ?_, ?_⟩
  · simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
    exact (ConcreteCategory.congr_hom ((Cat.arrows.mapCocone V).w t) A₀).trans hA₀
  · simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp,
      Arrow.arrow_mk_comp_eqToHom]
    exact (ConcreteCategory.congr_hom ((Cat.arrows.mapCocone V).w t) B₀).trans hB₀

/-- Joint monicity of the image of the two stable stage pullback projections.
Source: Stacks Project, Sites, Tag 09YL, pullback paragraph and Hom calculation.
(blueprint: lem-weil-pbc-filtered-colimit-pullback-hom-ext)

Proof: Lift the two proposed arrows to stage arrows using joint surjectivity
of the arrow colimit. Move their stages and j to a common upper stage. Eventual
equality in the object colimit aligns their sources with each other and their
targets with the transitioned pullback object. After these identifications,
their composites with the transitioned projections have equal colimit images.
Use eventual equality in the arrow colimit twice to enforce these two equalities
at a later stage. The pullback remains preserved by the composite transition
out of j, so its two projections are jointly monic there. The two stage arrows
are equal, and applying the cocone functor proves equality of the original
arrows. This uses no existence of a factorization for an arbitrary cone. -/
theorem filteredColimit_pullback_hom_ext
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) {X Y Z : F.obj j} (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f g]
    (hpres : ∀ (k : J) (a : j ⟶ k),
      PreservesLimit (cospan f g) (F.map a).toFunctor) :
    ∀ (W : V.pt) (a b : W ⟶ (V.ι.app j).toFunctor.obj (pullback f g)),
      a ≫ (V.ι.app j).toFunctor.map (pullback.fst f g) =
        b ≫ (V.ι.app j).toFunctor.map (pullback.fst f g) →
      a ≫ (V.ι.app j).toFunctor.map (pullback.snd f g) =
        b ≫ (V.ι.app j).toFunctor.map (pullback.snd f g) → a = b := by
  intro W a b hf hg
  obtain ⟨k, v, W', a', b', ha, hb⟩ :=
    lift_pair F V hobjects harrows j (pullback f g) W a b
  let T := (F.map v).toFunctor
  let U := (V.ι.app k).toFunctor
  have hw : T ⋙ U = (V.ι.app j).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w v)
  have hcomp {Q : F.obj j} (p : pullback f g ⟶ Q)
      (hab : a ≫ (V.ι.app j).toFunctor.map p =
        b ≫ (V.ι.app j).toFunctor.map p) :
      U.mapArrow.obj (Arrow.mk (a' ≫ T.map p)) =
        U.mapArrow.obj (Arrow.mk (b' ≫ T.map p)) := by
    have hp : Arrow.mk (U.map (T.map p)) =
        Arrow.mk ((V.ι.app j).toFunctor.map p) :=
      congrArg (fun H : F.obj j ⥤ V.pt ↦ Arrow.mk (H.map p)) hw
    change Arrow.mk (U.map (a' ≫ T.map p)) = Arrow.mk (U.map (b' ≫ T.map p))
    simp only [Functor.map_comp]
    exact (arrow_comp_congr _ _ _ _ ha hp).trans
      ((congrArg Arrow.mk hab).trans (arrow_comp_congr _ _ _ _ hb hp).symm)
  let x : Fin 2 → Arrow (F.obj k) :=
    ![Arrow.mk (a' ≫ T.map (pullback.fst f g)),
      Arrow.mk (a' ≫ T.map (pullback.snd f g))]
  let y : Fin 2 → Arrow (F.obj k) :=
    ![Arrow.mk (b' ≫ T.map (pullback.fst f g)),
      Arrow.mk (b' ≫ T.map (pullback.snd f g))]
  have hxy : ∀ q, (Cat.arrows.mapCocone V).ι.app k (x q) =
      (Cat.arrows.mapCocone V).ι.app k (y q) := by
    intro q
    fin_cases q
    · exact hcomp (pullback.fst f g) hf
    · exact hcomp (pullback.snd f g) hg
  obtain ⟨l, t, ht⟩ := finite_stage_eq (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows 2 k x y hxy
  let S := (F.map t).toFunctor
  have heq (Q : F.obj j) (p : pullback f g ⟶ Q)
      (h : Arrow.mk (S.map (a' ≫ T.map p)) =
        Arrow.mk (S.map (b' ≫ T.map p))) :
      S.map a' ≫ S.map (T.map p) = S.map b' ≫ S.map (T.map p) := by
    have hh := Arrow.mk_injective _ _ h
    simpa only [Functor.map_comp] using hh
  have hf' := heq _ (pullback.fst f g) (ht 0)
  have hg' := heq _ (pullback.snd f g) (ht 1)
  have : PreservesLimit (cospan f g) (T ⋙ S) := by
    change PreservesLimit (cospan f g)
      ((F.map v).toFunctor ⋙ (F.map t).toFunctor)
    rw [← Cat.Hom.comp_toFunctor, ← F.map_comp]
    exact hpres l (v ≫ t)
  have hlim := (PullbackCone.isLimitMapConeEquiv (pullback.cone f g) (T ⋙ S)).1
    (isLimitOfPreserves (T ⋙ S) (pullback.isLimit f g))
  have hab : S.map a' = S.map b' := PullbackCone.IsLimit.hom_ext hlim hf' hg'
  have himage : Arrow.mk (U.map a') = Arrow.mk (U.map b') := by
    have hh := congrArg ((V.ι.app l).toFunctor.mapArrow.obj)
      (congrArg Arrow.mk hab)
    have hwa :
        (V.ι.app l).toFunctor.mapArrow.obj (S.mapArrow.obj (Arrow.mk a')) =
          U.mapArrow.obj (Arrow.mk a') :=
      ConcreteCategory.congr_hom ((Cat.arrows.mapCocone V).w t) (Arrow.mk a')
    have hwb :
        (V.ι.app l).toFunctor.mapArrow.obj (S.mapArrow.obj (Arrow.mk b')) =
          U.mapArrow.obj (Arrow.mk b') :=
      ConcreteCategory.congr_hom ((Cat.arrows.mapCocone V).w t) (Arrow.mk b')
    exact hwa.symm.trans (hh.trans hwb)
  exact Arrow.mk_injective _ _ (ha.symm.trans (himage.trans hb))

end CategoryTheory
