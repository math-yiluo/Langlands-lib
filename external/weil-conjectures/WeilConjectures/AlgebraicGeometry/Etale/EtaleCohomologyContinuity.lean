/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleCohomologyCocone
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap
import WeilConjectures.AlgebraicGeometry.Etale.EtaleCohomologyClassDescent

/-!
# Continuity of etale cohomology at inverse limits

Source: blueprint `sec-curve-estimates/sk-prop-h2`, lemma Etale cohomology continuity
(blueprint: corollary-cohomology-pro-etale-affine); Stacks Project, Tag 03Q6.

The canonical filtered-colimit isomorphism is stated by its elementwise criterion:
every limit class descends, and every stage class in the kernel eventually vanishes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem finiteStageKilling
    {J : Type u} [SmallCategory J] [IsCofiltered J] {S : Scheme.{u}}
    (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H G q) (j₀ : J)
    (hx : cohomologyMap (c.π.app j₀ ≫ π.app j₀) G q x = 0) :
    ∃ j, cohomologyMap (π.app j) G q x = 0 := by
  obtain ⟨H, eH, r, hr, heH, B, hB, e, he⟩ :=
    exists_cofiltered_etale_cohomology_cocone D π c hc G q j₀
  have hzero : B.ι.app (Opposite.op j₀) (r j₀ x) =
      B.ι.app (Opposite.op j₀) (0 : H.obj (Opposite.op j₀)) := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    simpa only [map_zero] using (he j₀ x).trans hx
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨j, f, hf⟩ := (hB.eq_iff' (r j₀ x) 0).mp hzero
  refine ⟨j.unop, ?_⟩
  have hj : r j.unop x = 0 := by
    rw [← hr j.unop j₀ f.unop x]
    simpa only [Quiver.Hom.op_unop, map_zero] using hf
  rw [← heH j.unop x, hj, map_zero]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Etale cohomology of a torsion sheaf descending to a stage of a cofiltered qcqs
system with affine transition morphisms is the filtered colimit of stage cohomology.
The two conjuncts express surjectivity and injectivity of the canonical comparison,
with the indexing category of later stages given by arrows `f : j ⟶ i`.
The composition isomorphism identifies iterated inverse images with direct inverse images.

Source: blueprint `sec-curve-estimates/sk-prop-h2`, Etale cohomology continuity;
Stacks Project, Tag 03Q6 (the base-change case of the continuity theorem).
(blueprint: corollary-cohomology-pro-etale-affine).

Proof:
1. The class-descent theorem `exists_cohomology_class_of_isLimit` gives the first
   conjunct by descending a finite hypercover cocycle and its cocycle equation.
2. For the second conjunct, invertibility of the composition comparison shows that
   the original class pulls back to zero along the projection to its own stage j.
   Restrict D to Over j. The forgetful functor is initial, so the whiskered cone
   is still limiting; its stages retain the qcqs and affine-transition hypotheses.
3. Apply `exists_cofiltered_etale_cohomology_cocone` to the pullback sheaf on D_j.
   In its filtered cohomology colimit, the compatible image of the class equals zero.
   Since the forgetful functor to types preserves filtered colimits, `IsColimit.eq_iff'`
   gives a later arrow where that image is zero. The stage identification gives
   vanishing of the canonical cohomology pullback there.
4. The later object of Over j supplies k and g : k to j. Apply the composition
   isomorphism on cohomology to this zero class; additive maps preserve zero. -/
theorem cohomology_continuity_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    [∀ j : J, CompactSpace (D.obj j)] [∀ j : J, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : J)
    (F : Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) (q : ℕ) :
    (∀ x : Sheaf.H (((c.π.app i)^*[AddCommGrpCat.{u + 1}]).obj F) q,
      ∃ (j : J) (f : j ⟶ i)
        (y : Sheaf.H (((D.map f)^*[AddCommGrpCat.{u + 1}]).obj F) q),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm).inv.app F) q
          (cohomologyMap (c.π.app j) _ q y) = x) ∧
    (∀ (j : J) (f : j ⟶ i)
      (y : Sheaf.H (((D.map f)^*[AddCommGrpCat.{u + 1}]).obj F) q),
      Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
          (c.π.app i) (c.w f).symm).inv.app F) q
        (cohomologyMap (c.π.app j) _ q y) = 0 →
      ∃ (k : J) (g : k ⟶ j),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f)).inv.app F) q
          (cohomologyMap (D.map g) _ q y) = 0) := by
  refine ⟨?_, ?_⟩
  · exact exists_cohomology_class_of_isLimit D c hc i F hF q
  · intro j f y hy
    have hz : cohomologyMap (c.π.app j) _ q y = 0 := by
      apply injective_sheafHMap_of_isIso
        ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
          (c.π.app i) (c.w f).symm).inv.app F) q
      simpa only [map_zero] using hy
    let E : Over j ⥤ Scheme.{u} := Over.forget j ⋙ D
    let : ∀ a : Over j, CompactSpace (E.obj a) :=
      fun a ↦ inferInstanceAs (CompactSpace (D.obj a.left))
    let : ∀ a : Over j, QuasiSeparatedSpace (E.obj a) :=
      fun a ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj a.left))
    let : ∀ {a b : Over j} (g : a ⟶ b), IsAffineHom (E.map g) :=
      fun g ↦ inferInstanceAs (IsAffineHom (D.map g.left))
    let π : E ⟶ (Functor.const (Over j)).obj (D.obj j) :=
      { app := fun a ↦ D.map a.hom
        naturality := fun a b g ↦ by
          dsimp [E]
          simpa only [Category.comp_id, ← D.map_comp] using congrArg D.map g.w }
    let c' : Cone E := c.whisker (Over.forget j)
    have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv _ c).symm hc
    have hz' : cohomologyMap (c'.π.app (Over.mk (𝟙 j)) ≫
        π.app (Over.mk (𝟙 j))) _ q y = 0 := by
      change cohomologyMap (c.π.app j ≫ D.map (𝟙 j)) _ q y = 0
      have hm : c.π.app j ≫ D.map (𝟙 j) = c.π.app j := by
        rw [D.map_id, Category.comp_id]
      exact (congrArg (fun m ↦ cohomologyMap m _ q y = 0) hm).mpr hz
    obtain ⟨a, ha⟩ := finiteStageKilling E π c' hc' _ q y (Over.mk (𝟙 j)) hz'
    refine ⟨a.left, a.hom, ?_⟩
    change cohomologyMap (D.map a.hom) _ q y = 0 at ha
    rw [ha, map_zero]

end AlgebraicGeometry.Etale
