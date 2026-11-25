/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Evaluation at affine weakly contractible pro-etale objects

Source: Stacks Project, Tags 0946 (1), 03DA and 0935 (2)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.Scheme.ProEt

/-- An affine pro-etale object has a finite covering family refining any covering sieve.
This follows from quasi-compact refinement of the underlying scheme cover. -/
theorem finite_cover_refinement (X : Scheme.{u}) (W : X.ProEt)
    [IsAffine W.left] (S : Sieve W) (hS : S ∈ topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ topology X W ∧ ∀ i, S (f i) := by
  classical
  have : (precoverage X).IsStableUnderComposition := by
    dsimp [precoverage]
    infer_instance
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by
    dsimp [precoverage]
    infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let E := T.preZeroHypercover
  let F := ProEt.forget X ⋙ Over.forget X
  let E' := E.map F
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage W.left := by
    have he : E'.presieve₀ = Presieve.map F T := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map F) T.presieve₀_preZeroHypercover
    rw [he]
    exact hT
  let U : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover U.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨A, r, hfin, _⟩ := QuasiCompactCover.exists_hom U
  let := hfin
  have (i : A.I₀) : WeaklyEtale (A.f i) := A.cover.map_prop i
  let V : A.I₀ → X.ProEt := fun i ↦ ProEt.mk (A.f i ≫ W.hom)
  let f : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (A.f i) (by rfl)
  refine ⟨A.I₀, hfin, V, f, ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    change Presieve.map F (Presieve.ofArrows V f) ∈ Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    change A.cover.presieve₀ ∈ Scheme.proetalePrecoverage W.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, A.cover.mem₀⟩
  · intro i
    let e := r.s₀ i
    let g : V i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = A.f i ≫ W.hom
      have he : r.h₀ i ≫ (E.f e).left = A.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hTS _ _ e.2) g

end AlgebraicGeometry.Scheme.ProEt
