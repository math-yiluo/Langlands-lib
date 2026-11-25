/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
import WeilConjectures.AlgebraicGeometry.TensorStalkComparisonSquares
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonInheritance

/-! # Tensor inheritance of the single-complex base-change condition

Source: Stacks Project, perfect.tex, Tag 0DJA, part (1)
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Tensoring a map satisfying the single-complex stalkwise base-change condition by an
arbitrary quasi-coherent derived object preserves the condition for the canonical
pullback tensor comparison. The comparison is characterized by its K-flat coordinate
and shared derived-counit equations, as in the paper.
Source: Stacks Project, perfect.tex, Tag 0DJA, part (1).
Proof: realize the canonical comparison as a monoidal model using the existing
existence and realization theorems. For the inherited
condition, identify both stalk comparisons with their ring-level cohomology models.
The original commuting square transfers h_stalk to the localized ring comparison.
Apply tensor inheritance for K-flat stalk complexes and the flat localization
A tensor-over-R B -> C. The tensor square then transfers invertibility back to every
coordinate presentation of the inherited map, by cancellation of its vertical isomorphisms.
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition). -/
theorem singleComplexInheritedTensorCondition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K.obj K'.obj φ) :
    ∃ m : (derivedPullback g').CoreMonoidal,
      IsCanonicalPullbackTensorComparison g' (fun A B ↦ (m.μIso A B).inv) ∧
      ∀ E : schemeDerivedQCohCategory X,
        SingleComplexBaseChange.StalkCondition f f' g g' sq
          (E.obj ⊗ K.obj) (((derivedPullback g').obj E.obj) ⊗ K'.obj)
          ((m.μIso E.obj K.obj).inv ≫ ((derivedPullback g').obj E.obj ◁ φ)) := by
  obtain ⟨τ, hτ⟩ := exists_canonicalPullbackTensorComparison g'
  obtain ⟨m, hm⟩ := canonicalPullbackTensor_monoidal_realization g' τ hτ
  have heq : (fun A B ↦ (m.μIso A B).inv) = τ := by
    funext A B
    exact hm A B
  have hcanonical : IsCanonicalPullbackTensorComparison g'
      (fun A B ↦ (m.μIso A B).inv) := by
    rw [heq]
    exact hτ
  refine ⟨m, hcanonical, ?_⟩
  intro E d z i
  obtain ⟨c⟩ := SingleComplexBaseChange.nonempty_coordinates g' K.obj K'.obj φ
  obtain ⟨hC, U, Q, N, hU, hQ, t, m, mU, hs⟩ :=
    exists_tensorStalkComparison_squares f f' g g' sq E K K' φ
      (fun A B ↦ (m.μIso A B).inv) hcanonical c d z
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  have hm (j : ℤ) : IsIso (m.localizedComparison j ≫ HomologicalComplex.homologyMap t j) := by
    obtain ⟨a, b, _, _, h, _⟩ := hs j
    have := h_stalk c z j
    have hcomp : IsIso (m.localizedComparison j ≫
        HomologicalComplex.homologyMap t j ≫ b.hom) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ b.hom
  have ht := ModuleCat.localizedTensorComparison_inheritance
    (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
    (SingleComplexBaseChange.B f' z) (SingleComplexBaseChange.C z)
    hC U Q N hU hQ t m mU hm i
  obtain ⟨_, _, aU, bU, _, h⟩ := hs i
  have hcomp : IsIso (aU.hom ≫
      SingleComplexBaseChange.stalkComparison f f' g g' sq d z i) := by
    rw [h, ← Category.assoc]
    infer_instance
  exact IsIso.of_isIso_comp_left aU.hom _

end AlgebraicGeometry
