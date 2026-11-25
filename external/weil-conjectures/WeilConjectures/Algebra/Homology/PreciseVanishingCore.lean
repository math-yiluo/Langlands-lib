/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # The localization comparison step for precise vanishing

Source: Stacks Project, Tags 064B and 064D
(blueprint: lem-pc-ring-precise-vanishing-core).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

/-- A vanishing result for homotopy morphisms lifts across the derived localization.
Source: Stacks Project, Tags 064B and 064D
(blueprint: lem-pc-ring-precise-vanishing-core).
Proof: the upper bound and termwise projectivity make `P` K-projective. Transport a
morphism in the derived category along `quotientCompQhIso`, represent it by a
homotopy-category morphism using `Qh_map_bijective`, apply `hzero`, and cancel the
two comparison isomorphisms.
-/
theorem precise_vanishing_of_homotopy_zero
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P K : CochainComplex A ℤ)
    (hPbounded : ∃ a b : ℤ,
      (∀ i : ℤ, i < a → IsZero (P.X i)) ∧
      (∀ i : ℤ, b < i → IsZero (P.X i)))
    (hPprojective : ∀ i : ℤ, Projective (P.X i))
    (hzero : ∀ g :
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K),
      DerivedCategory.Qh.map g = 0) :
    ∀ f : (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K), f = 0 := by
  obtain ⟨_, b, _, hb⟩ := hPbounded
  let : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hb i hi
  let : ∀ i, Projective (P.X i) := hPprojective
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  intro f
  let eP := (DerivedCategory.quotientCompQhIso A).app P
  let eK := (DerivedCategory.quotientCompQhIso A).app K
  let f' := eP.hom ≫ f ≫ eK.inv
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).surjective f'
  have hz : DerivedCategory.Qh.map g = 0 := hzero g
  have hf' : f' = 0 := by rw [← hg, hz]
  rw [← cancel_epi eP.hom, ← cancel_mono eK.inv]
  simpa [f'] using hf'

end CategoryTheory
