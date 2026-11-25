/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The zero locus of a function

If `i : Z ⟶ X` is the base change of the zero section of `𝔸¹_S` along `h : X ⟶ 𝔸¹_S`, the image
of `i` is the complement of the basic open set of the function `h^* t`
(`AlgebraicGeometry.range_eq_compl_basicOpen_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The zero locus of a function: if `i : Z ⟶ X` is the base change of the zero section of
`𝔸¹_S` along `h : X ⟶ 𝔸¹_S`, the image of `i` is the complement of the basic open set of the
function `h^* t`. -/
theorem range_eq_compl_basicOpen_of_isPullback {X Z S : Scheme.{u}}
    (h : X ⟶ 𝔸(PUnit.{u + 1}; S)) (i : Z ⟶ X) (p : Z ⟶ S)
    (hi : IsPullback p i (AffineSpace.zeroSection PUnit.{u + 1} S) h) :
    Set.range i = (X.basicOpen (h.appTop (AffineSpace.coord S PUnit.unit)) : Set X)ᶜ := by
  have hr :
      Set.range i = Set.range (pullback.snd (AffineSpace.zeroSection PUnit.{u + 1} S) h) := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨hi.isoPullback.hom z, by rw [← Scheme.Hom.comp_apply, hi.isoPullback_hom_snd]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨hi.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, hi.isoPullback_inv_snd]⟩
  rw [hr, Scheme.Pullback.range_snd, AffineSpace.range_zeroSection]
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff, SetLike.mem_coe]
  rw [← Scheme.preimage_basicOpen_top]
  exact ⟨fun H ↦ H PUnit.unit, fun H _ ↦ H⟩

end AlgebraicGeometry
