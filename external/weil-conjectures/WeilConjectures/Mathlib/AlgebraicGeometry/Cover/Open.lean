/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Extensionality of opens along an open cover

Two open subsets of a scheme agree if their preimages under every chart of an open cover
agree.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Two open subsets of a scheme agree if their preimages under every chart of an open
cover agree. -/
lemma Scheme.Opens.ext_of_openCover {Y : Scheme.{u}} (𝒰 : Y.OpenCover) {U V : Y.Opens}
    (h : ∀ i, 𝒰.f i ⁻¹ᵁ U = 𝒰.f i ⁻¹ᵁ V) : U = V := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  rw [← hy]
  constructor
  · intro hx
    have hyU : y ∈ 𝒰.f (𝒰.idx x) ⁻¹ᵁ U := hx
    rw [h] at hyU
    exact hyU
  · intro hx
    have hyV : y ∈ 𝒰.f (𝒰.idx x) ⁻¹ᵁ V := hx
    rw [← h] at hyV
    exact hyV

end AlgebraicGeometry
