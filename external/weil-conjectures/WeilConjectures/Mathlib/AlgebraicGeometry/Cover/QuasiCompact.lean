/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Quasi-compact covers obtained by refinement

Let `j k : Y k ⟶ S` be finitely many quasi-compact morphisms jointly covering `S`, and let `E k`
be a quasi-compact cover of `Y k`. A family `D` of morphisms to `S` through which every member of
every `E k`, followed by `j k`, factors is a quasi-compact cover of `S`
(`AlgebraicGeometry.QuasiCompactCover.of_comp_factor`). The pieces `Y k` need not be open: this
is how a section vanishing on neighbourhoods of the strata of a stratification is seen to vanish
on a cover.
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Refining quasi-compact covers of the members of a quasi-compact family.** Let
`j k : Y k ⟶ S` be finitely many quasi-compact morphisms jointly covering `S`, let `E k` be a
quasi-compact cover of `Y k`, and let `D` be a family of morphisms to `S` through which every
member of every `E k`, followed by `j k`, factors. Then `D` is quasi-compact. -/
lemma QuasiCompactCover.of_comp_factor {S : Scheme.{u}} {κ : Type*} [Finite κ]
    {Y : κ → Scheme.{u}} (j : ∀ k, Y k ⟶ S) [∀ k, QuasiCompact (j k)]
    (hj : ∀ x, ∃ k, x ∈ Set.range (j k)) (E : ∀ k, PreZeroHypercover.{w} (Y k))
    [∀ k, QuasiCompactCover (E k)] (D : PreZeroHypercover.{w'} S) (a : ∀ k, (E k).I₀ → D.I₀)
    (φ : ∀ k m, (E k).X m ⟶ D.X (a k m)) (hφ : ∀ k m, φ k m ≫ D.f (a k m) = (E k).f m ≫ j k) :
    QuasiCompactCover D := by
  constructor
  intro A hA
  have hU : IsCompactOpenCovered (fun p : Σ k, (E k).I₀ ↦ ((E p.1).f p.2 ≫ j p.1).base)
      (A : Set S) := by
    refine .of_iUnion_eq_of_finite (fun k ↦ (j k).base '' ((j k).base ⁻¹' A)) ?_ fun k ↦ ?_
    · ext x
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, y, hy, rfl⟩
        exact hy
      · intro hx
        obtain ⟨k, y, rfl⟩ := hj x
        exact ⟨k, y, hx, rfl⟩
    · have hc : IsCompact (((j k) ⁻¹ᵁ A : (Y k).Opens) : Set (Y k)) :=
        (j k).isCompact_preimage hA.isCompact
      obtain ⟨s, hs, V, hVc, hV⟩ := QuasiCompactCover.isCompactOpenCovered_of_isCompact (E k) hc
      have := hs.to_subtype
      refine .of_finite (fun i : s ↦ (⟨k, i.1⟩ : Σ k, (E k).I₀)) (fun i ↦ V i.1 i.2)
        (fun i ↦ hVc i.1 i.2) ?_
      change _ = (j k).base '' ((j k ⁻¹ᵁ A : (Y k).Opens) : Set (Y k))
      rw [← hV, Set.image_iUnion₂]
      ext x
      simp only [Set.mem_iUnion, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      exact ⟨fun ⟨i, h⟩ ↦ ⟨i.1, i.2, h⟩, fun ⟨i, hi, h⟩ ↦ ⟨⟨i, hi⟩, h⟩⟩
  refine IsCompactOpenCovered.of_comp (f := fun i ↦ (D.f i).base) (a := fun p ↦ a p.1 p.2)
    (g := fun p : Σ k, (E k).I₀ ↦ ((E p.1).f p.2 ≫ j p.1).base)
    (fun p ↦ (φ p.1 p.2).base) (fun p ↦ (φ p.1 p.2).base.hom.continuous) (fun p ↦ ?_)
    (fun i ↦ (D.f i).base.hom.continuous) A.isOpen hU
  ext x
  simp only [Function.comp_apply, ← Scheme.Hom.comp_apply, hφ]

end AlgebraicGeometry
