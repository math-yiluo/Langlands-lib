/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The sheaf of differentials of projective space

The sheaf of relative differentials `Ω¹_{ℙ/S}` of `ℙ = ℙ(n; S)` is locally free of rank `d`, where
`n` has `d + 1` elements: on the standard open `Uᵢ = D₊(xᵢ)`, the affine space with coordinates
`x_k / xᵢ` (`k ≠ i`), it is free on the differentials `d(x_k / xᵢ)`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.smoothOfRelativeDimension`: `ℙ(n; S) ⟶ S` is smooth of
  relative dimension `d`.
- `AlgebraicGeometry.ProjectiveSpace.isFiniteLocallyFreeOfRank_relativeDifferentials`:
  `Ω¹_{ℙ(n; S)/S}` is finite locally free of rank `d`.

## See also

- `AlgebraicGeometry.ProjectiveSpace.canonicalModuleIsoTwist`: the canonical module
  `ω_ℙ = Λᵈ Ω¹_{ℙ/A}` is isomorphic to `𝒪(-d-1)`, sending the local bases
  `ηᵢ = (-1)ⁱ ⋀_{k ≠ i} d(x_k / xᵢ)` to the bases `eᵢ^{(-d-1)}` of the twist. For `d = 1`, where
  `ω = Ω¹`, see also `AlgebraicGeometry.ProjectiveLine.nonempty_relativeDifferentials_iso_twist`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- **Projective space is smooth.** For `n` with `Nat.card n = d + 1`, the projective space
`ℙ(n; S) ⟶ S` is smooth of relative dimension `d`: on the standard open `D₊(xᵢ)` it is the affine
space `𝔸({k // k ≠ i}; S)`. -/
theorem smoothOfRelativeDimension {d : ℕ} (hn : Nat.card n = d + 1) :
    SmoothOfRelativeDimension d (ℙ(n; S) ↘ S) := by
  have : Finite n := Nat.finite_of_card_ne_zero (by omega)
  refine smoothOfRelativeDimension_of_forall_exists_mem _ d fun y ↦ ?_
  have : y ∈ (⊤ : ℙ(n; S).Opens) := trivial
  rw [← iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨_, hi, ?_⟩
  rw [← standardOpenIso_hom_over]
  have h : Nat.card {j : n // j ≠ i} = d := by
    have := Fintype.ofFinite n
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hn, Nat.add_sub_cancel]
  have := AffineSpace.smoothOfRelativeDimension_over {j : n // j ≠ i} S
  rw [h] at this
  have h' : SmoothOfRelativeDimension (0 + d)
      ((standardOpenIso n S i).hom ≫ (𝔸({j : n // j ≠ i}; S) ↘ S)) :=
    inferInstance
  rwa [zero_add] at h'

/-- **The differentials of projective space are locally free of rank `d`.** For `n` with
`Nat.card n = d + 1`, the sheaf of relative differentials `Ω¹_{ℙ(n; S)/S}` is finite locally
free of rank `d`: on the standard open `Uᵢ` it is free on the differentials `d(x_k / xᵢ)`. -/
theorem isFiniteLocallyFreeOfRank_relativeDifferentials {d : ℕ} (hn : Nat.card n = d + 1) :
    (ℙ(n; S) ↘ S).relativeDifferentials.IsFiniteLocallyFreeOfRank d :=
  have := smoothOfRelativeDimension n S hn
  Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials _ d

end AlgebraicGeometry.ProjectiveSpace
