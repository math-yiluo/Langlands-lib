/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerLocus
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Ampleness lifts along a square-zero thickening

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case
(blueprint: lem-sc-ample-square-zero-thickening).

The invertibility of the pullback `j^*L` is the first clause of the landed
`Scheme.Modules.invertible_pullback_tensor` (lem-weil-pbc-invertible-pullback-tensor);
it is not restated here.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

private theorem surjective_of_square_zero {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (hI : j.ker ^ 2 = ⊥) : Function.Surjective j := by
  have hs : j.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ j.ker 1, hI]
    exact Scheme.IdealSheafData.support_bot
  apply Set.range_eq_univ.mp
  rw [← j.isClosedEmbedding.isClosed_range.closure_eq, ← j.support_ker, hs]
  rfl

private theorem affine_of_affine_preimage {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsLocallyNoetherian X] [CompactSpace X]
    (hj : Function.Surjective j) (V : X.Opens) (hV : IsAffineOpen (j ⁻¹ᵁ V)) :
    IsAffineOpen V := by
  have : IsNoetherian X := ⟨⟩
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (V : Set X))
  have : IsNoetherian V := ⟨⟩
  have : IsAffine (j ⁻¹ᵁ V).toScheme := hV
  have : Surjective (j ∣_ V) := ⟨by
    intro x
    obtain ⟨z, hz⟩ := hj x.1
    refine ⟨⟨z, ?_⟩, ?_⟩
    · change j z ∈ V
      exact hz.symm ▸ x.2
    · apply Subtype.ext
      simpa using hz⟩
  exact isAffine_of_isFinite_surjective_of_isNoetherian (j ∣_ V)

/-- Ampleness lifts along a square-zero closed immersion of Noetherian schemes.
Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case
(blueprint: lem-sc-ample-square-zero-thickening).

Proof: the ideal sheaf `I` is quasi-coherent with `I^2 = 0`, so the sequence
`0 → I ⊗ L^n → L^n → j_*j^*L^n → 0` is exact. For a point `x`, choose
`s ∈ Γ(Z, j^*L^n)` with `x ∈ Z_s` affine. The boundary of `s` is a derivation-like
class `ξ` in `H^1(X, I ⊗ L^n)`, and `∂(s^{e+1}) = (e+1) s^e ξ`. Since `Z_s` is affine
and `I ⊗ L^n` is annihilated by `I`, the class `s^e ξ` vanishes for `e` large (Lemma 01XR),
so a power of `s` lifts to `s' ∈ Γ(X, L^{(e+1)n})`. Then `j⁻¹ X_{s'} = Z_s` and
`Z_s → X_{s'}` is a finite surjective morphism from an affine scheme to a Noetherian
scheme, so `X_{s'}` is affine (Lemma 01YQ); with `X` quasi-compact, `L` is ample.
-/
theorem isAmple_of_isAmple_tensorPullback_of_square_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Z] [CompactSpace Z]
    (L : X.Modules) [L.IsInvertible]
    (hI : j.ker ^ 2 = ⊥) :
    letI : ((Scheme.Modules.tensorPullback j).obj L).IsInvertible :=
      ((Scheme.Modules.invertible_pullback_tensor j).1 L).2
    AlgebraicGeometry.Scheme.Modules.IsAmple Z ((Scheme.Modules.tensorPullback j).obj L) →
      AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  let : ((tensorPullback j).obj L).IsInvertible :=
    ((invertible_pullback_tensor j).1 L).2
  intro hample
  have hj := surjective_of_square_zero j hI
  refine ⟨inferInstance, ?_⟩
  intro x
  obtain ⟨z, hz⟩ := hj x
  obtain ⟨n, hn, s, U, hzU, hUaff, hUlocus⟩ := hample.2 z
  have hU : (U : Set Z) = nonvanishingLocus (((tensorPullback j).obj L).tensorPow n) s :=
    Set.ext hUlocus
  obtain ⟨k, hk, t, htlocus⟩ :=
    exists_section_power_locus_of_square_zero j L hI n s U hU hUaff
  obtain ⟨V, hVlocus, _, _⟩ := nonvanishing_section_trivializes X (L.tensorPow (n * k)) t
  have hpre : j ⁻¹ᵁ V = U := by
    ext z
    change j z ∈ V ↔ z ∈ U
    exact (Set.ext_iff.mp hVlocus (j z)).trans (htlocus z)
  refine ⟨n * k, Nat.mul_pos hn hk, t, V, ?_, ?_, ?_⟩
  · have hzV : z ∈ j ⁻¹ᵁ V := hpre.symm ▸ hzU
    change j z ∈ V at hzV
    exact hz ▸ hzV
  · apply affine_of_affine_preimage j hj V
    exact hpre.symm ▸ hUaff
  · intro y
    change y ∈ V ↔ y ∈ nonvanishingLocus (L.tensorPow (n * k)) t
    exact Set.ext_iff.mp hVlocus y

end AlgebraicGeometry.Scheme.Modules
