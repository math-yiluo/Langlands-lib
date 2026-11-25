/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomologyBaseChangeReduced

/-!
# Base change of the top cohomology of a bounded complex of flat modules

Let `C` be a bounded complex of flat `A`-modules (indexed by `ℕ`) which is exact in all degrees
`> i`. Then the cokernels `Cᵏ⁺¹ ⧸ im dᵏ` are flat for `k ≥ i`, and the base change map
`B ⊗[A] Hⁱ(C) ⟶ Hⁱ(B ⊗[A] C)` is bijective for every `A`-algebra `B`
(`HomologicalComplex.bijective_homologyBaseChange_of_exactAt_of_flat`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace HomologicalComplex

variable {A : Type u} [CommRing A] (C : CochainComplex (ModuleCat.{u} A) ℕ)
  [hC : ∀ n, Module.Flat A (C.X n)] {N i : ℕ} (hN : ∀ n, N ≤ n → Subsingleton (C.X n))
  (hex : ∀ n, i < n → C.ExactAt n)

include hN hex in
/-- The cokernel `Cᵏ⁺¹ ⧸ im dᵏ` of a bounded complex of flat modules which is exact in degrees
`> i` is flat for `k ≥ i`. -/
theorem flat_quotient_range_d_of_exactAt :
    ∀ (n k : ℕ), N ≤ k + 1 + n → i ≤ k →
      Module.Flat A (C.X (k + 1) ⧸ LinearMap.range (C.d k (k + 1)).hom) := by
  intro n
  induction n with
  | zero =>
    intro k hk _
    have := hN (k + 1) (by lia)
    infer_instance
  | succ n ih =>
    intro k hk hik
    by_cases hNk : N ≤ k + 1
    · have := hN (k + 1) hNk
      infer_instance
    have hflat := ih (k + 1) (by lia) (by lia)
    -- exactness at `k + 1` identifies the quotient with the range of `dᵏ⁺¹`
    have h := (C.exactAt_iff' k (k + 1) (k + 2) (by simp) (by simp)).1 (hex (k + 1) (by lia))
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    change LinearMap.range (C.d k (k + 1)).hom = LinearMap.ker (C.d (k + 1) (k + 2)).hom at h
    rw [h]
    have hB : Function.Exact (LinearMap.range (C.d (k + 1) (k + 2)).hom).subtype
        (LinearMap.range (C.d (k + 1) (k + 2)).hom).mkQ := by
      intro x
      simp
    have : Module.Flat A (LinearMap.range (C.d (k + 1) (k + 2)).hom) :=
      Module.Flat.of_exact_of_flat_of_flat_right _ _ Subtype.val_injective
        (Submodule.mkQ_surjective _) hB
    exact Module.Flat.of_linearEquiv (C.d (k + 1) (k + 2)).hom.quotKerEquivRange

include hN hex in
/-- **Base change of the top cohomology.** Let `C` be a bounded complex of flat `A`-modules which
is exact in all degrees `> i`. Then for every `A`-algebra `B` the base change map
`B ⊗[A] Hⁱ(C) ⟶ Hⁱ(B ⊗[A] C)` is bijective. -/
theorem bijective_homologyBaseChange_of_exactAt_of_flat (B : Type u) [CommRing B]
    [Algebra A B] : Function.Bijective ((C.sc i).homologyBaseChange B) := by
  rw [ShortComplex.bijective_homologyBaseChange_iff]
  have : Module.Flat A ((C.sc i).X₃ ⧸ LinearMap.range (C.sc i).g.hom) := by
    change Module.Flat A (C.X ((ComplexShape.up ℕ).next i) ⧸
      LinearMap.range (C.d i ((ComplexShape.up ℕ).next i)).hom)
    rw [CochainComplex.next]
    exact C.flat_quotient_range_d_of_exactAt hN hex N i (by lia) le_rfl
  have : Module.Flat A (C.sc i).X₃ := hC _
  obtain ⟨hinj, hexact⟩ := LinearMap.injective_exact_lTensor_ker_of_flat (C.sc i).g.hom B
  exact (C.sc i).bijective_homologyBaseChangeAux_of_exact B hinj hexact

end HomologicalComplex
