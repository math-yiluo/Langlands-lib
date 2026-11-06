import Langlands.LinearAlgebra.RootFaceCone
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Reflections, restriction and integral sign patterns for root weights -/

noncomputable section

open Finset TensorProduct

namespace Langlands.LinearAlgebra.RootFaceCone

section Reflection

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : LinearMap.BilinForm ℝ E}

/-- An isometry negating `β` and moving every vector along `β` fixes every
vector `B`-orthogonal to `β`. -/
theorem eq_self_of_isometry_neg (w : E ≃ₗ[ℝ] E) (hB : ∀ x y, B (w x) (w y) = B x y)
    {β : E} (hβ : w β = -β) (hrank : ∀ x, ∃ t : ℝ, w x = x + t • β)
    (hββ : β ≠ 0 → 0 < B β β) {z : E} (hz : B β z = 0) : w z = z := by
  obtain ⟨t, ht⟩ := hrank z
  have h1 : B β (w z) = 0 := by
    have h := hB β z
    rw [hβ, hz, map_neg, LinearMap.neg_apply, neg_eq_zero] at h
    exact h
  rw [ht, map_add, map_smul, hz, zero_add, smul_eq_mul] at h1
  by_cases hβ0 : β = 0
  · rw [ht, hβ0, smul_zero, add_zero]
  · have hpos := hββ hβ0
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hpos.ne'
    rw [ht, ht0, zero_smul, add_zero]

/-- A vector fixed by an isometry negating `β` is `B`-orthogonal to `β`. -/
theorem apply_eq_zero_of_isometry_fixed (w : E ≃ₗ[ℝ] E) (hB : ∀ x y, B (w x) (w y) = B x y)
    {β : E} (hβ : w β = -β) {x : E} (hx : w x = x) : B β x = 0 := by
  have h := hB β x
  rw [hβ, hx, map_neg, LinearMap.neg_apply] at h
  linarith

variable {Φ : Finset E} {m : E → ℝ}

/-- An isometry permuting the roots with their multiplicities fixes the root weight
of every fixed vector. -/
theorem rootWeight_isometry_fixed (w : E ≃ₗ[ℝ] E) (hB : ∀ x y, B (w x) (w y) = B x y)
    (hΦ : ∀ γ ∈ Φ, w γ ∈ Φ) (hm : ∀ γ ∈ Φ, m (w γ) = m γ) {z : E} (hz : w z = z) :
    w (rootWeight B Φ m z) = rootWeight B Φ m z := by
  classical
  have himage : Φ.image w = Φ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hx
      exact hΦ γ hγ
    · rw [Finset.card_image_of_injective _ w.injective]
  have hBz : ∀ α, B (w α) z = B α z := fun α => by
    conv_lhs => rw [← hz]
    exact hB α z
  unfold rootWeight
  rw [map_sum]
  conv_rhs => rw [← himage]
  rw [Finset.filter_image, Finset.sum_image (fun x _ y _ h => w.injective h)]
  refine Finset.sum_congr ?_ ?_
  · ext γ
    simp only [Finset.mem_filter, hBz]
  · intro γ hγ
    rw [map_smul, hm γ (Finset.mem_filter.1 hγ).1]

/-- **Levi orthogonality from reflections.** If every root `β` has an isometric
reflection, negating `β`, moving every vector along `β`, and permuting the roots
with their multiplicities, then `B β (ρ y) = 0` whenever `B β y = 0`. -/
theorem rootWeight_levi_of_reflections (hpos : ∀ x : E, x ≠ 0 → 0 < B x x)
    (hrefl : ∀ β ∈ Φ, ∃ w : E ≃ₗ[ℝ] E, (∀ x y, B (w x) (w y) = B x y) ∧ w β = -β ∧
      (∀ x, ∃ t : ℝ, w x = x + t • β) ∧ (∀ γ ∈ Φ, w γ ∈ Φ) ∧ ∀ γ ∈ Φ, m (w γ) = m γ) :
    ∀ y : E, ∀ β ∈ Φ, B β y = 0 → B β (rootWeight B Φ m y) = 0 := by
  intro y β hβ hy
  obtain ⟨w, hB, hwβ, hrank, hΦ, hm⟩ := hrefl β hβ
  have hwy := eq_self_of_isometry_neg w hB hwβ hrank (hpos β) hy
  exact apply_eq_zero_of_isometry_fixed w hB hwβ (rootWeight_isometry_fixed w hB hΦ hm hwy)

/-- The root weight of the image of an injectively indexed family. -/
theorem rootWeight_image_eq {X : Type*} [DecidableEq E] (R : Finset X) {ι : X → E}
    (hι : Function.Injective ι) (n : X → ℝ) (y : E) :
    rootWeight B (R.image ι) (Function.extend ι n 0) y =
      ∑ χ ∈ R.filter (fun χ => 0 < B (ι χ) y), n χ • ι χ := by
  unfold rootWeight
  rw [Finset.filter_image, Finset.sum_image (fun x _ y _ h => hι h)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hι.extend_apply]

end Reflection

section Descent

variable {E F X Y : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {BT : LinearMap.BilinForm ℝ E} {BA : LinearMap.BilinForm ℝ F}
  {q : E →ₗ[ℝ] F} {L : F →ₗ[ℝ] E}
  {RT : Finset X} {ιT : X → E} {mT : X → ℝ} {RA : Finset Y} {ιA : Y → F} {mA : Y → ℝ}
  {res : X → Y}

private theorem apply_eq_zero_of_mem_span_set {S : Set E} {w z : E}
    (hw : w ∈ Submodule.span ℝ S) (h : ∀ s ∈ S, BT s z = 0) : BT w z = 0 := by
  have hle : Submodule.span ℝ S ≤ LinearMap.ker (BT.flip z) := by
    rw [Submodule.span_le]
    intro s hs
    exact h s hs
  exact hle hw

variable (hcompat : ∀ x y, BT (L x) y = BA x (q y))
  (hTsymm : ∀ x y, BT x y = BT y x) (hAsymm : ∀ x y, BA x y = BA y x)
  (hres : ∀ χ, q (ιT χ) = ιA (res χ))

include hcompat hTsymm hAsymm hres in
private theorem pairing_lift (y : F) (χ : X) : BT (ιT χ) (L y) = BA (ιA (res χ)) y := by
  rw [hTsymm, hcompat, hres, hAsymm]

include hcompat hTsymm hAsymm hres in
/-- **Restriction of root weights.** Restricting the root weight of the lift of `y`
gives the root weight of `y`, when multiplicities add along restriction. -/
theorem restrict_indexedRootWeight [DecidableEq Y]
    (hRA : ∀ χ ∈ RT, ιA (res χ) ≠ 0 → res χ ∈ RA)
    (hmult : ∀ α ∈ RA, mA α = ∑ χ ∈ RT.filter (fun χ => res χ = α), mT χ) (y : F) :
    q (∑ χ ∈ RT.filter (fun χ => 0 < BT (ιT χ) (L y)), mT χ • ιT χ) =
      ∑ α ∈ RA.filter (fun α => 0 < BA (ιA α) y), mA α • ιA α := by
  rw [map_sum]
  simp only [map_smul, hres, pairing_lift hcompat hTsymm hAsymm hres]
  rw [← Finset.sum_fiberwise_of_maps_to (g := res)
    (t := RA.filter (fun α => 0 < BA (ιA α) y))]
  · refine Finset.sum_congr rfl fun α hα => ?_
    have hαpos := (Finset.mem_filter.1 hα).2
    rw [Finset.filter_filter]
    have hfil : RT.filter (fun χ => 0 < BA (ιA (res χ)) y ∧ res χ = α) =
        RT.filter (fun χ => res χ = α) := by
      refine Finset.filter_congr fun χ _ => ?_
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h ▸ hαpos, h⟩
    rw [hfil, hmult α (Finset.mem_filter.1 hα).1, Finset.sum_smul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [(Finset.mem_filter.1 hχ).2]
  · intro χ hχ
    obtain ⟨hχR, hχpos⟩ := Finset.mem_filter.1 hχ
    refine Finset.mem_filter.2 ⟨hRA χ hχR ?_, hχpos⟩
    intro h0
    rw [h0, map_zero, LinearMap.zero_apply] at hχpos
    exact lt_irrefl _ hχpos

variable (hqL : ∀ x, q (L x) = x)

include hqL hres in
/-- The lift of a restricted root lies in the span of the roots restricting to
zero or to it. -/
theorem lift_mem_span_roots
    (hsurj : ∀ α ∈ RA, ∃ χ ∈ RT, res χ = α)
    (hker : ∀ k, q k = 0 → k ∈ Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ ιA (res χ) = 0}))
    {α : Y} (hα : α ∈ RA) :
    L (ιA α) ∈ Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ (ιA (res χ) = 0 ∨ res χ = α)}) := by
  obtain ⟨χ₀, hχ₀, hres₀⟩ := hsurj α hα
  have hk : q (ιT χ₀ - L (ιA α)) = 0 := by
    rw [map_sub, hqL, hres, hres₀, sub_self]
  have hkmem := hker _ hk
  have hmono : Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ ιA (res χ) = 0}) ≤
      Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ (ιA (res χ) = 0 ∨ res χ = α)}) :=
    Submodule.span_mono (Set.image_mono fun χ hχ => ⟨hχ.1, Or.inl hχ.2⟩)
  have h₀ : ιT χ₀ ∈ Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ (ιA (res χ) = 0 ∨ res χ = α)}) :=
    Submodule.subset_span ⟨χ₀, ⟨hχ₀, Or.inr hres₀⟩, rfl⟩
  have := Submodule.sub_mem _ h₀ (hmono hkmem)
  rwa [sub_sub_cancel] at this

include hcompat hTsymm hAsymm hres hqL in
/-- **Levi orthogonality descends along restriction.** -/
theorem indexedRootWeight_levi_descent [DecidableEq Y]
    (hRA : ∀ χ ∈ RT, ιA (res χ) ≠ 0 → res χ ∈ RA)
    (hmult : ∀ α ∈ RA, mA α = ∑ χ ∈ RT.filter (fun χ => res χ = α), mT χ)
    (hsurj : ∀ α ∈ RA, ∃ χ ∈ RT, res χ = α)
    (hker : ∀ k, q k = 0 → k ∈ Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ ιA (res χ) = 0}))
    (hlevi : ∀ z : E, ∀ χ ∈ RT, BT (ιT χ) z = 0 →
      BT (ιT χ) (∑ χ' ∈ RT.filter (fun χ' => 0 < BT (ιT χ') z), mT χ' • ιT χ') = 0)
    (y : F) {α : Y} (hα : α ∈ RA) (hy : BA (ιA α) y = 0) :
    BA (ιA α) (∑ α' ∈ RA.filter (fun α' => 0 < BA (ιA α') y), mA α' • ιA α') = 0 := by
  rw [← restrict_indexedRootWeight hcompat hTsymm hAsymm hres hRA hmult y, ← hcompat]
  apply apply_eq_zero_of_mem_span_set (lift_mem_span_roots hres hqL hsurj hker hα)
  rintro _ ⟨χ, ⟨hχ, hχ0⟩, rfl⟩
  apply hlevi (L y) χ hχ
  rw [pairing_lift hcompat hTsymm hAsymm hres]
  rcases hχ0 with h | h
  · rw [h, map_zero, LinearMap.zero_apply]
  · rw [h, hy]

include hcompat hres hqL in
/-- Vectors orthogonal to every ambient root restrict to vectors orthogonal to every
restricted root. -/
theorem restrict_orthogonal_roots
    (hsurj : ∀ α ∈ RA, ∃ χ ∈ RT, res χ = α)
    (hker : ∀ k, q k = 0 → k ∈ Submodule.span ℝ (ιT '' {χ | χ ∈ RT ∧ ιA (res χ) = 0}))
    {g : E} (hg : ∀ χ ∈ RT, BT (ιT χ) g = 0) {α : Y} (hα : α ∈ RA) :
    BA (ιA α) (q g) = 0 := by
  rw [← hcompat]
  apply apply_eq_zero_of_mem_span_set (lift_mem_span_roots hres hqL hsurj hker hα)
  rintro _ ⟨χ, ⟨hχ, _⟩, rfl⟩
  exact hg χ hχ

end Descent

section Realization

variable {N : Type*} [AddCommGroup N] {ι : Type*}

/-- **Integral realization of sign patterns.** For finitely many integral functionals
`φ j` on a lattice and their real scalar extensions `ψ j`, every real vector has an
integral vector with the same positive functionals. -/
theorem exists_int_sign_realization (s : Finset ι) (φ : ι → N →ₗ[ℤ] ℤ)
    (ψ : ι → (ℝ ⊗[ℤ] N) →ₗ[ℝ] ℝ) (hψ : ∀ j (t : ℝ) (n : N), ψ j (t ⊗ₜ n) = t * φ j n)
    (g : ℝ ⊗[ℤ] N) : ∃ μ : N, ∀ j ∈ s, (0 < φ j μ ↔ 0 < ψ j g) := by
  classical
  set Z := s.filter (fun j => ψ j g = 0) with hZ
  let Λ : N →ₗ[ℤ] (Z → ℤ) := LinearMap.pi (fun j : Z => φ j)
  let K := LinearMap.ker Λ
  have hex : Function.Exact K.subtype Λ := LinearMap.exact_subtype_ker_map Λ
  have hexR := Module.Flat.lTensor_exact ℝ hex
  have hrid : ∀ j, ∀ x : ℝ ⊗[ℤ] N, TensorProduct.rid ℤ ℝ ((φ j).lTensor ℝ x) = ψ j x := by
    intro j x
    induction x with
    | tmul t n =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hψ, zsmul_eq_mul, mul_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hpi : ∀ j : Z, ∀ x : ℝ ⊗[ℤ] N,
      TensorProduct.piRight ℤ ℤ ℝ (fun _ : Z => ℤ) (Λ.lTensor ℝ x) j =
        (φ j).lTensor ℝ x := by
    intro j x
    induction x with
    | tmul t n =>
      rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
        LinearMap.lTensor_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy, map_add]
  have hg : Λ.lTensor ℝ g = 0 := by
    apply (TensorProduct.piRight ℤ ℤ ℝ (fun _ : Z => ℤ)).injective
    rw [map_zero]
    funext j
    rw [hpi, Pi.zero_apply]
    apply (TensorProduct.rid ℤ ℝ).injective
    rw [map_zero, hrid]
    exact (Finset.mem_filter.1 j.2).2
  obtain ⟨gK, hgK⟩ := (hexR g).1 hg
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset gK
  -- the values of the functionals on the generators
  have hψg : ∀ j, ψ j g = ∑ i ∈ S, i.1 * (φ j (i.2 : N) : ℝ) := by
    intro j
    rw [← hgK, hS, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, hψ]
    rfl
  have hK : ∀ i : K, ∀ j ∈ Z, φ j (i : N) = 0 := by
    intro i j hj
    have h := congrFun (LinearMap.mem_ker.1 i.2) ⟨j, hj⟩
    exact h
  set c : ι → ℝ := fun j => ψ j g with hc
  set e : ι → ℝ := fun j => ∑ i ∈ S, |(φ j (i.2 : N) : ℝ)| with he
  obtain ⟨n, hn⟩ := exists_nat_gt
    (∑ j ∈ s.filter (fun j => c j ≠ 0), e j / |c j|)
  have hn' : ∀ j ∈ s, c j ≠ 0 → e j < n * |c j| := by
    intro j hj hcj
    have hcpos : 0 < |c j| := abs_pos.2 hcj
    have hle : e j / |c j| ≤ ∑ j ∈ s.filter (fun j => c j ≠ 0), e j / |c j| :=
      Finset.single_le_sum (f := fun j => e j / |c j|)
        (fun j _ => div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _))
        (Finset.mem_filter.2 ⟨hj, hcj⟩)
    have := (div_lt_iff₀ hcpos).1 (lt_of_le_of_lt hle hn)
    exact this
  refine ⟨∑ i ∈ S, ⌊(n : ℝ) * i.1⌋ • (i.2 : N), fun j hj => ?_⟩
  have hφμ : (φ j (∑ i ∈ S, ⌊(n : ℝ) * i.1⌋ • (i.2 : N)) : ℝ) =
      ∑ i ∈ S, (⌊(n : ℝ) * i.1⌋ : ℝ) * (φ j (i.2 : N) : ℝ) := by
    rw [map_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, smul_eq_mul, Int.cast_mul]
  change 0 < φ j _ ↔ 0 < c j
  by_cases hcj : c j = 0
  · have hjZ : j ∈ Z := Finset.mem_filter.2 ⟨hj, hcj⟩
    have h0 : φ j (∑ i ∈ S, ⌊(n : ℝ) * i.1⌋ • (i.2 : N)) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, hK i.2 j hjZ, smul_zero]
    rw [h0, hcj]
    exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
  · have hgap := hn' j hj hcj
    have hcval : c j = ∑ i ∈ S, i.1 * (φ j (i.2 : N) : ℝ) := hψg j
    -- the integral value is within `e j` of `n * c j`
    have hdiff : |(φ j (∑ i ∈ S, ⌊(n : ℝ) * i.1⌋ • (i.2 : N)) : ℝ) - n * c j| ≤ e j := by
      rw [hφμ, hcval, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hfl : |(⌊(n : ℝ) * i.1⌋ : ℝ) - n * i.1| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [Int.lt_floor_add_one ((n : ℝ) * i.1)]
        · linarith [Int.floor_le ((n : ℝ) * i.1)]
      calc |(⌊(n : ℝ) * i.1⌋ : ℝ) * (φ j (i.2 : N) : ℝ) - n * (i.1 * (φ j (i.2 : N) : ℝ))|
          = |(⌊(n : ℝ) * i.1⌋ : ℝ) - n * i.1| * |(φ j (i.2 : N) : ℝ)| := by
            rw [← abs_mul]
            ring_nf
        _ ≤ 1 * |(φ j (i.2 : N) : ℝ)| :=
            mul_le_mul_of_nonneg_right hfl (abs_nonneg _)
        _ = |(φ j (i.2 : N) : ℝ)| := one_mul _
    rw [← Int.cast_pos (R := ℝ)]
    rcases lt_or_gt_of_ne hcj with hneg | hpos
    · rw [abs_of_neg hneg] at hgap
      have := (abs_le.1 hdiff).2
      constructor
      · intro h
        exfalso
        linarith
      · intro h
        exact absurd h (not_lt.2 hneg.le)
    · rw [abs_of_pos hpos] at hgap
      have := (abs_le.1 hdiff).1
      constructor
      · intro _
        exact hpos
      · intro _
        linarith

end Realization

end Langlands.LinearAlgebra.RootFaceCone
