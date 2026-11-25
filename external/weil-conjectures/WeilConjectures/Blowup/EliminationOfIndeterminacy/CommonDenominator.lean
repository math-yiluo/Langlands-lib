/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Common denominators for the coordinates of a partial map

On a quasi-compact open of an affine scheme, the coordinates of a morphism to relative affine
space are fractions with a common power of finitely many denominators, satisfying the cross
identities exactly (`AlgebraicGeometry.exists_uniform_denominator`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section CommonDenominator

/-! ### Common denominators for the coordinates of a partial map

On a quasi-compact open `U` of an affine scheme the coordinates of a morphism to a
relative affine space are fractions with a common denominator over a finite cover of `U`
by basic opens, and after enlarging the exponent the numerators satisfy the transition
identities exactly in the global sections of `X`. -/

open AffineSpace in
/-- **Common denominators for a partial map to affine space.** If `U` is a quasi-compact
open of an affine scheme `X` and `f : U ⟶ 𝔸(σ; X)`, then `U` is covered by finitely many
basic opens `D(uᵢ)` on which the coordinates of `f` are the fractions `cᵢⱼ / uᵢ ^ N` for a
single exponent `N`, and the numerators satisfy the compatibilities
`cᵢⱼ · uᵢ'^N = cᵢ'ⱼ · uᵢ^N` *exactly* in `Γ(X, ⊤)`. -/
lemma exists_uniform_denominator {X : Scheme.{u}} [IsAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {σ : Type u} [Finite σ] (f : U.toScheme ⟶ 𝔸(σ; X)) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → Γ(X, ⊤)) (hle : ∀ i, X.basicOpen (u i) ≤ U)
      (N : ℕ) (c : ι → σ → Γ(X, ⊤)),
      U = ⨆ i, X.basicOpen (u i) ∧ 0 < N ∧
      (∀ i i' j, c i j * u i' ^ N = c i' j * u i ^ N) ∧
      (∀ i j, (X.homOfLE (hle i) ≫ f).appTop (coord X j) *
          (X.basicOpen (u i)).ι.appTop (u i ^ N) = (X.basicOpen (u i)).ι.appTop (c i j)) := by
  classical
  obtain ⟨ι, hι, u, hle, hUeq⟩ := exists_finite_basicOpen_cover hU
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype σ := Fintype.ofFinite σ
  set t : ∀ i : ι, σ → Γ((X.basicOpen (u i)).toScheme, ⊤) :=
    fun i j ↦ (X.homOfLE (hle i) ≫ f).appTop (coord X j) with ht
  -- the coordinates are fractions with a power of `u i` as denominator
  have hfrac : ∀ i j, ∃ (a : Γ(X, ⊤)) (k : ℕ),
      t i j * (X.basicOpen (u i)).ι.appTop (u i ^ k) =
        (X.basicOpen (u i)).ι.appTop a := by
    intro i j
    obtain ⟨⟨aa, s⟩, hh⟩ := IsLocalization.surj (Submonoid.powers (u i)) (t i j)
    obtain ⟨k, hk⟩ := s.2
    have hk' : u i ^ k = (s : Γ(X, ⊤)) := hk
    exact ⟨aa, k, by rw [hk']; exact hh⟩
  choose a k hak using hfrac
  -- one exponent works for all coordinates
  set N : ℕ := Finset.univ.sup (fun p : ι × σ ↦ k p.1 p.2) with hN
  have hkN : ∀ i j, k i j ≤ N := fun i j ↦ Finset.le_sup (f := fun p : ι × σ ↦ k p.1 p.2)
    (Finset.mem_univ (i, j))
  have hfrac2 : ∀ i j, ∃ bb : Γ(X, ⊤),
      t i j * (X.basicOpen (u i)).ι.appTop (u i ^ N) = (X.basicOpen (u i)).ι.appTop bb := by
    intro i j
    refine ⟨a i j * u i ^ (N - k i j), ?_⟩
    have hpow : u i ^ N = u i ^ k i j * u i ^ (N - k i j) := by
      rw [← pow_add, Nat.add_sub_cancel' (hkN i j)]
    rw [hpow, map_mul, map_mul, ← mul_assoc, hak i j]
  choose b hbN using hfrac2
  -- the numerators agree on the overlaps after multiplying by a power of the denominators
  have hover : ∀ i i' j, ∃ m : ℕ,
      (u i * u i') ^ m * (b i j * u i' ^ N - b i' j * u i ^ N) = 0 := by
    intro i i' j
    have hii' : X.basicOpen (u i * u i') ≤ X.basicOpen (u i) := by
      rw [Scheme.basicOpen_mul]; exact inf_le_left
    have hi'i : X.basicOpen (u i * u i') ≤ X.basicOpen (u i') := by
      rw [Scheme.basicOpen_mul]; exact inf_le_right
    -- the two local coordinates restrict to the same section on the overlap
    have hres : ∀ (i₀ : ι) (h : X.basicOpen (u i * u i') ≤ X.basicOpen (u i₀))
        (x : Γ(X, ⊤)), (X.homOfLE h).appTop ((X.basicOpen (u i₀)).ι.appTop x) =
          (X.basicOpen (u i * u i')).ι.appTop x := by
      intro i₀ h x
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
    have hcommon : (X.homOfLE hii').appTop (t i j) = (X.homOfLE hi'i).appTop (t i' j) := by
      simp only [ht]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
        Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]
    have h1 := congrArg (X.homOfLE hii').appTop (hbN i j)
    have h2 := congrArg (X.homOfLE hi'i).appTop (hbN i' j)
    rw [map_mul, hres i hii', hres i hii'] at h1
    rw [map_mul, hres i' hi'i, hres i' hi'i, ← hcommon] at h2
    have h3 : (X.basicOpen (u i * u i')).ι.appTop (b i j * u i' ^ N) =
        (X.basicOpen (u i * u i')).ι.appTop (b i' j * u i ^ N) := by
      rw [map_mul, map_mul, ← h1, ← h2]; ring
    obtain ⟨cc, hcm⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (u i * u i')) (S := Γ((X.basicOpen (u i * u i')).toScheme, ⊤)) h3
    obtain ⟨mm, hmc⟩ := cc.2
    have hmc' : (u i * u i') ^ mm = (cc : Γ(X, ⊤)) := hmc
    exact ⟨mm, by rw [hmc', mul_sub, hcm, sub_self]⟩
  choose m hm using hover
  set M : ℕ := Finset.univ.sup (fun p : ι × ι × σ ↦ m p.1 p.2.1 p.2.2) + 1 with hM
  have hmM : ∀ i i' j, m i i' j ≤ M := fun i i' j ↦
    (Finset.le_sup (f := fun p : ι × ι × σ ↦ m p.1 p.2.1 p.2.2)
      (Finset.mem_univ (i, i', j))).trans (Nat.le_succ _)
  have hmM' : ∀ i i' j, (u i * u i') ^ M * (b i j * u i' ^ N - b i' j * u i ^ N) = 0 := by
    intro i i' j
    have : (u i * u i') ^ M = (u i * u i') ^ (M - m i i' j) * (u i * u i') ^ m i i' j := by
      rw [← pow_add, Nat.sub_add_cancel (hmM i i' j)]
    rw [this, mul_assoc, hm i i' j, mul_zero]
  refine ⟨ι, inferInstance, u, hle, N + M, fun i j ↦ b i j * u i ^ M, hUeq,
    by omega, ?_, ?_⟩
  · intro i i' j
    have := hmM' i i' j
    rw [mul_pow, mul_sub, sub_eq_zero] at this
    calc b i j * u i ^ M * u i' ^ (N + M)
        = u i ^ M * u i' ^ M * (b i j * u i' ^ N) := by ring
      _ = u i ^ M * u i' ^ M * (b i' j * u i ^ N) := this
      _ = b i' j * u i' ^ M * u i ^ (N + M) := by ring
  · intro i j
    rw [pow_add, map_mul, ← mul_assoc, hbN i j, ← map_mul]

end CommonDenominator

end AlgebraicGeometry
