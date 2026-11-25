/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import WeilConjectures.FieldTheory.Cr

/-!
# Galois `2`-cocycles over a quasi-algebraically closed field are coboundaries

Let `L / K` be a finite Galois extension with group `G` and `f : G × G → Lˣ` a `2`-cocycle,
`σ(f(τ, ρ)) f(σ, τρ) = f(στ, ρ) f(σ, τ)`. If `K` is quasi-algebraically closed (`C₁`), then `f`
is a coboundary: `f(σ, τ) = σ(c(τ)) c(σ) c(στ)⁻¹` for some `c : G → Lˣ`. This is the vanishing
of `H²(G, Lˣ)`, i.e. of the relative Brauer group of `L / K`.

The proof goes through the crossed product algebra. It is realised concretely as the algebra
`A ⊆ End_K(W)` of the operators `∑_σ a_σ U_σ` on `W = (G → L)`, where `a ∈ L` acts by
multiplication and `(U_σ w)(π) = σ(w(σ⁻¹π)) f(σ, σ⁻¹π)`; then `U_σ a = σ(a) U_σ` and
`U_σ U_τ = f(σ, τ) U_{στ}`. The algebra `A` is central simple of dimension `[L : K]²`, so it is a
matrix algebra over the `C₁` field `K` (`IsQuasiAlgClosed.exists_algEquiv_matrix`). Hence `W`
contains an `A`-submodule `S` of `K`-dimension at most `[L : K]`; it is an `L`-line, and the
operators `U_σ` act on a generator `v` of `S` by `U_σ v = c(σ) v`, which exhibits `f` as the
coboundary of `c`.

## Main statements

- `IsQuasiAlgClosed.exists_algEquiv_matrix`: a central simple algebra over a `C₁` field is a
  matrix algebra.
- `IsQuasiAlgClosed.exists_eq_of_isCocycle`: Galois `2`-cocycles over a `C₁` field are
  coboundaries.
-/

@[expose] public section

open Module

namespace IsQuasiAlgClosed

/-- **Central simple algebras over a `C₁` field are matrix algebras.** -/
theorem exists_algEquiv_matrix (K A : Type*) [Field K] [IsQuasiAlgClosed K] [Ring A]
    [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ n : ℕ, NeZero n ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  have := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Algebra.IsCentral K D := Algebra.IsCentral.of_algEquiv_matrix e
  let f : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D) <| by
    refine ⟨(algebraMap K D).injective, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (Algebra.ofId K D).toLinearMap)
      (by rw [Module.finrank_self, finrank_eq_one_of_isCentral K D])).mp
      (algebraMap K D).injective
  exact ⟨n, hn, ⟨e.trans f.symm.mapMatrix⟩⟩

section CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (f : Gal(L/K) → Gal(L/K) → Lˣ)

namespace CrossedProduct



/-- The `K`-vector space `W = (G → L)` on which the crossed product acts. -/
abbrev W (K L : Type*) [Field K] [Field L] [Algebra K L] : Type _ := Gal(L/K) → L

/-- Multiplication by `a ∈ L` on `W`. -/
def mulOp (a : L) : Module.End K (W K L) :=
  DistribSMul.toLinearMap K (W K L) a

@[simp]
lemma mulOp_apply (a : L) (w : W K L) (π : Gal(L/K)) : mulOp a w π = a * w π := rfl

/-- The operator `(U_σ w)(π) = σ(w(σ⁻¹π)) f(σ, σ⁻¹π)` on `W`. -/
def U (σ : Gal(L/K)) : Module.End K (W K L) where
  toFun w π := σ (w (σ⁻¹ * π)) * f σ (σ⁻¹ * π)
  map_add' w w' := by
    funext π
    simp [add_mul]
  map_smul' c w := by
    funext π
    simp [Algebra.smul_def, mul_assoc]

@[simp]
lemma U_apply (σ : Gal(L/K)) (w : W K L) (π : Gal(L/K)) :
    U f σ w π = σ (w (σ⁻¹ * π)) * f σ (σ⁻¹ * π) := rfl

lemma mulOp_mul (a b : L) : mulOp (K := K) a * mulOp b = mulOp (a * b) := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp [mul_assoc]

lemma mulOp_one : mulOp (K := K) (1 : L) = 1 := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp

lemma mulOp_add (a b : L) : mulOp (K := K) (a + b) = mulOp a + mulOp b := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp [add_mul]

lemma mulOp_zero : mulOp (K := K) (0 : L) = 0 := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp

lemma mulOp_algebraMap (c : K) : mulOp (K := K) (algebraMap K L c) = algebraMap K _ c := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp [Algebra.smul_def]

lemma U_mul_mulOp (σ : Gal(L/K)) (a : L) : U f σ * mulOp a = mulOp (σ a) * U f σ := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp [mul_assoc]

variable {f}
variable (hf : ∀ σ τ ρ : Gal(L/K), σ (f τ ρ : L) * f σ (τ * ρ) = f (σ * τ) ρ * f σ τ)
include hf

lemma f_one_left (ρ : Gal(L/K)) : f 1 ρ = f 1 1 := by
  have h := hf 1 1 ρ
  simp only [AlgEquiv.one_apply, one_mul] at h
  exact Units.ext (mul_left_cancel₀ (f 1 ρ).ne_zero h)

lemma U_mul_U (σ τ : Gal(L/K)) : U f σ * U f τ = mulOp (f σ τ : L) * U f (σ * τ) := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp only [Module.End.mul_apply, U_apply, mulOp_apply, map_mul, mul_inv_rev]
  have e₁ : σ⁻¹ * π = τ * (τ⁻¹ * (σ⁻¹ * π)) := by group
  have e₂ : τ⁻¹ * σ⁻¹ * π = τ⁻¹ * (σ⁻¹ * π) := by group
  rw [e₂]
  conv_lhs => rw [show f σ (σ⁻¹ * π) = f σ (τ * (τ⁻¹ * (σ⁻¹ * π))) by rw [← e₁]]
  have h := hf σ τ (τ⁻¹ * (σ⁻¹ * π))
  rw [AlgEquiv.mul_apply]
  linear_combination (σ (τ (w (τ⁻¹ * (σ⁻¹ * π))))) * h

lemma U_one : U f 1 = mulOp (f 1 1 : L) := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp [f_one_left hf, mul_comm]

omit hf in
lemma U_injective (σ : Gal(L/K)) : Function.Injective (U f σ) := by
  intro w w' h
  funext π
  have := congrFun h (σ * π)
  simp only [U_apply, inv_mul_cancel_left] at this
  exact σ.injective (mul_right_cancel₀ (f σ π).ne_zero this)

omit hf in
lemma mulOp_smul (c : K) (a : L) : mulOp (K := K) (c • a) = c • mulOp a := by
  refine LinearMap.ext fun w ↦ funext fun π ↦ ?_
  simp [Algebra.smul_def, mul_assoc]

variable [FiniteDimensional K L]

variable (f) in
/-- The operator `Φ a = ∑_σ a_σ U_σ` attached to `a : G → L`. -/
noncomputable def Φ : (Gal(L/K) → L) →ₗ[K] Module.End K (W K L) where
  toFun a := ∑ σ, mulOp (a σ) * U f σ
  map_add' a b := by simp [mulOp_add, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [mulOp_smul, Finset.smul_sum]

open Classical in
omit hf in
lemma Φ_single (σ : Gal(L/K)) (b : L) : Φ f (Pi.single σ b) = mulOp b * U f σ := by
  classical
  rw [Φ, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    simp [hτ, mulOp_zero]
  · simp

open Classical in
omit hf in
lemma Φ_eq_sum_single (a : Gal(L/K) → L) :
    Φ f a = ∑ σ, Φ f (Pi.single σ (a σ)) := by
  simp only [Φ_single]
  rfl

open Classical in
lemma Φ_single_mul_Φ_single (σ τ : Gal(L/K)) (a b : L) :
    Φ f (Pi.single σ a) * Φ f (Pi.single τ b) =
      Φ f (Pi.single (σ * τ) (a * σ b * f σ τ)) := by
  rw [Φ_single, Φ_single, Φ_single, mul_assoc, ← mul_assoc (U f σ), U_mul_mulOp, mul_assoc,
    U_mul_U hf, ← mul_assoc, ← mul_assoc, mulOp_mul, mulOp_mul, mul_assoc a]

lemma mem_range_Φ_mul {x y : Module.End K (W K L)} (hx : x ∈ LinearMap.range (Φ f))
    (hy : y ∈ LinearMap.range (Φ f)) : x * y ∈ LinearMap.range (Φ f) := by
  classical
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [Φ_eq_sum_single a, Φ_eq_sum_single b, Finset.sum_mul]
  refine Submodule.sum_mem _ fun σ _ ↦ ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun τ _ ↦ ?_
  rw [Φ_single_mul_Φ_single hf]
  exact ⟨_, rfl⟩

open Classical in
lemma mulOp_eq_Φ (b : L) : mulOp b = Φ f (Pi.single 1 (b * (f 1 1 : L)⁻¹)) := by
  rw [Φ_single, U_one hf, mulOp_mul, inv_mul_cancel_right₀ (f 1 1).ne_zero]

open Classical in
omit hf in
lemma U_eq_Φ (σ : Gal(L/K)) : U f σ = Φ f (Pi.single σ 1) := by
  rw [Φ_single, mulOp_one, one_mul]

variable (f) in
/-- The crossed product algebra `⨁_σ L U_σ ⊆ End_K(W)`. -/
noncomputable def algebra : Subalgebra K (Module.End K (W K L)) :=
  (LinearMap.range (Φ f)).toSubalgebra
    (by classical rw [← mulOp_one, mulOp_eq_Φ hf]; exact ⟨_, rfl⟩) (fun _ _ ↦ mem_range_Φ_mul hf)

lemma mem_algebra_iff (x : Module.End K (W K L)) :
    x ∈ algebra f hf ↔ x ∈ LinearMap.range (Φ f) := Iff.rfl

lemma mulOp_mem (b : L) : mulOp b ∈ algebra f hf := by
  rw [mem_algebra_iff, mulOp_eq_Φ hf]
  exact ⟨_, rfl⟩

lemma U_mem (σ : Gal(L/K)) : U f σ ∈ algebra f hf := by
  rw [mem_algebra_iff, U_eq_Φ]
  exact ⟨_, rfl⟩

open Classical in
omit hf in
lemma Φ_apply_single_one (a : Gal(L/K) → L) (π : Gal(L/K)) :
    Φ f a (Pi.single 1 1) π = a π * f π 1 := by
  classical
  change (∑ σ, mulOp (a σ) * U f σ : Module.End K (W K L)) (Pi.single 1 1) π = _
  rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single π]
  · simp
  · intro σ _ hσ
    have : σ⁻¹ * π ≠ 1 := fun h ↦ hσ (inv_mul_eq_one.mp h)
    simp [this]
  · simp

omit hf in
lemma Φ_injective : Function.Injective (Φ f) := by
  classical
  intro a b h
  funext π
  have := congrFun (congrFun (congrArg DFunLike.coe h) (Pi.single 1 1)) π
  rw [Φ_apply_single_one, Φ_apply_single_one] at this
  exact mul_right_cancel₀ (f π 1).ne_zero this

omit hf in
lemma Φ_mul_mulOp (a : Gal(L/K) → L) (b : L) :
    Φ f a * mulOp b = Φ f (fun σ ↦ a σ * σ b) := by
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [mul_assoc, U_mul_mulOp, ← mul_assoc, mulOp_mul]

omit hf in
lemma mulOp_mul_Φ (a : Gal(L/K) → L) (b : L) :
    mulOp b * Φ f a = Φ f (fun σ ↦ b * a σ) := by
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, ← mul_assoc, mulOp_mul]

lemma nontrivial_algebra : Nontrivial (algebra f hf) := by
  refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
  have := congrArg (fun x : algebra f hf ↦ x.1 (fun _ ↦ 1) 1) h
  simp at this

variable [IsGalois K L]

theorem isCentral_algebra : Algebra.IsCentral K (algebra f hf) := by
  classical
  refine ⟨fun z hz ↦ ?_⟩
  obtain ⟨a, ha⟩ := (mem_algebra_iff hf z.1).1 z.2
  have hcomm (y : algebra f hf) : y.1 * z.1 = z.1 * y.1 :=
    congrArg Subtype.val (Subalgebra.mem_center_iff.1 hz y)
  -- the coefficients of `z` away from `1` vanish
  have h1 (b : L) (σ : Gal(L/K)) : a σ * σ b = b * a σ := by
    have := hcomm ⟨mulOp b, mulOp_mem hf b⟩
    rw [← ha, Φ_mul_mulOp, mulOp_mul_Φ] at this
    exact (congrFun (Φ_injective this) σ).symm
  have h0 (σ : Gal(L/K)) (hσ : σ ≠ 1) : a σ = 0 := by
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
      by_contra! h
      exact hσ (AlgEquiv.ext h)
    have h' : a σ * (σ b - b) = 0 := by rw [mul_sub, h1 b σ, mul_comm, sub_self]
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 hb)
  set c := a 1 * f 1 1 with hc
  have ha1 : z.1 = mulOp c := by
    rw [← ha, Φ_eq_sum_single, Finset.sum_eq_single 1, Φ_single, U_one hf, mulOp_mul]
    · intro σ _ hσ
      rw [h0 σ hσ, Pi.single_zero, map_zero]
    · simp
  -- the remaining coefficient is fixed by the Galois group
  have h2 (τ : Gal(L/K)) : τ c = c := by
    have := hcomm ⟨U f τ, U_mem hf τ⟩
    rw [ha1, U_mul_mulOp, ← Φ_single, ← Φ_single] at this
    simpa using congrFun (Φ_injective this) τ
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) c).2 h2
  refine Algebra.mem_bot.2 ⟨k, Subtype.ext ?_⟩
  rw [ha1, ← hk, mulOp_algebraMap]
  rfl

omit [IsGalois K L] in
theorem isSimpleRing_algebra : IsSimpleRing (algebra f hf) := by
  classical
  have := nontrivial_algebra hf
  refine .of_eq_bot_or_eq_top fun I ↦ ?_
  by_cases hI : I = ⊥
  · exact .inl hI
  refine .inr (I.one_mem_iff.1 ?_)
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
    by_contra! h
    exact hI (eq_bot_iff.2 fun x hx ↦ by simpa [TwoSidedIdeal.mem_bot] using h x hx)
  let supp (a : Gal(L/K) → L) : Finset Gal(L/K) := Finset.univ.filter fun σ ↦ a σ ≠ 0
  let P : ℕ → Prop := fun n ↦ ∃ a : Gal(L/K) → L, ∃ h : Φ f a ∈ algebra f hf,
    (⟨Φ f a, h⟩ : algebra f hf) ∈ I ∧ a ≠ 0 ∧ (supp a).card = n
  have hP : ∃ n, P n := by
    obtain ⟨a, ha⟩ := (mem_algebra_iff hf x.1).1 x.2
    refine ⟨_, a, ha ▸ x.2, by simpa [ha] using hxI, fun h ↦ hx0 (Subtype.ext ?_), rfl⟩
    rw [← ha, h, map_zero]
    rfl
  obtain ⟨a, ha, haI, ha0, hcard⟩ := Nat.find_spec hP
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ, a σ ≠ 0 := by
    by_contra! h
    exact ha0 (funext h)
  -- an element of minimal support has only one nonzero coefficient
  have hsingle (σ₁ : Gal(L/K)) (h₁ : σ₁ ≠ σ₀) : a σ₁ = 0 := by
    by_contra hne
    obtain ⟨b, hb⟩ : ∃ b, σ₁ b ≠ σ₀ b := by
      by_contra! h
      exact h₁ (AlgEquiv.ext h)
    let a' : Gal(L/K) → L := fun σ ↦ a σ * (σ b - σ₀ b)
    have hΦ : Φ f a' = Φ f a * mulOp b - mulOp (σ₀ b) * Φ f a := by
      rw [Φ_mul_mulOp, mulOp_mul_Φ, ← map_sub]
      congr 1
      funext σ
      simp only [a', Pi.sub_apply]
      ring
    have ha' : Φ f a' ∈ algebra f hf := by
      rw [hΦ]
      exact sub_mem (mul_mem ha (mulOp_mem hf b)) (mul_mem (mulOp_mem hf _) ha)
    have ha'I : (⟨Φ f a', ha'⟩ : algebra f hf) ∈ I := by
      have : (⟨Φ f a', ha'⟩ : algebra f hf) =
          ⟨Φ f a, ha⟩ * ⟨mulOp b, mulOp_mem hf b⟩ -
            ⟨mulOp (σ₀ b), mulOp_mem hf _⟩ * ⟨Φ f a, ha⟩ := Subtype.ext hΦ
      rw [this]
      exact I.sub_mem (I.mul_mem_right _ _ haI) (I.mul_mem_left _ _ haI)
    have hsub : supp a' ⊂ supp a := by
      refine Finset.ssubset_iff_of_subset (fun σ hσ ↦ ?_) |>.2 ⟨σ₀, ?_, ?_⟩
      · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        exact left_ne_zero_of_mul hσ
      · simpa [supp] using hσ₀
      · simp [supp, a']
    have ha'0 : a' ≠ 0 := fun h ↦ by
      have := congrFun h σ₁
      simp only [a', Pi.zero_apply, mul_eq_zero, sub_eq_zero] at this
      exact this.elim hne hb
    exact Nat.find_min hP (hcard ▸ Finset.card_lt_card hsub) ⟨a', ha', ha'I, ha'0, rfl⟩
  have hx : Φ f a = mulOp (a σ₀) * U f σ₀ := by
    rw [Φ_eq_sum_single, Finset.sum_eq_single σ₀, Φ_single]
    · intro σ _ hσ
      rw [hsingle σ hσ, Pi.single_zero, map_zero]
    · simp
  -- it has a right inverse
  set e : L := (a σ₀ * f σ₀ σ₀⁻¹ * f 1 1)⁻¹ with he
  have hy : U f σ₀⁻¹ * mulOp e ∈ algebra f hf := mul_mem (U_mem hf _) (mulOp_mem hf _)
  have h1 : (⟨Φ f a, ha⟩ : algebra f hf) * ⟨_, hy⟩ = 1 := by
    refine Subtype.ext ?_
    change Φ f a * (U f σ₀⁻¹ * mulOp e) = 1
    rw [hx, mul_assoc, ← mul_assoc (U f σ₀), U_mul_U hf, mul_inv_cancel, U_one hf, ← mul_assoc,
      ← mul_assoc, mulOp_mul, mulOp_mul, mulOp_mul, he,
      mul_inv_cancel₀ (by simp [hσ₀]), mulOp_one]
  rw [← h1]
  exact I.mul_mem_right _ _ haI

end CrossedProduct

end CrossedProduct

open CrossedProduct in
/-- **Galois `2`-cocycles over a `C₁` field are coboundaries.** Let `L / K` be a finite Galois
extension of a quasi-algebraically closed field `K`, and let `f : G × G → Lˣ` be a `2`-cocycle of
`G = Gal(L/K)`. Then `f(σ, τ) = σ(c(τ)) c(σ) c(στ)⁻¹` for some `c : G → Lˣ`. -/
theorem exists_eq_of_isCocycle {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsQuasiAlgClosed K]
    (f : Gal(L/K) → Gal(L/K) → Lˣ)
    (hf : ∀ σ τ ρ : Gal(L/K), σ (f τ ρ : L) * f σ (τ * ρ) = f (σ * τ) ρ * f σ τ) :
    ∃ c : Gal(L/K) → Lˣ, ∀ σ τ, (f σ τ : L) = σ (c τ : L) * c σ * (c (σ * τ) : L)⁻¹ := by
  classical
  let A := algebra f hf
  have := isCentral_algebra hf
  have := isSimpleRing_algebra hf
  obtain ⟨m, hm, ⟨φ⟩⟩ := exists_algEquiv_matrix K A
  set n := finrank K L with hn
  have hcard : Fintype.card Gal(L/K) = n :=
    Nat.card_eq_fintype_card.symm.trans (IsGalois.card_aut_eq_finrank K L)
  have hn0 : 0 < n := finrank_pos
  -- `A` has dimension `n²`, so `m = n`
  have hmn : m = n := by
    have h1 : finrank K A = m * m := by
      rw [φ.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin,
        Module.finrank_self, mul_one]
    have h2 : finrank K A = n * n := by
      change finrank K (LinearMap.range (Φ f)) = _
      rw [LinearMap.finrank_range_of_inj Φ_injective, Module.finrank_pi_fintype,
        Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
    exact Nat.mul_self_inj.1 (h1.symm.trans h2)
  -- the matrix units of `A`
  let E (i j : Fin m) : A := φ.symm (Matrix.single i j 1)
  have hE (i j k : Fin m) : E i j * E j k = E i k := by
    simp only [E, ← map_mul, Matrix.single_mul_single_same, mul_one]
  have hEsum : ∑ i, E i i = 1 := by
    have : ∑ i, Matrix.single i i (1 : K) = (1 : Matrix (Fin m) (Fin m) K) := by
      ext a b
      by_cases h : a = b
      · subst h
        simp [Matrix.sum_apply, Matrix.single_apply]
      · rw [Matrix.one_apply_ne h, Matrix.sum_apply]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        rw [Matrix.single_apply, ite_eq_right]
        rintro ⟨rfl, rfl⟩
        exact h rfl
    simp only [E, ← map_sum, this, map_one]
  let i₀ : Fin m := ⟨0, Nat.pos_of_neZero m⟩
  -- some vector is not killed by `E i₀ i₀`
  obtain ⟨w₀, hw₀⟩ : ∃ w : W K L, (E i₀ i₀).1 w ≠ 0 := by
    by_contra! h
    have hw (w : W K L) : w = 0 := by
      have : w = (∑ i, E i i₀ * E i₀ i₀ * E i₀ i).1 w := by
        simp only [hE, hEsum]
        rfl
      rw [this, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      change (E i i₀).1 ((E i₀ i₀).1 ((E i₀ i).1 w)) = 0
      rw [h, map_zero]
    exact one_ne_zero (congrFun (hw fun _ ↦ 1) 1)
  -- the `A`-submodule `S = A E w₀` of `W`, an `L`-subspace
  let S : Submodule L (W K L) :=
    { carrier := {w | ∃ x : A, (x * E i₀ i₀).1 w₀ = w}
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by rw [add_mul]; rfl⟩
      zero_mem' := ⟨0, by rw [zero_mul]; rfl⟩
      smul_mem' := by
        rintro b _ ⟨x, rfl⟩
        exact ⟨⟨_, mulOp_mem hf b⟩ * x, by rw [mul_assoc]; rfl⟩ }
  have hSA (y : A) {w : W K L} (hw : w ∈ S) : y.1 w ∈ S := by
    obtain ⟨x, rfl⟩ := hw
    exact ⟨y * x, by rw [mul_assoc]; rfl⟩
  set v := (E i₀ i₀).1 w₀ with hv
  have hvS : v ∈ S := ⟨1, by rw [one_mul]⟩
  -- `S` has `K`-dimension at most `n`
  have hle : finrank K (S.restrictScalars K) ≤ n := by
    have hsub : S.restrictScalars K ≤ Submodule.span K (Set.range fun i ↦ (E i i₀).1 w₀) := by
      rintro _ ⟨x, rfl⟩
      have hx : x * E i₀ i₀ = ∑ i, φ x i i₀ • E i i₀ := by
        apply φ.injective
        rw [map_mul, map_sum]
        simp only [E, map_smul, AlgEquiv.apply_symm_apply]
        ext a b
        by_cases hb : i₀ = b
        · simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply, hb]
        · simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply, hb]
      rw [hx, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [Subalgebra.coe_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine (Submodule.finrank_mono hsub).trans ?_
    exact (finrank_range_le_card _).trans (by rw [Fintype.card_fin, hmn])
  -- hence `S` is an `L`-line
  have hS1 : finrank L S = 1 := by
    have htower := Module.finrank_mul_finrank K L S
    have hpos : 0 < finrank L S :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hvS⟩, by simpa using hw₀⟩
    have : finrank K S ≤ n := hle
    rw [← htower, ← hn] at this
    nlinarith
  have hv0 : (⟨v, hvS⟩ : S) ≠ 0 := by simpa using hw₀
  have hline := (finrank_eq_one_iff_of_nonzero' _ hv0).1 hS1
  -- the operators `U σ` act on `v` by scalars `c σ`
  choose c hc using fun σ ↦ hline ⟨(U f σ) v, hSA ⟨U f σ, U_mem hf σ⟩ hvS⟩
  have hc' (σ : Gal(L/K)) : c σ • v = U f σ v := congrArg Subtype.val (hc σ)
  have hc0 (σ : Gal(L/K)) : c σ ≠ 0 := by
    intro h
    have := hc' σ
    rw [h, zero_smul, ← map_zero (U f σ)] at this
    exact hw₀ (U_injective σ this).symm
  refine ⟨fun σ ↦ Units.mk0 (c σ) (hc0 σ), fun σ τ ↦ ?_⟩
  simp only [Units.val_mk0]
  have h1 : U f σ (U f τ v) = (σ (c τ) * c σ) • v := by
    rw [← hc' τ, mul_smul, hc' σ]
    exact LinearMap.congr_fun (U_mul_mulOp f σ (c τ)) v
  have h2 : U f σ (U f τ v) = (f σ τ * c (σ * τ) : L) • v := by
    rw [mul_smul, hc']
    exact LinearMap.congr_fun (U_mul_U hf σ τ) v
  have h3 := smul_left_injective L (show v ≠ 0 from hw₀) (h2.symm.trans h1)
  field_simp [hc0 (σ * τ)]
  exact h3

/-- **Homogeneous Galois `2`-cocycles over a `C₁` field are coboundaries.** Let `L / K` be a
finite Galois extension of a quasi-algebraically closed field `K` with group `G`, and let
`F : G³ → Lˣ` be a homogeneous `2`-cocycle: `F (h a) (h b) (h c) = h (F a b c)` and
`F b c d · F a c d⁻¹ · F a b d · F a b c⁻¹ = 1`. Then `F a b c = E b c · E a c⁻¹ · E a b` for
an equivariant `E : G² → Lˣ`. -/
theorem exists_eq_of_isHomogeneousCocycle {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsQuasiAlgClosed K]
    (F : Gal(L/K) → Gal(L/K) → Gal(L/K) → Lˣ)
    (hF : ∀ h a b c, F (h * a) (h * b) (h * c) = Units.map h.toAlgHom.toMonoidHom (F a b c))
    (hc : ∀ a b c d, F b c d * (F a c d)⁻¹ * F a b d * (F a b c)⁻¹ = 1) :
    ∃ E : Gal(L/K) → Gal(L/K) → Lˣ,
      (∀ h a b, E (h * a) (h * b) = Units.map h.toAlgHom.toMonoidHom (E a b)) ∧
      ∀ a b c, F a b c = E b c * (E a c)⁻¹ * E a b := by
  have hmap (h : Gal(L/K)) (u : Lˣ) :
      ((Units.map h.toAlgHom.toMonoidHom u : Lˣ) : L) = h (u : L) := rfl
  -- the inhomogeneous cocycle `f σ τ = F 1 σ (σ τ)`
  let f : Gal(L/K) → Gal(L/K) → Lˣ := fun σ τ ↦ F 1 σ (σ * τ)
  have hF1 (a b c : Gal(L/K)) :
      F a b c = Units.map a.toAlgHom.toMonoidHom (F 1 (a⁻¹ * b) (a⁻¹ * c)) := by
    rw [← hF, mul_one, mul_inv_cancel_left, mul_inv_cancel_left]
  have hf : ∀ σ τ ρ : Gal(L/K), σ (f τ ρ : L) * f σ (τ * ρ) = f (σ * τ) ρ * f σ τ := by
    intro σ τ ρ
    have h := hc 1 σ (σ * τ) (σ * τ * ρ)
    rw [hF1 σ (σ * τ) (σ * τ * ρ), inv_mul_cancel_left,
      show σ⁻¹ * (σ * τ * ρ) = τ * ρ by group] at h
    rw [mul_assoc σ τ ρ] at h
    have h' := congrArg (fun u : Lˣ ↦ (u : L)) h
    simp only [Units.val_mul, hmap, Units.val_inv_eq_inv_val, Units.val_one] at h'
    simp only [f]
    rw [mul_assoc σ τ ρ]
    have h1 := (F 1 (σ * τ) (σ * (τ * ρ))).ne_zero
    have h2 := (F 1 σ (σ * τ)).ne_zero
    field_simp at h'
    linear_combination h'
  obtain ⟨c, hc'⟩ := exists_eq_of_isCocycle f hf
  refine ⟨fun a b ↦ Units.map a.toAlgHom.toMonoidHom (c (a⁻¹ * b)), fun h a b ↦ ?_,
    fun a b c' ↦ ?_⟩
  · ext
    simp [mul_inv_rev, mul_assoc]
  · obtain ⟨σ, rfl⟩ : ∃ σ, b = a * σ := ⟨a⁻¹ * b, by group⟩
    obtain ⟨τ, rfl⟩ : ∃ τ, c' = a * σ * τ := ⟨(a * σ)⁻¹ * c', by group⟩
    beta_reduce
    rw [hF1, show a⁻¹ * (a * σ) = σ by group, show a⁻¹ * (a * σ * τ) = σ * τ by group,
      show (a * σ)⁻¹ * (a * σ * τ) = τ by group]
    ext
    simp only [f] at hc'
    simp only [Units.val_mul, hmap, Units.val_inv_eq_inv_val, hc', map_mul, map_inv₀,
      AlgEquiv.mul_apply]
    ring

end IsQuasiAlgClosed
