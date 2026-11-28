import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Unit eigenvectors of a cyclic automorphism over a ring with trivial Picard group

Let `B` be a faithful algebra over a commutative ring `A`, let `ℓ` be a positive integer, and
let `σ` be an `A`-algebra endomorphism of `B` with `σ^ℓ = 1` whose fixed points are exactly the
image of `A`. Suppose that over every maximal ideal of `A` there is a ring map `φ` from `B`
to a field killing the image of the ideal, with `φ ∘ σ^j ≠ φ` for `0 < j < ℓ`. If the Picard
group of `A` is trivial, then for each `c ∈ A`
with `c^ℓ = 1` there is a unit `v` of `B` with `σ v = c v`, and `v^ℓ` is the image of a unit
of `A`.

The eigenspaces `E(d) = {b | d σ(b) = b}` multiply into each other. Under `σ^ℓ = 1`, the
Lagrange resolvent `∑_{j<ℓ} d^j σ^j(b)` lies in `E(d)` when `d^ℓ = 1`. For each `d ∈ A`,
Dedekind's independence of characters gives, at each of the given field points, a resolvent
whose value there is nonzero. The product of the eigenspaces for `c^{ℓ-1}` and `c` is
therefore the image of `A` in `B`, so the first eigenspace is an invertible `A`-submodule
of `B`. Since the Picard group is trivial, Mathlib's exact sequence
`Submodule.ker_unitsToPic` makes it the span of a unit of `B`.
-/

noncomputable section

universe u

open Submodule

namespace Langlands.CommutativeAlgebra.KummerEigenvector

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (σ : B →ₐ[A] B)

/-- The eigenspace `{b | d σ(b) = b}`, an `A`-submodule of `B`. -/
def eigenspace (d : A) : Submodule A B where
  carrier := {b | algebraMap A B d * σ b = b}
  add_mem' {b b'} hb hb' := by
    simp only [Set.mem_ofPred_eq, map_add, mul_add] at hb hb' ⊢
    rw [hb, hb']
  zero_mem' := by simp
  smul_mem' a b hb := by
    simp only [Set.mem_ofPred_eq, map_smul] at hb ⊢
    rw [mul_smul_comm, hb]

theorem mem_eigenspace_iff (d : A) (b : B) :
    b ∈ eigenspace σ d ↔ algebraMap A B d * σ b = b := Iff.rfl

theorem eigenspace_mul_le (d d' : A) :
    eigenspace σ d * eigenspace σ d' ≤ eigenspace σ (d * d') := by
  rw [Submodule.mul_le]
  intro b hb b' hb'
  rw [mem_eigenspace_iff] at hb hb' ⊢
  rw [map_mul, map_mul]
  calc algebraMap A B d * algebraMap A B d' * (σ b * σ b') =
      (algebraMap A B d * σ b) * (algebraMap A B d' * σ b') := by ring
    _ = b * b' := by rw [hb, hb']

theorem eigenspace_one_le (hfix : ∀ b, σ b = b → ∃ a, algebraMap A B a = b) :
    eigenspace σ 1 ≤ 1 := by
  intro b hb
  rw [mem_eigenspace_iff, map_one, one_mul] at hb
  obtain ⟨a, ha⟩ := hfix b hb
  exact mem_one.mpr ⟨a, ha⟩

/-- The Lagrange resolvent `∑_{j<ℓ} d^j σ^j(b)`. -/
def resolvent (ℓ : ℕ) (d : A) (b : B) : B :=
  ∑ j ∈ Finset.range ℓ, algebraMap A B d ^ j * (σ ^ j) b

theorem resolvent_mem {ℓ : ℕ} (hσℓ : σ ^ ℓ = 1) {d : A} (hd : d ^ ℓ = 1) (b : B) :
    resolvent σ ℓ d b ∈ eigenspace σ d := by
  rw [mem_eigenspace_iff]
  cases ℓ with
  | zero => simp [resolvent]
  | succ n =>
    have hstep (j : ℕ) : σ ((σ ^ j) b) = (σ ^ (j + 1)) b := by
      rw [pow_succ', AlgHom.mul_apply]
    simp only [resolvent, map_sum, map_mul, map_pow, AlgHom.commutes, Finset.mul_sum, hstep]
    rw [Finset.sum_range_succ, Finset.sum_range_succ' _ n, hσℓ, AlgHom.one_apply]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [← mul_assoc, ← pow_succ', ← map_pow, hd, map_one, pow_zero, pow_zero, one_mul,
        AlgHom.one_apply, one_mul]

/-- **Dedekind independence for resolvents.** If `0 < ℓ` and the ring maps `φ ∘ σ^j`, `j < ℓ`,
are pairwise distinct, then for each `d` some resolvent has nonzero image under `φ`. -/
theorem exists_resolvent_ne_zero {K : Type*} [Field K] (φ : B →+* K) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hφ : ∀ i j, i < ℓ → j < ℓ → φ.comp (σ ^ i).toRingHom = φ.comp (σ ^ j).toRingHom → i = j)
    (d : A) : ∃ b, φ (resolvent σ ℓ d b) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let χ : Fin ℓ → (B →* K) := fun j => (φ.comp (σ ^ (j : ℕ)).toRingHom).toMonoidHom
  have hχ : Function.Injective χ := by
    intro i j hij
    apply Fin.ext
    apply hφ i j i.2 j.2
    ext b
    exact DFunLike.congr_fun hij b
  have hli := (linearIndependent_monoidHom B K).comp χ hχ
  have hsum : ∑ j : Fin ℓ, (φ (algebraMap A B d) ^ (j : ℕ)) • ((χ j : B →* K) : B → K) = 0 := by
    funext b
    have h := hcon b
    simp only [resolvent, map_sum, map_mul, map_pow] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h, ← Fin.sum_univ_eq_sum_range (fun j => φ (algebraMap A B d) ^ j * φ ((σ ^ j) b))]
    rfl
  have h0 := Fintype.linearIndependent_iff.mp hli _ hsum ⟨0, hℓ⟩
  simp at h0

/-- **Unit eigenvectors.** Under the hypotheses described in the module docstring (including
`0 < ℓ` and `σ^ℓ = 1`), for every `c ∈ A` with `c^ℓ = 1` there is a unit `v` of `B` with
`σ v = c v` whose `ℓ`-th power is the image of a unit of `A`. -/
theorem exists_unit_eigenvector [FaithfulSMul A B] [Subsingleton (CommRing.Pic A)] {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hσℓ : σ ^ ℓ = 1) (hfix : ∀ b, σ b = b → ∃ a, algebraMap A B a = b)
    (hpts : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ (K : Type u) (_ : Field K) (φ : B →+* K),
      (∀ a ∈ 𝔪, φ (algebraMap A B a) = 0) ∧
        ∀ j, 0 < j → j < ℓ → φ.comp (σ ^ j).toRingHom ≠ φ)
    {c : A} (hc : c ^ ℓ = 1) :
    ∃ v : Bˣ, σ v = algebraMap A B c * v ∧ ∃ w : Aˣ, (v : B) ^ ℓ = algebraMap A B w := by
  classical
  set e := c ^ (ℓ - 1) with he_def
  have hce : c * e = 1 := by rw [he_def, ← pow_succ', Nat.sub_add_cancel hℓ, hc]
  have he : e ^ ℓ = 1 := by rw [he_def, ← pow_mul, mul_comm, pow_mul, hc, one_pow]
  -- pairwise distinctness of the characters `φ ∘ σ^j`
  have hpair : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ (K : Type u) (_ : Field K) (φ : B →+* K),
      (∀ a ∈ 𝔪, φ (algebraMap A B a) = 0) ∧
        ∀ i j, i < ℓ → j < ℓ → φ.comp (σ ^ i).toRingHom = φ.comp (σ ^ j).toRingHom → i = j := by
    intro 𝔪 h𝔪
    obtain ⟨K, _, φ, hφ𝔪, hφ⟩ := hpts 𝔪 h𝔪
    refine ⟨K, inferInstance, φ, hφ𝔪, ?_⟩
    have key : ∀ i j, i < j → j < ℓ →
        φ.comp (σ ^ i).toRingHom = φ.comp (σ ^ j).toRingHom → False := by
      intro i j hij hjℓ h
      apply hφ (j - i) (Nat.sub_pos_of_lt hij) (lt_of_le_of_lt (Nat.sub_le j i) hjℓ)
      have h2 : ∀ b, φ ((σ ^ i) ((σ ^ (ℓ - i)) b)) = φ ((σ ^ j) ((σ ^ (ℓ - i)) b)) :=
        fun b => DFunLike.congr_fun h _
      ext b
      have h3 := h2 b
      rw [← AlgHom.mul_apply, ← AlgHom.mul_apply, ← pow_add, ← pow_add,
        Nat.add_sub_cancel' (le_of_lt (lt_trans hij hjℓ)), hσℓ, AlgHom.one_apply] at h3
      have h4 : j + (ℓ - i) = ℓ + (j - i) := by omega
      rw [h4, pow_add, hσℓ, one_mul] at h3
      exact h3.symm
    intro i j hi hj h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (key i j hij hj h).elim
    · exact hij
    · exact (key j i hij hi h.symm).elim
  set E₁ := eigenspace σ e
  set E₂ := eigenspace σ c
  have hle : E₁ * E₂ ≤ 1 := by
    refine (eigenspace_mul_le σ e c).trans ?_
    rw [mul_comm e c, hce]
    exact eigenspace_one_le σ hfix
  have hone : (1 : B) ∈ E₁ * E₂ := by
    by_contra hnot
    let J : Ideal A := (E₁ * E₂).comap (Algebra.linearMap A B)
    have hJ : J ≠ ⊤ := by
      intro h
      apply hnot
      have h1 : (1 : A) ∈ J := (Ideal.eq_top_iff_one J).mp h
      simpa [J] using h1
    obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal J hJ
    obtain ⟨K, _, φ, hφ𝔪, hφσ⟩ := hpair 𝔪 h𝔪
    obtain ⟨b₁, hb₁⟩ := exists_resolvent_ne_zero σ φ hℓ hφσ e
    obtain ⟨b₂, hb₂⟩ := exists_resolvent_ne_zero σ φ hℓ hφσ c
    have hmem : resolvent σ ℓ e b₁ * resolvent σ ℓ c b₂ ∈ E₁ * E₂ :=
      mul_mem_mul (resolvent_mem σ hσℓ he b₁) (resolvent_mem σ hσℓ hc b₂)
    obtain ⟨a, ha⟩ := mem_one.mp (hle hmem)
    have haJ : a ∈ J := by
      change Algebra.linearMap A B a ∈ E₁ * E₂
      rw [Algebra.linearMap_apply, ha]
      exact hmem
    have h0 := hφ𝔪 a (hJ𝔪 haJ)
    rw [ha, map_mul] at h0
    exact mul_ne_zero hb₁ hb₂ h0
  have hprod : E₁ * E₂ = 1 := le_antisymm hle (one_le.mpr hone)
  let U : (Submodule A B)ˣ := ⟨E₁, E₂, hprod, by rw [mul_comm]; exact hprod⟩
  have hU : U ∈ (unitsToPic A B).ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [ker_unitsToPic] at hU
  obtain ⟨v, hv⟩ := hU
  have hspan : Submodule.span A {(v : B)} = E₁ := by
    have := congrArg Units.val hv
    simpa [U] using this
  have hvE : (v : B) ∈ E₁ := by
    rw [← hspan]
    exact Submodule.subset_span rfl
  have hσv : σ v = algebraMap A B c * v := by
    rw [mem_eigenspace_iff] at hvE
    calc σ v = algebraMap A B (c * e) * σ v := by rw [hce, map_one, one_mul]
      _ = algebraMap A B c * (algebraMap A B e * σ v) := by rw [map_mul, mul_assoc]
      _ = algebraMap A B c * v := by rw [hvE]
  refine ⟨v, hσv, ?_⟩
  have hσpow : σ ((v : B) ^ ℓ) = (v : B) ^ ℓ := by
    rw [map_pow, hσv, mul_pow, ← map_pow, hc, map_one, one_mul]
  have hσinv : σ (((v⁻¹ : Bˣ) : B) ^ ℓ) = ((v⁻¹ : Bˣ) : B) ^ ℓ := by
    have h1 : σ ((v : B) ^ ℓ) * σ (((v⁻¹ : Bˣ) : B) ^ ℓ) = 1 := by
      rw [← map_mul, ← mul_pow, Units.mul_inv, one_pow, map_one]
    rw [hσpow] at h1
    calc σ (((v⁻¹ : Bˣ) : B) ^ ℓ) =
        (((v⁻¹ : Bˣ) : B) ^ ℓ * (v : B) ^ ℓ) * σ (((v⁻¹ : Bˣ) : B) ^ ℓ) := by
          rw [← mul_pow, Units.inv_mul, one_pow, one_mul]
      _ = ((v⁻¹ : Bˣ) : B) ^ ℓ * ((v : B) ^ ℓ * σ (((v⁻¹ : Bˣ) : B) ^ ℓ)) := by ring
      _ = ((v⁻¹ : Bˣ) : B) ^ ℓ := by rw [h1, mul_one]
  obtain ⟨w₀, hw₀⟩ := hfix _ hσpow
  obtain ⟨w₁, hw₁⟩ := hfix _ hσinv
  have hinj := FaithfulSMul.algebraMap_injective A B
  have hw : w₀ * w₁ = 1 := by
    apply hinj
    rw [map_mul, hw₀, hw₁, ← mul_pow, Units.mul_inv, one_pow, map_one]
  exact ⟨⟨w₀, w₁, hw, by rw [mul_comm]; exact hw⟩, hw₀.symm⟩

end Langlands.CommutativeAlgebra.KummerEigenvector
