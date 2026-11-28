import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Trace

/-!
# The trace form of a semisimple algebra and the decomposition `A = z ⊕ z^⊥`

Let `A` be a finite-dimensional algebra over a field `F`. This module studies the trace form
`B₀(X, Y) = tr_{A/F}(L_{XY})`, `L` the left regular representation (`traceFormPairing`):

* it is symmetric (`traceFormPairing_comm`) and invariant under conjugation by units
  (`traceFormPairing_conj`);
* a semisimple ring is von Neumann regular: every `X` has a `Y` with `X Y X = X`
  (`exists_mul_mul_eq_self`); hence a nilpotent element commuting with everything is `0`
  (`eq_zero_of_isNilpotent_of_commute`);
* for `A` semisimple and `F` of characteristic zero, `B₀` is nondegenerate, so it is an
  invariant pairing (`isInvariantPairing_traceFormPairing`). For `X ≠ 0`, choose `Y` with
  `X Y X = X`. Then `X Y` is a nonzero idempotent, so left multiplication by `X Y` is a
  projection whose trace equals its positive rank.
* the center `z` of `A` meets its `B₀`-orthogonal `z^⊥` only in `0`, so `A = z ⊕ z^⊥`
  (`isCompl_center_centerOrthogonal`): for `Z ∈ z` the descending chain `Z^k z` stabilizes,
  which gives a central `W` with `Z = Z² W`, and `Z W` is an idempotent with `B₀(Z, W) ≠ 0`
  when `Z ≠ 0`;
* `z^⊥` is stable under conjugation (`conj_mem_centerOrthogonal`) and contains every nilpotent
  element (`mem_centerOrthogonal_of_isNilpotent`), since `L_{ZN}` is nilpotent for central `Z`;
* the centralizer of a nilpotent element is strictly larger than `z` when `A` is not
  commutative (`finrank_center_lt_finrank_centralizer`).

The decomposition `g = z ⊕ [g, g]` of a reductive Lie algebra into its center and its derived
algebra is used by Harish-Chandra, *Admissible invariant distributions on reductive p-adic
groups* (notes by DeBacker and Sally, 1999), §3.4, Lemma 3.11, printed p. 26; for the trace
form `[A, A] ⊆ z^⊥`.
-/

noncomputable section

open Module

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe u v

section TraceForm

variable (F : Type u) [Field F] (A : Type v) [Ring A] [Algebra F A]

/-- The trace form `B₀(X, Y) = tr_{A/F}(L_{XY})` of `A`, `L` the left regular representation. -/
def traceFormPairing : LinearMap.BilinForm F A :=
  (LinearMap.mul F A).compr₂ ((LinearMap.trace F A).comp (Algebra.lmul F A).toLinearMap)

variable {F A}

theorem traceFormPairing_apply (X Y : A) :
    traceFormPairing F A X Y = LinearMap.trace F A (Algebra.lmul F A (X * Y)) := rfl

theorem traceFormPairing_apply_eq_trace_mul (X Y : A) :
    traceFormPairing F A X Y =
      LinearMap.trace F A (Algebra.lmul F A X * Algebra.lmul F A Y) := by
  rw [traceFormPairing_apply, map_mul]

theorem traceFormPairing_comm (X Y : A) :
    traceFormPairing F A X Y = traceFormPairing F A Y X := by
  rw [traceFormPairing_apply_eq_trace_mul, traceFormPairing_apply_eq_trace_mul,
    LinearMap.trace_mul_comm]

theorem traceFormPairing_isSymm : (traceFormPairing F A).IsSymm :=
  ⟨traceFormPairing_comm⟩

/-- The trace of `L_{u W u⁻¹}` is that of `L_W`. -/
theorem trace_lmul_conj (u : Aˣ) (W : A) :
    LinearMap.trace F A (Algebra.lmul F A ((u : A) * W * ((u⁻¹ : Aˣ) : A))) =
      LinearMap.trace F A (Algebra.lmul F A W) := by
  rw [show Algebra.lmul F A ((u : A) * W * ((u⁻¹ : Aˣ) : A)) =
      Algebra.lmul F A (u : A) * (Algebra.lmul F A W * Algebra.lmul F A ((u⁻¹ : Aˣ) : A)) by
    rw [← map_mul, ← map_mul, mul_assoc], LinearMap.trace_mul_comm, mul_assoc, ← map_mul,
    ← map_mul, Units.inv_mul, mul_one]

theorem traceFormPairing_conj (u : Aˣ) (X Y : A) :
    traceFormPairing F A ((u : A) * X * ((u⁻¹ : Aˣ) : A)) ((u : A) * Y * ((u⁻¹ : Aˣ) : A)) =
      traceFormPairing F A X Y := by
  rw [traceFormPairing_apply, traceFormPairing_apply]
  have : (u : A) * X * ((u⁻¹ : Aˣ) : A) * ((u : A) * Y * ((u⁻¹ : Aˣ) : A)) =
      (u : A) * (X * Y) * ((u⁻¹ : Aˣ) : A) := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [this, trace_lmul_conj]

end TraceForm

section Regular

variable {A : Type v} [Ring A] [IsSemisimpleRing A]

/-- A semisimple ring is von Neumann regular: every `X` has a `Y` with `X Y X = X`. The left
ideal `A X` has a complement; the projection onto it is right multiplication by an element
`e = Y X` of `A X`, and it fixes `X`. -/
theorem exists_mul_mul_eq_self (X : A) : ∃ Y : A, X * Y * X = X := by
  obtain ⟨L, hL⟩ := exists_isCompl (Submodule.span A ({X} : Set A))
  let p := Submodule.projectionOnto _ L hL
  obtain ⟨Y, hY⟩ := Submodule.mem_span_singleton.1 (p 1).2
  refine ⟨Y, ?_⟩
  have hX : (p X : A) = X := by
    exact congrArg Subtype.val
      (Submodule.projectionOnto_apply_left hL ⟨X, Submodule.mem_span_singleton_self X⟩)
  have h1 : p X = X • p 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have h2 : (p X : A) = X * (p 1 : A) := by
    rw [h1, Submodule.coe_smul, smul_eq_mul]
  rw [← hY, smul_eq_mul] at h2
  rw [mul_assoc, ← h2, hX]

/-- A nilpotent element of the center of a semisimple ring is `0`. -/
theorem eq_zero_of_isNilpotent_of_commute {N : A} (hN : IsNilpotent N)
    (hc : ∀ Y : A, Y * N = N * Y) : N = 0 := by
  obtain ⟨Y, hY⟩ := exists_mul_mul_eq_self N
  have key : ∀ k : ℕ, N = N ^ (k + 1) * Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc N = N * Y * N := hY.symm
        _ = N ^ 2 * Y := by rw [mul_assoc, hc Y, ← mul_assoc, sq]
        _ = N * (N ^ (k + 1) * Y ^ k) * Y := by rw [← ih, sq]
        _ = N ^ (k + 1 + 1) * Y ^ (k + 1) := by
          rw [pow_succ' N (k + 1), pow_succ Y k, mul_assoc, mul_assoc, mul_assoc]
  obtain ⟨n, hn⟩ := hN
  rcases n with _ | n
  · rw [pow_zero] at hn
    have : (1 : A) = 0 := hn
    calc N = 1 * N := (one_mul N).symm
      _ = 0 := by rw [this, zero_mul]
  · rw [key n, hn, zero_mul]

end Regular

section Nondegenerate

variable {F : Type u} [Field F] [CharZero F] {A : Type v} [Ring A] [Algebra F A]
  [FiniteDimensional F A]

/-- The trace of left multiplication by a nonzero idempotent is nonzero in characteristic
zero: it is the rank of the projection. -/
theorem trace_lmul_ne_zero_of_mul_self {e : A} (he : e * e = e) (h0 : e ≠ 0) :
    LinearMap.trace F A (Algebra.lmul F A e) ≠ 0 := by
  intro h
  have hidem : IsIdempotentElem (Algebra.lmul F A e) := by
    rw [IsIdempotentElem, ← map_mul, he]
  have h1 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem h
  apply h0
  have h2 := congrArg (fun φ : A →ₗ[F] A => φ 1) h1
  simpa using h2

variable [IsSemisimpleRing A]

theorem traceFormPairing_separatingLeft (X : A) (hX : ∀ Y, traceFormPairing F A X Y = 0) :
    X = 0 := by
  by_contra hne
  obtain ⟨Y, hY⟩ := exists_mul_mul_eq_self X
  have he : X * Y * (X * Y) = X * Y := by rw [← mul_assoc, hY]
  have h0 : X * Y ≠ 0 := by
    intro h
    apply hne
    rw [← hY, h, zero_mul]
  exact trace_lmul_ne_zero_of_mul_self he h0 (hX Y)

/-- The trace form of a semisimple algebra over a field of characteristic zero is
nondegenerate. -/
theorem traceFormPairing_nondegenerate : (traceFormPairing F A).Nondegenerate :=
  ⟨traceFormPairing_separatingLeft, fun Y hY =>
    traceFormPairing_separatingLeft (F := F) Y fun X => by
      rw [traceFormPairing_comm]; exact hY X⟩

/-- The trace form of a semisimple algebra over a field of characteristic zero is an invariant
pairing. -/
theorem isInvariantPairing_traceFormPairing : IsInvariantPairing (traceFormPairing F A) :=
  ⟨traceFormPairing_isSymm, traceFormPairing_nondegenerate, traceFormPairing_conj⟩

end Nondegenerate

section Center

variable (F : Type u) [Field F] (A : Type v) [Ring A] [Algebra F A]

/-- The `B₀`-orthogonal `z^⊥` of the center `z` of `A`, for the trace form `B₀`. -/
def centerOrthogonal : Submodule F A :=
  (traceFormPairing F A).orthogonal (Subalgebra.center F A).toSubmodule

variable {F A}

theorem mem_centerOrthogonal_iff (Y : A) :
    Y ∈ centerOrthogonal F A ↔ ∀ Z ∈ Subalgebra.center F A, traceFormPairing F A Z Y = 0 :=
  Iff.rfl

/-- `z^⊥` is stable under conjugation. -/
theorem conj_mem_centerOrthogonal (u : Aˣ) {Y : A} (hY : Y ∈ centerOrthogonal F A) :
    (u : A) * Y * ((u⁻¹ : Aˣ) : A) ∈ centerOrthogonal F A := by
  intro Z hZ
  have hZ' : (u : A) * Z * ((u⁻¹ : Aˣ) : A) = Z := by
    rw [(Subalgebra.mem_center_iff (R := F)).1 hZ (u : A), mul_assoc, Units.mul_inv, mul_one]
  change traceFormPairing F A Z ((u : A) * Y * ((u⁻¹ : Aˣ) : A)) = 0
  rw [← hZ', traceFormPairing_conj]
  exact hY Z hZ

/-- Every nilpotent element lies in `z^⊥`: for central `Z`, `L_{ZN}` is nilpotent. -/
theorem mem_centerOrthogonal_of_isNilpotent [FiniteDimensional F A] {N : A}
    (hN : IsNilpotent N) : N ∈ centerOrthogonal F A := by
  intro Z hZ
  change traceFormPairing F A Z N = 0
  have hc : Commute Z N := ((Subalgebra.mem_center_iff (R := F)).1 hZ N).symm
  have hZN : IsNilpotent (Z * N) := hc.isNilpotent_mul_left hN
  have h := LinearMap.isNilpotent_trace_of_isNilpotent (hZN.map (Algebra.lmul F A))
  exact h.eq_zero

variable [IsSemisimpleRing A]

/-- A central element `Z` of a finite-dimensional semisimple algebra has a central `W` with
`Z = Z Z W`: the chain `Z^k z` stabilizes, and `Z (1 - Z W)` is central and nilpotent. -/
theorem exists_center_mul_mul_eq [FiniteDimensional F A] {Z : A}
    (hZ : Z ∈ Subalgebra.center F A) :
    ∃ W ∈ Subalgebra.center F A, Z = Z * Z * W := by
  let I : ℕ → Submodule F A := fun k =>
    (Subalgebra.center F A).toSubmodule.map (LinearMap.mulLeft F (Z ^ k))
  have hle : ∀ k, I (k + 1) ≤ I k := by
    rintro k _ ⟨W, hW, rfl⟩
    refine ⟨Z * W, Subalgebra.mul_mem _ hZ hW, ?_⟩
    simp only [LinearMap.mulLeft_apply, pow_succ, mul_assoc]
  have hstab : ∃ k, Module.finrank F (I (k + 1)) = Module.finrank F (I k) := by
    by_contra hcon
    push Not at hcon
    have hlt : ∀ k, Module.finrank F (I (k + 1)) < Module.finrank F (I k) := fun k =>
      lt_of_le_of_ne (Submodule.finrank_mono (hle k)) (hcon k)
    have hbound : ∀ k, Module.finrank F (I k) + k ≤ Module.finrank F (I 0) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => have := hlt k; omega
    have := hbound (Module.finrank F (I 0) + 1)
    omega
  obtain ⟨k, hk⟩ := hstab
  have heq : I (k + 1) = I k := Submodule.eq_of_le_of_finrank_eq (hle k) hk
  have hmem : Z ^ k ∈ I (k + 1) := by
    rw [heq]
    exact ⟨1, Subalgebra.one_mem _, by simp⟩
  obtain ⟨W, hW, hWe⟩ := hmem
  simp only [LinearMap.mulLeft_apply] at hWe
  refine ⟨W, hW, ?_⟩
  have hWc : ∀ Y : A, Y * W = W * Y := fun Y => (Subalgebra.mem_center_iff (R := F)).1 hW Y
  have hZc : ∀ Y : A, Y * Z = Z * Y := fun Y => (Subalgebra.mem_center_iff (R := F)).1 hZ Y
  have hPZ : Z - Z * Z * W = Z * (1 - Z * W) := by
    rw [mul_sub, mul_one, mul_assoc]
  have hPc : ∀ Y : A, Y * (Z - Z * Z * W) = (Z - Z * Z * W) * Y := by
    intro Y
    have hYZ : Commute Y Z := hZc Y
    have hYW : Commute Y W := hWc Y
    exact (Commute.sub_right hYZ ((hYZ.mul_right hYZ).mul_right hYW)).eq
  have hcomm : Commute Z (1 - Z * W) :=
    Commute.sub_right (Commute.one_right Z) (Commute.mul_right (Commute.refl Z) (show Commute Z W from hWc Z))
  have h1 : Z ^ (k + 1) * (1 - Z * W) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, pow_succ' Z (k + 1), mul_assoc, hWe,
      ← pow_succ' Z k, sub_self]
  have hnil : IsNilpotent (Z - Z * Z * W) :=
    ⟨k + 1, by rw [hPZ, hcomm.mul_pow, pow_succ' (1 - Z * W) k, ← mul_assoc, h1, zero_mul]⟩
  exact sub_eq_zero.1 (eq_zero_of_isNilpotent_of_commute hnil hPc)

variable [CharZero F] [FiniteDimensional F A]

/-- The center of a finite-dimensional semisimple algebra over a field of characteristic zero
meets `z^⊥` only in `0`. -/
theorem eq_zero_of_mem_center_of_mem_centerOrthogonal {Z : A}
    (hZ : Z ∈ Subalgebra.center F A) (hZo : Z ∈ centerOrthogonal F A) : Z = 0 := by
  obtain ⟨W, hW, hZW⟩ := exists_center_mul_mul_eq hZ
  by_contra hne
  have hWc : ∀ Y : A, Y * W = W * Y := fun Y => (Subalgebra.mem_center_iff (R := F)).1 hW Y
  have he : Z * W * (Z * W) = Z * W := by
    rw [show Z * W * (Z * W) = Z * (W * Z) * W by simp only [mul_assoc], ← hWc Z,
      ← mul_assoc Z Z W, ← hZW]
  have h0 : Z * W ≠ 0 := by
    intro h
    apply hne
    rw [hZW, mul_assoc, h, mul_zero]
  apply trace_lmul_ne_zero_of_mul_self (F := F) he h0
  have h := hZo W hW
  change traceFormPairing F A W Z = 0 at h
  rwa [traceFormPairing_apply, ← hWc Z] at h

/-- `A = z ⊕ z^⊥` for the trace form. -/
theorem isCompl_center_centerOrthogonal :
    IsCompl (Subalgebra.center F A).toSubmodule (centerOrthogonal F A) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    traceFormPairing_isSymm.isRefl).2 ?_
  rw [Submodule.disjoint_def]
  intro Z hZ hZo
  exact eq_zero_of_mem_center_of_mem_centerOrthogonal hZ hZo

omit [CharZero F] in
/-- When `A` is not commutative, the centralizer of a nilpotent element is strictly larger than
the center. -/
theorem finrank_center_lt_finrank_centralizer (hA : Subalgebra.center F A ≠ ⊤) {N : A}
    (hN : IsNilpotent N) :
    Module.finrank F (Subalgebra.center F A) <
      Module.finrank F (Subalgebra.centralizer F ({N} : Set A)) := by
  have hle : Subalgebra.center F A ≤ Subalgebra.centralizer F ({N} : Set A) :=
    Subalgebra.center_le_centralizer F _
  have hne : Subalgebra.center F A ≠ Subalgebra.centralizer F ({N} : Set A) := by
    intro h
    by_cases h0 : N = 0
    · apply hA
      rw [h, h0, eq_top_iff]
      intro Y _
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, zero_mul, mul_zero]
    · apply h0
      have hNc : N ∈ Subalgebra.center F A := by
        rw [h, Subalgebra.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
      exact eq_zero_of_isNilpotent_of_commute hN fun Y => (Subalgebra.mem_center_iff (R := F)).1 hNc Y
  have hlt : (Subalgebra.center F A).toSubmodule <
      (Subalgebra.centralizer F ({N} : Set A)).toSubmodule :=
    lt_of_le_of_ne hle fun h => hne (Subalgebra.toSubmodule_injective h)
  exact Submodule.finrank_lt_finrank_of_lt hlt

end Center

end Langlands.HarmonicAnalysis.UnitConjugation
