import Langlands.GroupScheme.Torus.CompleteLocalDeformation.Lifting
import Mathlib.RingTheory.Filtration

/-! # Rigidity of bialgebra maps over finite algebras over a noetherian local ring

Let `A` be a noetherian local ring with maximal ideal `𝔪`, let `K` be a commutative `A`-algebra
that is finite as an `A`-module, and let `B` be a commutative `K`-bialgebra that is
cocommutative modulo `𝔪 K`. Two bialgebra maps `B → K[N]` that agree modulo `𝔪 K` are equal.

The module also supplies the cocommutativity hypothesis in the forms in which it arises:
from a cocommutative reduction `(K ⧸ I) ⊗ B`, from a bialgebra isomorphism of that reduction
with a group algebra, and by scalar extension from a bialgebra over `A`. -/

noncomputable section

universe u v w

open TensorProduct Coalgebra

namespace Langlands.GroupScheme.CompleteLocalDeformation

open Langlands.GroupAlgebraCoaction

section Cocomm

/-- A coalgebra equivalent to a cocommutative coalgebra is cocommutative. -/
theorem isCocomm_of_coalgEquiv {R : Type u} [CommSemiring R] {C : Type v} {D : Type w}
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid D] [Module R D]
    [Coalgebra R D] [IsCocomm R D] (e : C ≃ₗc[R] D) : IsCocomm R C where
  comm_comp_comul := by
    ext c
    apply (TensorProduct.congr e.toLinearEquiv e.toLinearEquiv).injective
    change TensorProduct.map (e : C →ₗ[R] D) (e : C →ₗ[R] D) (TensorProduct.comm R C C (comul c)) =
      TensorProduct.map (e : C →ₗ[R] D) (e : C →ₗ[R] D) (comul c)
    have h : TensorProduct.map (e : C →ₗ[R] D) (e : C →ₗ[R] D) (comul c) = comul (e c) :=
      CoalgHomClass.map_comp_comul_apply e c
    rw [TensorProduct.map_comm, h, comm_comul]

variable {R : Type u} [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
variable {C : Type v} [CommRing C] [Bialgebra R C]

/-- The comultiplication of a scalar extension `S ⊗ C` on `1 ⊗ x`. -/
theorem comul_one_tmul_baseChange (x : C) :
    comul (R := S) ((1 : S) ⊗ₜ[R] x) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R S C C
        ((1 : S) ⊗ₜ[R] comul (R := R) x) := by
  rw [TensorProduct.comul_tmul]
  have h1 : comul (R := S) (1 : S) = 1 ⊗ₜ 1 := rfl
  rw [h1]
  generalize comul (R := R) x = t
  induction t with
  | tmul c d => simp
  | add s t hs ht => rw [TensorProduct.tmul_add, map_add, hs, ht, TensorProduct.tmul_add, map_add]

/-- Distributing a scalar extension over a tensor product commutes with swapping factors. -/
theorem distribBaseChange_one_tmul_comm (t : C ⊗[R] C) :
    TensorProduct.AlgebraTensorModule.distribBaseChange R S C C
        ((1 : S) ⊗ₜ[R] TensorProduct.comm R C C t) =
      TensorProduct.comm S (S ⊗[R] C) (S ⊗[R] C)
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S C C ((1 : S) ⊗ₜ[R] t)) := by
  induction t with
  | tmul c d => simp
  | add s t hs ht => rw [map_add, TensorProduct.tmul_add, map_add, hs, TensorProduct.tmul_add,
      map_add, map_add, ht]

/-- Cocommutativity modulo `I • ⊤` passes to every scalar extension. -/
theorem comul_sub_comm_mem_baseChange (J : Ideal R)
    (hcomm : ∀ c : C, comul c - TensorProduct.comm R C C (comul c) ∈
      J • (⊤ : Submodule R (C ⊗[R] C)))
    (t : S ⊗[R] C) :
    comul t - TensorProduct.comm S (S ⊗[R] C) (S ⊗[R] C) (comul t) ∈
      J.map (algebraMap R S) • (⊤ : Submodule S ((S ⊗[R] C) ⊗[S] (S ⊗[R] C))) := by
  set I := J.map (algebraMap R S)
  -- the image of `1 ⊗ s` for `s ∈ J • ⊤`
  have himage : ∀ s : C ⊗[R] C, s ∈ J • (⊤ : Submodule R (C ⊗[R] C)) →
      TensorProduct.AlgebraTensorModule.distribBaseChange R S C C ((1 : S) ⊗ₜ[R] s) ∈
        I • (⊤ : Submodule S ((S ⊗[R] C) ⊗[S] (S ⊗[R] C))) := by
    intro s hs
    refine Submodule.smul_induction_on hs (fun r hr y _ => ?_) (fun a b ha hb => ?_)
    · rw [TensorProduct.tmul_smul, ← algebraMap_smul S r, map_smul]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    · rw [TensorProduct.tmul_add, map_add]; exact add_mem ha hb
  -- the generators `1 ⊗ c`
  have hgen : ∀ c : C, comul ((1 : S) ⊗ₜ[R] c) - TensorProduct.comm S (S ⊗[R] C) (S ⊗[R] C)
      (comul ((1 : S) ⊗ₜ[R] c)) ∈ I • (⊤ : Submodule S ((S ⊗[R] C) ⊗[S] (S ⊗[R] C))) := by
    intro c
    rw [comul_one_tmul_baseChange, ← distribBaseChange_one_tmul_comm, ← map_sub,
      ← TensorProduct.tmul_sub]
    exact himage _ (hcomm c)
  induction t with
  | tmul s c =>
    have : s ⊗ₜ[R] c = s • ((1 : S) ⊗ₜ[R] c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul]
    convert Submodule.smul_mem _ s (hgen c) using 1
    rw [smul_sub]
  | add s t hs ht =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hs ht

/-- If the reduction `(R ⧸ J) ⊗ C` is cocommutative, then `C` is cocommutative modulo `J`. -/
theorem comul_sub_comm_mem_of_isCocomm (J : Ideal R) [IsCocomm (R ⧸ J) ((R ⧸ J) ⊗[R] C)]
    (c : C) : comul c - TensorProduct.comm R C C (comul c) ∈
      J • (⊤ : Submodule R (C ⊗[R] C)) := by
  rw [← one_tmul_eq_zero_iff]
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R (R ⧸ J) C C).injective
  rw [TensorProduct.tmul_sub, map_sub, distribBaseChange_one_tmul_comm, ← comul_one_tmul,
    comm_comul, sub_self, map_zero]

/-- If the reduction `(R ⧸ J) ⊗ C` is isomorphic as a bialgebra to a group algebra, then `C`
is cocommutative modulo `J`. -/
theorem comul_sub_comm_mem_of_bialgEquiv (J : Ideal R) {N : Type*} [AddCommMonoid N]
    (e : (R ⧸ J) ⊗[R] C ≃ₐc[R ⧸ J] AddMonoidAlgebra (R ⧸ J) N) (c : C) :
    comul c - TensorProduct.comm R C C (comul c) ∈ J • (⊤ : Submodule R (C ⊗[R] C)) := by
  have : IsCocomm (R ⧸ J) ((R ⧸ J) ⊗[R] C) := isCocomm_of_coalgEquiv e.toCoalgEquiv
  exact comul_sub_comm_mem_of_isCocomm J c

end Cocomm

section Separated

/-- A noetherian ring is separated for every ideal contained in its Jacobson radical. -/
theorem eq_zero_of_mem_pow_of_le_jacobson {K : Type u} [CommRing K] [IsNoetherianRing K]
    (I : Ideal K) (hI : I ≤ Ideal.jacobson ⊥) (x : K) (hx : ∀ k : ℕ, x ∈ I ^ k) : x = 0 := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := K) I hI
  have hmem : x ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule K K) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [smul_eq_mul, Ideal.mul_top]
    exact hx i
  rw [h] at hmem
  exact (Submodule.mem_bot K).mp hmem

/-- A finite algebra over a noetherian local ring `A` is separated for the extension of the
maximal ideal of `A`. -/
theorem eq_zero_of_mem_map_maximalIdeal_pow {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {K : Type v} [CommRing K] [Algebra A K] [Module.Finite A K] (x : K)
    (hx : ∀ k : ℕ, x ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A K)) ^ k) : x = 0 := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := K) (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hmem : x ∈ (⨅ i : ℕ, IsLocalRing.maximalIdeal A ^ i • ⊤ : Submodule A K) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    exact hx i
  rw [h] at hmem
  exact (Submodule.mem_bot A).mp hmem

end Separated

section Rigidity

variable {K : Type u} [CommRing K] {N : Type w} [AddCommGroup N]
variable {B : Type v} [CommRing B] [Bialgebra K B]

/-- **Rigidity modulo an ideal, module form.** Over an `I`-adically separated base, bialgebra
maps `B → K[N]` from a bialgebra cocommutative modulo `I` that agree modulo `I` are equal. -/
theorem eq_of_sub_mem_smul_top (I : Ideal K) (hsep : ∀ x : K, (∀ k : ℕ, x ∈ I ^ k) → x = 0)
    (hcomm : ∀ b : B, comul b - TensorProduct.comm K B B (comul b) ∈
      I • (⊤ : Submodule K (B ⊗[K] B)))
    (π π' : B →ₐc[K] AddMonoidAlgebra K N)
    (h : ∀ b : B, π b - π' b ∈ I • (⊤ : Submodule K (AddMonoidAlgebra K N))) : π = π' := by
  refine eq_of_coeff_sub_mem I hsep hcomm π π' fun b n => ?_
  have := form_mem_of_mem_smul_top (lcoeff n) I (h b)
  rwa [lcoeff_apply, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at this

/-- **Rigidity over a noetherian ring.** Let `I` be an ideal in the Jacobson radical of a
noetherian ring `K`. Bialgebra maps `B → K[N]` from a bialgebra cocommutative modulo `I` that
agree modulo `I` are equal. -/
theorem eq_of_sub_mem_of_le_jacobson [IsNoetherianRing K] (I : Ideal K)
    (hI : I ≤ Ideal.jacobson ⊥)
    (hcomm : ∀ b : B, comul b - TensorProduct.comm K B B (comul b) ∈
      I • (⊤ : Submodule K (B ⊗[K] B)))
    (π π' : B →ₐc[K] AddMonoidAlgebra K N)
    (h : ∀ b : B, π b - π' b ∈ I • (⊤ : Submodule K (AddMonoidAlgebra K N))) : π = π' :=
  eq_of_sub_mem_smul_top I (eq_zero_of_mem_pow_of_le_jacobson I hI) hcomm π π' h

/-- **Rigidity over a finite algebra over a noetherian local ring.** Let `A` be a noetherian
local ring with maximal ideal `𝔪` and `K` a finite `A`-algebra. Bialgebra maps `B → K[N]` from a
`K`-bialgebra cocommutative modulo `𝔪 K` that agree modulo `𝔪 K` are equal. -/
theorem eq_of_sub_mem_map_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra A K] [Module.Finite A K]
    (hcomm : ∀ b : B, comul b - TensorProduct.comm K B B (comul b) ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A K) • (⊤ : Submodule K (B ⊗[K] B)))
    (π π' : B →ₐc[K] AddMonoidAlgebra K N)
    (h : ∀ b : B, π b - π' b ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A K) •
        (⊤ : Submodule K (AddMonoidAlgebra K N))) : π = π' :=
  eq_of_sub_mem_smul_top _ eq_zero_of_mem_map_maximalIdeal_pow hcomm π π' h

/-- **Rigidity for scalar extensions.** Let `A` be a noetherian local ring with maximal ideal
`𝔪`, `C` a commutative `A`-bialgebra cocommutative modulo `𝔪`, and `K` a finite `A`-algebra.
Bialgebra maps `K ⊗ C → K[N]` that agree modulo `𝔪 K` are equal. -/
theorem eq_of_sub_mem_map_maximalIdeal_baseChange {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra A K] [Module.Finite A K] {C : Type*} [CommRing C]
    [Bialgebra A C]
    (hcomm : ∀ c : C, comul c - TensorProduct.comm A C C (comul c) ∈
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (C ⊗[A] C)))
    (π π' : K ⊗[A] C →ₐc[K] AddMonoidAlgebra K N)
    (h : ∀ b : K ⊗[A] C, π b - π' b ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A K) •
        (⊤ : Submodule K (AddMonoidAlgebra K N))) : π = π' :=
  eq_of_sub_mem_map_maximalIdeal (A := A)
    (comul_sub_comm_mem_baseChange K (IsLocalRing.maximalIdeal A) hcomm) π π' h

end Rigidity

end Langlands.GroupScheme.CompleteLocalDeformation
