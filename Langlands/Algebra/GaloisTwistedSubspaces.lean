import Langlands.Algebra.GaloisTwistedMatrix
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Descent of twisted-stable subspaces of a matrix algebra -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {n : Type} [Fintype n] [DecidableEq n]
  (P : (K ≃ₐ[k] K) → Matrix n n K) (hP : ∀ σ, IsUnit (P σ))
  (A : Subalgebra k (Matrix n n K)) (hA : A ≤ twistedFixed P)
  (hspan : Submodule.span K (A : Set (Matrix n n K)) = ⊤)

/-- The twisted Galois action `M ↦ P σ⁻¹ σ(M) P σ` on matrices. -/
def twistedAct (σ : K ≃ₐ[k] K) (M : Matrix n n K) : Matrix n n K :=
  (P σ)⁻¹ * M.map σ * P σ

omit [IsGalois k K] in
theorem twistedAct_add (σ : K ≃ₐ[k] K) (M N : Matrix n n K) :
    twistedAct P σ (M + N) = twistedAct P σ M + twistedAct P σ N := by
  simp only [twistedAct, Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.add_mul]

omit [IsGalois k K] in
theorem twistedAct_zero (σ : K ≃ₐ[k] K) : twistedAct P σ (0 : Matrix n n K) = 0 := by
  simp [twistedAct]

omit [IsGalois k K] in
theorem twistedAct_smul (σ : K ≃ₐ[k] K) (a : K) (M : Matrix n n K) :
    twistedAct P σ (a • M) = σ a • twistedAct P σ M := by
  have h : (a • M).map σ = σ a • M.map σ := by
    ext i j
    simp [map_mul]
  simp only [twistedAct, h, Matrix.mul_smul, Matrix.smul_mul]

omit [IsGalois k K] in
include hP in
theorem twistedAct_of_mem {σ : K ≃ₐ[k] K} {X : Matrix n n K} (hX : X ∈ twistedFixed P) :
    twistedAct P σ X = X := by
  have h := hX σ
  rw [twistedAct, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hP σ)), Matrix.one_mul]

include hP hA hspan in
/-- A `K`-subspace of `M_n(K)` stable under the twisted Galois action is spanned by its
elements in `A`. -/
theorem le_span_inf_of_twisted_stable (S : Submodule K (Matrix n n K))
    (hS : ∀ σ, ∀ M ∈ S, twistedAct P σ M ∈ S) :
    S ≤ Submodule.span K {X | X ∈ A ∧ X ∈ S} := by
  classical
  have := finiteDimensional P hP A hA
  let b := Module.finBasis k A
  let v : Fin (Module.finrank k A) → Matrix n n K := fun i => (b i : Matrix n n K)
  have hli : LinearIndependent K v := linearIndependent_of_le_twistedFixed P hP v
    (fun i => hA (b i).2)
    (b.linearIndependent.map' A.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    have hxb : (⟨x, hx⟩ : A) ∈ Submodule.span k (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    have hxv : x ∈ Submodule.span k (Set.range v) := by
      have := Submodule.apply_mem_span_image_of_mem_span A.val.toLinearMap hxb
      rw [← Set.range_comp] at this
      exact this
    exact Submodule.span_le_restrictScalars k K (Set.range v) hxv
  let c := Module.Basis.mk hli hsp
  have hc : ∀ i, c i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hact : ∀ (σ : K ≃ₐ[k] K) (x : Fin (Module.finrank k A) →₀ K),
      twistedAct P σ (Finsupp.linearCombination K v x) =
        Finsupp.linearCombination K v (LinearAlgebra.GaloisSubmoduleDescent.conjugate σ x) := by
    intro σ x
    induction x using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, twistedAct_zero]
      rw [show LinearAlgebra.GaloisSubmoduleDescent.conjugate σ
        (0 : Fin (Module.finrank k A) →₀ K) = 0 by ext; simp, map_zero]
    | add x y hx hy =>
      rw [map_add, twistedAct_add, hx, hy, ← map_add]
      congr 1
      ext i
      simp
    | single i a =>
      rw [Finsupp.linearCombination_single, twistedAct_smul,
        twistedAct_of_mem P hP (hA (b i).2)]
      rw [show LinearAlgebra.GaloisSubmoduleDescent.conjugate σ (Finsupp.single i a) =
        Finsupp.single i (σ a) by ext j; simp [Finsupp.single_apply]; split_ifs <;> simp,
        Finsupp.linearCombination_single]
  have hcv : (⇑c : Fin (Module.finrank k A) → Matrix n n K) = v := funext hc
  let W : Submodule K (Fin (Module.finrank k A) →₀ K) := S.map c.repr.toLinearMap
  have hW : ∀ (σ : K ≃ₐ[k] K) (x : Fin (Module.finrank k A) →₀ K), x ∈ W →
      LinearAlgebra.GaloisSubmoduleDescent.conjugate σ x ∈ W := by
    rintro σ _ ⟨M, hM, rfl⟩
    refine ⟨twistedAct P σ M, hS σ M hM, ?_⟩
    change c.repr (twistedAct P σ M) = LinearAlgebra.GaloisSubmoduleDescent.conjugate σ (c.repr M)
    have hMc : M = Finsupp.linearCombination K v (c.repr M) := by
      rw [← hcv, c.linearCombination_repr]
    conv_lhs => rw [hMc]
    rw [hact, ← hcv, c.repr_linearCombination]
  intro M hM
  have hMW : c.repr M ∈ W := ⟨M, hM, rfl⟩
  rw [LinearAlgebra.GaloisSubmoduleDescent.eq_span_ground_vectors W hW] at hMW
  have h1 : M ∈ (Submodule.span K {x | ∃ y : Fin (Module.finrank k A) →₀ k,
      LinearAlgebra.GaloisSubmoduleDescent.extend y = x ∧ x ∈ W}).map
        c.repr.symm.toLinearMap :=
    ⟨c.repr M, hMW, c.repr.symm_apply_apply M⟩
  rw [Submodule.map_span] at h1
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨x, ⟨y, rfl, hxW⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · change c.repr.symm (LinearAlgebra.GaloisSubmoduleDescent.extend y) ∈ A
    rw [c.repr_symm_apply, hcv, Finsupp.linearCombination_apply,
      LinearAlgebra.GaloisSubmoduleDescent.extend, Finsupp.mapRange.linearMap_apply,
      Finsupp.sum_mapRange_index (fun i => zero_smul K (v i))]
    exact sum_mem fun i _ => by
      change (Algebra.linearMap k K) (y i) • v i ∈ A
      rw [Algebra.linearMap_apply, algebraMap_smul]
      exact A.smul_mem (b i).2 _
  · obtain ⟨M', hM', hM'x⟩ := hxW
    change c.repr.symm _ ∈ S
    rw [← hM'x]
    simpa using hM'


include hP hA hspan in
/-- For a subspace `U ⊆ Kⁿ` stable under `u ↦ σ⁻¹(P σ u)`, there is an idempotent of `A` whose
kernel is exactly `U`. -/
theorem exists_idempotent_ker_eq [Nonempty n] (U : Submodule K (n → K))
    (hU : ∀ σ : K ≃ₐ[k] K, ∀ u ∈ U, (fun i => σ.symm ((P σ *ᵥ u) i)) ∈ U) :
    ∃ e ∈ A, e * e = e ∧ ∀ v : n → K, e *ᵥ v = 0 ↔ v ∈ U := by
  classical
  have := finiteDimensional P hP A hA
  have := isSimpleRing P hP A hA hspan
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsSemisimpleRing A := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr this
  -- the left ideal of elements of `A` killing `U`
  let L : Submodule A A :=
    { carrier := {X | ∀ u ∈ U, (X : Matrix n n K) *ᵥ u = 0}
      add_mem' := fun hX hY u hu => by
        simp only [Subalgebra.coe_add, Matrix.add_mulVec, hX u hu, hY u hu, add_zero]
      zero_mem' := fun u _ => by simp
      smul_mem' := fun Y X hX u hu => by
        change ((Y * X : A) : Matrix n n K) *ᵥ u = 0
        rw [Subalgebra.coe_mul, ← Matrix.mulVec_mulVec, hX u hu, Matrix.mulVec_zero] }
  obtain ⟨L', hcompl⟩ := exists_isCompl L
  have h1 : (1 : A) ∈ L ⊔ L' := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hright : ∀ X ∈ L, X * e = X := by
    intro X hX
    have hXf : X * f ∈ L ⊓ L' := by
      refine ⟨?_, L'.smul_mem X hf⟩
      have : X * f = X - X * e := by
        rw [eq_sub_iff_add_eq, add_comm, ← mul_add, hef, mul_one]
      rw [this]
      exact L.sub_mem hX (L.smul_mem X he)
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hXf
    calc X * e = X * e + X * f := by rw [hXf, add_zero]
      _ = X := by rw [← mul_add, hef, mul_one]
  refine ⟨e, e.2, congrArg Subtype.val (hright e he), fun v => ⟨fun hv => ?_, fun hv => he v hv⟩⟩
  by_contra hvU
  obtain ⟨ℓ, hℓv, hℓU⟩ := U.exists_dual_map_eq_bot_of_notMem hvU inferInstance
  obtain ⟨j₀⟩ := ‹Nonempty n›
  let M : Matrix n n K := Matrix.of fun i j => if i = j₀ then ℓ (Pi.single j 1) else 0
  have hMw : ∀ w : n → K, M *ᵥ w = fun i => if i = j₀ then ℓ w else 0 := by
    intro w
    funext i
    have hw : w = ∑ j, w j • (Pi.single j (1 : K) : n → K) := by
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    by_cases hi : i = j₀
    · simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, hi, ite_true]
      conv_rhs => rw [hw]
      simp [map_sum, map_smul, mul_comm]
    · simp [Matrix.mulVec, dotProduct, M, hi]
  let S : Submodule K (Matrix n n K) :=
    { carrier := {N | ∀ u ∈ U, N *ᵥ u = 0}
      add_mem' := fun hN hN' u hu => by rw [Matrix.add_mulVec, hN u hu, hN' u hu, add_zero]
      zero_mem' := fun u _ => by simp
      smul_mem' := fun c N hN u hu => by rw [Matrix.smul_mulVec, hN u hu, smul_zero] }
  have hMS : M ∈ S := by
    intro u hu
    rw [hMw]
    funext i
    have : ℓ u = 0 := by
      have : ℓ u ∈ U.map ℓ := Submodule.mem_map_of_mem hu
      rwa [hℓU, Submodule.mem_bot] at this
    simp [this]
  have hSst : ∀ σ, ∀ N ∈ S, twistedAct P σ N ∈ S := by
    intro σ N hN u hu
    have hx := hU σ u hu
    have hNx := hN _ hx
    rw [twistedAct, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hmap : N.map σ *ᵥ (P σ *ᵥ u) = fun i => σ ((N *ᵥ fun i => σ.symm ((P σ *ᵥ u) i)) i) := by
      funext i
      have h := RingHom.map_mulVec (σ : K →+* K) N (fun j => σ.symm ((P σ *ᵥ u) j)) i
      simpa [Function.comp_def] using h.symm
    rw [hmap, hNx]
    show (P σ)⁻¹ *ᵥ (fun _ => σ (0 : K)) = 0
    rw [map_zero]
    exact Matrix.mulVec_zero _
  have hspanM := le_span_inf_of_twisted_stable P hP A hA hspan S hSst hMS
  have hkill : ∀ N ∈ Submodule.span K {X | X ∈ A ∧ X ∈ S}, N *ᵥ v = 0 := by
    intro N hN
    induction hN using Submodule.span_induction with
    | mem X hX =>
      have hXL : (⟨X, hX.1⟩ : A) ∈ L := hX.2
      have := congrArg Subtype.val (hright _ hXL)
      change X * (e : Matrix n n K) = X at this
      rw [← this, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    | zero => simp
    | add N N' _ _ h h' => rw [Matrix.add_mulVec, h, h', add_zero]
    | smul c N _ h => rw [Matrix.smul_mulVec, h, smul_zero]
  have hMv := hkill M hspanM
  rw [hMw] at hMv
  have := congrFun hMv j₀
  simp at this
  exact hℓv this

end Langlands.Algebra.GaloisTwistedMatrix
