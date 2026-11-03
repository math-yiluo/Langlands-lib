import Langlands.CommutativeAlgebra.IntegralFibre.Purity
import Langlands.CommutativeAlgebra.IntegralFibre.Taylor
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Langlands.CommutativeAlgebra.LocallySplit.Basic

/-! # Taylor coefficients detect elements over a Noetherian model -/

open TensorProduct

namespace Langlands.CommutativeAlgebra.IntegralFibre

section Model

variable {R₀ B : Type*} [CommRing R₀] [CommRing B] [Algebra R₀ B]

/-- An associated prime of a module over `R₀` that embeds in a `B`-module comes from a prime
of `B`. -/
lemma exists_prime_comap_eq {N : Type*} [AddCommGroup N] [Module B N] [Module R₀ N]
    [IsScalarTower R₀ B N] (p : Ideal R₀) [p.IsPrime] (n : N)
    (hp : ∀ r : R₀, r ∈ p ↔ r • n = 0) :
    ∃ P : Ideal B, P.IsPrime ∧ P.comap (algebraMap R₀ B) = p := by
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B N n)
  have hI : I.comap (algebraMap R₀ B) = p := by
    ext r
    simp only [Ideal.mem_comap, I, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      algebraMap_smul, hp]
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_comap_le_prime p I hI.le
  refine ⟨Q, hQ, le_antisymm hQp ?_⟩
  rw [← hI]
  exact Ideal.comap_mono hIQ

variable {S₀ : Type*} [CommRing S₀] [Algebra R₀ S₀] [Module.Flat R₀ S₀]

/-- Injectivity on a residue field of `B` descends to the residue field of the contracted
prime. -/
lemma SMulInjOn.residueField_of_comap {u : S₀} (P : Ideal B) [P.IsPrime] (p : Ideal R₀)
    [p.IsPrime] (hp : p = P.comap (algebraMap R₀ B)) (h : SMulInjOn R₀ u P.ResidueField) :
    SMulInjOn R₀ u p.ResidueField := by
  let f : p.ResidueField →ₗ[R₀] P.ResidueField :=
    { toFun := Ideal.ResidueField.map p P (algebraMap R₀ B) hp
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        rw [Algebra.smul_def, map_mul, Ideal.ResidueField.map_algebraMap, RingHom.id_apply,
          Algebra.smul_def, ← IsScalarTower.algebraMap_apply] }
  exact h.of_injective f (Ideal.ResidueField.map p P (algebraMap R₀ B) hp).injective

end Model

section Vanishing

variable {R₀ S₀ B : Type*} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [CommRing B]
  [Algebra R₀ B] [IsNoetherianRing R₀] [IsNoetherianRing S₀] [Module.Flat R₀ S₀]
  (σ₀ : S₀ →ₐ[R₀] R₀) {d : ℕ} (t₀ : Fin d → S₀) (ht₀ : ∀ i, σ₀ (t₀ i) = 0)
  (hθ : ∀ k, Function.Bijective (theta σ₀ t₀ k))
  (hfib : ∀ (P : Ideal B) [P.IsPrime] (u : S₀), σ₀ u = 1 → SMulInjOn R₀ u P.ResidueField)
include ht₀ hfib

/-- **Taylor coefficients detect elements.** An element of `S₀ ⊗[R₀] N`, for a `B`-module
`N`, all of whose Taylor coefficients vanish is zero. -/
theorem eq_zero_of_taylorCoeff_eq_zero {N : Type*} [AddCommGroup N] [Module B N] [Module R₀ N]
    [IsScalarTower R₀ B N] (y : S₀ ⊗[R₀] N)
    (hy : ∀ α, (taylorCoeff σ₀ t₀ hθ α).rTensor N y = 0) : y = 0 := by
  obtain ⟨K, s, n, rfl⟩ := TensorProduct.exists_sum_tmul_eq y
  let N₀ : Submodule R₀ N := Submodule.span R₀ (Set.range n)
  have : Module.Finite R₀ N₀ := Module.Finite.span_of_finite R₀ (Set.finite_range n)
  let y₀ : S₀ ⊗[R₀] N₀ := ∑ j, s j ⊗ₜ ⟨n j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hy₀ : N₀.subtype.lTensor S₀ y₀ = ∑ j, s j ⊗ₜ n j := by simp [y₀]
  have hc : ∀ α, (taylorCoeff σ₀ t₀ hθ α).rTensor N₀ y₀ = 0 := by
    intro α
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := R₀) N₀.subtype
      Subtype.val_injective
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hy₀, hy α, map_zero]
  have hmem : y₀ ∈ (⨅ i : ℕ, RingHom.ker σ₀ ^ i • ⊤ : Submodule S₀ (S₀ ⊗[R₀] N₀)) :=
    Submodule.mem_iInf _ |>.mpr fun k ↦ mem_pow_smul_top_of_taylorCoeff σ₀ t₀ hθ ht₀ y₀ hc k
  obtain ⟨⟨r, hr⟩, hry⟩ := ((RingHom.ker σ₀).mem_iInf_smul_pow_eq_bot_iff y₀).mp hmem
  have hu : SMulInjOn R₀ (1 - r) N₀ := by
    apply SMulInjOn.of_associatedPrimes
    intro p _ hp
    obtain ⟨x, hx⟩ := (isAssociatedPrime_iff.mp hp).2
    have hpx : ∀ c : R₀, c ∈ p ↔ c • (x : N) = 0 := by
      intro c
      rw [hx, Submodule.mem_colon]
      simp only [Set.mem_singleton_iff, forall_eq, Submodule.mem_bot]
      constructor
      · intro h; simpa using congrArg Subtype.val h
      · intro h; exact Subtype.ext (by simpa using h)
    obtain ⟨P, hP, hPp⟩ := exists_prime_comap_eq (B := B) p (x : N) hpx
    exact SMulInjOn.residueField_of_comap P p hPp.symm
      (hfib P (1 - r) (by rw [map_sub, map_one, RingHom.mem_ker.mp hr, sub_zero]))
  have h1 : (1 - r) • y₀ = 0 := by
    have := hry
    simp only at this
    have e1 : (1 - r) • y₀ = (1 : S₀) • y₀ - r • y₀ := sub_smul (1 : S₀) r y₀
    have e2 : (1 : S₀) • y₀ = y₀ := one_smul _ _
    rw [e1, e2, this, sub_self]
  have h0 : y₀ = 0 := hu (h1.trans (smul_zero _).symm)
  rw [← hy₀, h0, map_zero]

end Vanishing

section Split

lemma exists_common_tmul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) (x : Fin n → M ⊗[R] N) :
    ∃ (K : ℕ) (b : Fin n → Fin K → M) (s : Fin K → N), ∀ i, x i = ∑ m, b i m ⊗ₜ s m := by
  induction n with
  | zero => exact ⟨0, fun i ↦ i.elim0, Fin.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨K, b, s, hb⟩ := ih (fun i ↦ x i.succ)
    obtain ⟨K0, m0, n0, h0⟩ := TensorProduct.exists_sum_tmul_eq (x 0)
    refine ⟨K0 + K, Fin.cases (Fin.append m0 0) (fun i ↦ Fin.append 0 (b i)),
      Fin.append n0 s, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [Fin.sum_univ_add, h0]
    · simp [Fin.sum_univ_add, hb i]

lemma exists_fin_family_mem_span {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] (w : ι → M) :
    ∃ (r : ℕ) (α : Fin r → ι), ∀ β, w β ∈ Submodule.span R (Set.range (w ∘ α)) := by
  obtain ⟨N₀, ⟨r, α, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance
    {N | ∃ (r : ℕ) (α : Fin r → ι), N = Submodule.span R (Set.range (w ∘ α))}
    ⟨_, 0, Fin.elim0, rfl⟩
  refine ⟨r, α, fun β ↦ ?_⟩
  have hle : Submodule.span R (Set.range (w ∘ α)) ≤
      Submodule.span R (Set.range (w ∘ Fin.snoc (α := fun _ ↦ ι) α β)) := by
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨j.castSucc, by simp⟩
  have heq := (hle.lt_or_eq).resolve_left (hmax _ ⟨r + 1, _, rfl⟩)
  rw [heq]
  exact Submodule.subset_span ⟨Fin.last r, by simp⟩

variable {R₀ S₀ B : Type*} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [CommRing B]
  [Algebra R₀ B] [IsNoetherianRing R₀] [IsNoetherianRing S₀] [Module.Flat R₀ S₀]
  (σ₀ : S₀ →ₐ[R₀] R₀) {d : ℕ} (t₀ : Fin d → S₀) (ht₀ : ∀ i, σ₀ (t₀ i) = 0)
  (hθ : ∀ k, Function.Bijective (theta σ₀ t₀ k))
  (hfib : ∀ (P : Ideal B) [P.IsPrime] (u : S₀), σ₀ u = 1 → SMulInjOn R₀ u P.ResidueField)

/-- The base-changed Taylor coefficient on `B ⊗[R₀] S₀`. -/
noncomputable def taylorCoeffB (α : Fin d →₀ ℕ) : B ⊗[R₀] S₀ →ₗ[B] B :=
  (TensorProduct.AlgebraTensorModule.rid R₀ B B).toLinearMap ∘ₗ
    (taylorCoeff σ₀ t₀ hθ α).baseChange B

omit [IsNoetherianRing R₀] [IsNoetherianRing S₀] [Module.Flat R₀ S₀] in
lemma taylorCoeffB_tmul (α : Fin d →₀ ℕ) (b : B) (s : S₀) :
    taylorCoeffB σ₀ t₀ hθ α (b ⊗ₜ s) = taylorCoeff σ₀ t₀ hθ α s • b := by
  simp [taylorCoeffB]

include ht₀ hθ hfib

/-- **Local splitting over a Noetherian model.** -/
theorem locallySplit_of_model : LocallySplit B (B ⊗[R₀] S₀) := by
  intro n x
  obtain ⟨K, b, s, hx⟩ := exists_common_tmul n x
  -- coefficient vectors over `R₀`
  let w : (Fin d →₀ ℕ) → (Fin K → R₀) := fun α m ↦ taylorCoeff σ₀ t₀ hθ α (s m)
  obtain ⟨r, α, hα⟩ := exists_fin_family_mem_span (R := R₀) w
  -- the comparison map to `B`-coefficient vectors
  let L : (Fin K → R₀) →ₗ[R₀] (Fin n → B) :=
    { toFun := fun c i ↦ ∑ m, c m • b i m
      map_add' := fun c c' ↦ by ext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c ↦ by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hL : ∀ β, L (w β) = fun i ↦ taylorCoeffB σ₀ t₀ hθ β (x i) := by
    intro β
    ext i
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, w, hx i, map_sum, taylorCoeffB_tmul]
  let v : Fin r → (Fin n → B) := fun j i ↦ taylorCoeffB σ₀ t₀ hθ (α j) (x i)
  let C : Submodule B (Fin n → B) := Submodule.span B (Set.range v)
  have hC : ∀ β, (fun i ↦ taylorCoeffB σ₀ t₀ hθ β (x i)) ∈ C := by
    intro β
    rw [← hL]
    have h1 : L (w β) ∈ Submodule.map L (Submodule.span R₀ (Set.range (w ∘ α))) :=
      Submodule.mem_map_of_mem (hα β)
    rw [Submodule.map_span] at h1
    refine (Submodule.span_le.mpr ?_ : Submodule.span R₀ _ ≤ C.restrictScalars R₀) h1
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨j, by simp only [v, ← hL]; rfl⟩
  -- the auxiliary element of `S₀ ⊗ (B^n / C)`
  let Ŷ : S₀ ⊗[R₀] (Fin n → B) := ∑ m, s m ⊗ₜ[R₀] (fun i ↦ b i m)
  let g : (Fin n → B) →ₗ[R₀] (Fin n → B) ⧸ C := C.mkQ.restrictScalars R₀
  let f : C →ₗ[R₀] (Fin n → B) := C.subtype.restrictScalars R₀
  have hY : g.lTensor S₀ Ŷ = 0 := by
    apply eq_zero_of_taylorCoeff_eq_zero σ₀ t₀ ht₀ hθ hfib (N := (Fin n → B) ⧸ C)
    intro β
    apply (TensorProduct.lid R₀ _).injective
    simp only [Ŷ, map_sum, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      map_zero]
    have : ∑ m, taylorCoeff σ₀ t₀ hθ β (s m) • g (fun i ↦ b i m) = g (L (w β)) := by
      simp only [← map_smul, ← map_sum]
      congr 1
      ext i
      simp [L, w, Finset.sum_apply]
    rw [this]
    simp only [g, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hL]
    exact hC β
  have hex : Function.Exact f g := LinearMap.exact_subtype_mkQ C
  obtain ⟨Z, hZ⟩ := (lTensor_exact S₀ hex (Submodule.mkQ_surjective C) Ŷ).mp hY
  let Γ : S₀ ⊗[R₀] (Fin n → B) →ₗ[R₀] (Fin n → B ⊗[R₀] S₀) :=
    LinearMap.pi fun i ↦ (TensorProduct.comm R₀ S₀ B).toLinearMap ∘ₗ
      (LinearMap.proj i : (Fin n → B) →ₗ[R₀] B).lTensor S₀
  have hΓ : Γ Ŷ = x := by
    ext i
    simp [Γ, Ŷ, hx i]
  have key : ∀ Z : S₀ ⊗[R₀] C, ∃ y : Fin r → B ⊗[R₀] S₀,
      Γ (f.lTensor S₀ Z) = fun i ↦ ∑ j, taylorCoeffB σ₀ t₀ hθ (α j) (x i) • y j := by
    intro Z
    induction Z with
    | tmul s0 c =>
      obtain ⟨c, hc⟩ := c
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hc
      refine ⟨fun j ↦ a j ⊗ₜ s0, ?_⟩
      ext i
      simp only [Γ, f, v, LinearMap.lTensor_tmul, LinearMap.pi_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.restrictScalars_apply, Submodule.coe_subtype,
        LinearEquiv.coe_coe, TensorProduct.comm_tmul, LinearMap.coe_proj, Function.eval,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TensorProduct.sum_tmul,
        TensorProduct.smul_tmul', mul_comm]
    | add Z Z' hZ hZ' =>
      obtain ⟨y, hy⟩ := hZ
      obtain ⟨y', hy'⟩ := hZ'
      refine ⟨y + y', ?_⟩
      rw [map_add, map_add, hy, hy']
      ext i
      simp [smul_add, Finset.sum_add_distrib]
  obtain ⟨y, hy⟩ := key Z
  refine ⟨r, LinearMap.pi fun j ↦ taylorCoeffB σ₀ t₀ hθ (α j), y, fun i ↦ ?_⟩
  have := congrFun hy i
  rw [hZ, hΓ] at this
  simpa using this.symm

end Split

end Langlands.CommutativeAlgebra.IntegralFibre
