import Langlands.RingTheory.Smooth.SectionJets
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Krull intersection along the section of a smooth algebra -/

universe u

open TensorProduct

namespace Langlands.GroupScheme.SmoothNormalizer

section Noetherian

variable {R₀ C₀ R : Type*} [CommRing R₀] [CommRing C₀] [CommRing R]
  [Algebra R₀ C₀] [Algebra R₀ R]

/-- The Noetherian step: if the quotients `C₀ ⧸ J ^ (n + 1)` are flat over `R₀` and `C₀` is
Noetherian, an element of `C₀ ⊗[R₀] R` vanishing in every `(C₀ ⧸ J ^ (n + 1)) ⊗[R₀] R` is
killed by an element `1 - r` with `r ∈ J`. -/
theorem exists_one_sub_smul_eq_zero [IsNoetherianRing C₀] (J : Ideal C₀)
    (hflat : ∀ n : ℕ, Module.Flat R₀ (C₀ ⧸ J ^ (n + 1))) (b : C₀ ⊗[R₀] R)
    (hb : ∀ n : ℕ, LinearMap.rTensor R (Ideal.Quotient.mkₐ R₀ (J ^ (n + 1))).toLinearMap b = 0) :
    ∃ r ∈ J, (1 - r) • b = 0 := by
  obtain ⟨M, hM, hbM⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({b} : Set (C₀ ⊗[R₀] R)) (Set.finite_singleton b)
  obtain ⟨b', hb'⟩ := hbM (Set.mem_singleton b)
  -- `b'` vanishes in every truncation, by flatness of the truncations.
  have hvan : ∀ n : ℕ,
      LinearMap.rTensor M (Ideal.Quotient.mkₐ R₀ (J ^ (n + 1))).toLinearMap b' = 0 := by
    intro n
    have := hflat n
    have hinj : Function.Injective (LinearMap.lTensor (C₀ ⧸ J ^ (n + 1)) M.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap M.subtype M.injective_subtype
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hb', hb n]
  -- Hence `b'` lies in every `J ^ (n + 1) • ⊤`.
  have hmem : b' ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule C₀ (C₀ ⊗[R₀] M)) := by
    rw [Submodule.mem_iInf]
    intro i
    cases i with
    | zero => simp
    | succ n =>
      let g := (Ideal.Quotient.mkₐ R₀ (J ^ (n + 1))).toLinearMap
      have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
      have hex := rTensor_exact M g.exact_subtype_ker_map hg
      have hrange : ∀ y : LinearMap.ker g ⊗[R₀] M,
          LinearMap.rTensor M (LinearMap.ker g).subtype y ∈
            (J ^ (n + 1) • ⊤ : Submodule C₀ (C₀ ⊗[R₀] M)) := by
        intro y
        induction y with
        | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
        | tmul j m =>
          rw [LinearMap.rTensor_tmul]
          have hj : (j : C₀) ∈ J ^ (n + 1) :=
            Ideal.Quotient.eq_zero_iff_mem.1 (LinearMap.mem_ker.1 j.2)
          have : (j : C₀) ⊗ₜ[R₀] m = (j : C₀) • ((1 : C₀) ⊗ₜ[R₀] m) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [Submodule.coe_subtype, this]
          exact Submodule.smul_mem_smul hj Submodule.mem_top
      obtain ⟨y, hy⟩ := hex.linearMap_ker_eq ▸ (LinearMap.mem_ker.mpr (hvan n))
      rw [← hy]
      exact hrange y
  obtain ⟨⟨r, hr⟩, hrb⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff J b').1 hmem
  refine ⟨r, hr, ?_⟩
  have h0 : (1 - r) • b' = 0 := by
    have h1 : (1 - r) • b' = (1 : C₀) • b' - r • b' := sub_smul (1 : C₀) r b'
    rw [h1, one_smul]
    exact sub_eq_zero.2 hrb.symm
  have hlin : ∀ (c : C₀) (x : C₀ ⊗[R₀] M),
      LinearMap.lTensor C₀ M.subtype (c • x) = c • LinearMap.lTensor C₀ M.subtype x := by
    intro c x
    induction x with
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
    | tmul a m => rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.smul_tmul']
  rw [← hb', ← hlin, h0, map_zero]

end Noetherian

section Descent

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- **Krull intersection along the section of a smooth algebra.** If `b` lies in every power of
the augmentation ideal `ker ε` of a smooth `R`-algebra `C`, then `b` is killed by an element `s`
with `ε s = 1`. No Noetherian hypothesis is made: the proof descends `C` to a smooth algebra over
a finitely generated `ℤ`-algebra. -/
theorem exists_mul_eq_zero_of_forall_mem_pow [Algebra.Smooth R C] (ε : C →ₐ[R] R) {b : C}
    (hb : ∀ n : ℕ, b ∈ RingHom.ker ε ^ n) : ∃ s : C, ε s = 1 ∧ s * b = 0 := by
  obtain ⟨R₀, C₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R C
  have : Algebra.FiniteType ℤ R₀ := ⟨R₀.fg_top.mpr hfg⟩
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have : IsNoetherianRing C₀ := Algebra.FiniteType.isNoetherianRing R₀ C₀
  -- The section, restricted to the model `C₀`.
  let ε₀ : C₀ →+* R := ε.toRingHom.comp (e.symm.toRingHom.comp
    (Algebra.TensorProduct.includeRight : C₀ →ₐ[R₀] R ⊗[R₀] C₀).toRingHom)
  have hε₀ : ∀ (r : R) (c : C₀), ε (e.symm (r ⊗ₜ[R₀] c)) = r * ε₀ c := by
    intro r c
    have : r ⊗ₜ[R₀] c = r • ((1 : R) ⊗ₜ[R₀] c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, smul_eq_mul]
    rfl
  let _ : Algebra C₀ R := ε₀.toAlgebra
  have : IsScalarTower R₀ C₀ R := IsScalarTower.of_algebraMap_eq fun x => by
    change (x : R) = ε₀ (algebraMap R₀ C₀ x)
    have h := hε₀ (x : R) 1
    rw [map_one, mul_one] at h
    rw [← h]
    have : (x : R) ⊗ₜ[R₀] (1 : C₀) = (1 : R) ⊗ₜ[R₀] algebraMap R₀ C₀ x := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Subalgebra.smul_def, smul_eq_mul, mul_one]
    rw [this]
    rfl
  -- The diagonal model `C₁ = C₀ ⊗[R₀] C₀` over `C₀`, with the multiplication as section.
  let μ : C₀ ⊗[R₀] C₀ →ₐ[C₀] C₀ := Algebra.TensorProduct.lmul'' R₀
  have hμtmul : ∀ a c : C₀, μ (a ⊗ₜ[R₀] c) = a * c := fun _ _ => rfl
  have hμ : Function.Surjective μ := fun c => ⟨c ⊗ₜ 1, by rw [hμtmul, mul_one]⟩
  have : IsNoetherianRing (C₀ ⊗[R₀] C₀) := Algebra.FiniteType.isNoetherianRing C₀ _
  have hflat : ∀ n : ℕ, Module.Flat C₀ ((C₀ ⊗[R₀] C₀) ⧸ RingHom.ker μ ^ (n + 1)) := fun n =>
    have := (Algebra.Smooth.finite_projective_quotient_ker_pow μ n).2
    inferInstance
  -- The identification `C ≃ (C₀ ⊗[R₀] C₀) ⊗[C₀] R`.
  let cbc := Algebra.TensorProduct.cancelBaseChange R₀ C₀ R R C₀
  let cm := Algebra.TensorProduct.comm C₀ R (C₀ ⊗[R₀] C₀)
  let Φ : C ≃+* (C₀ ⊗[R₀] C₀) ⊗[C₀] R :=
    e.toRingEquiv.trans (cbc.symm.toRingEquiv.trans cm.toRingEquiv)
  let ρ : (C₀ ⊗[R₀] C₀) ⊗[C₀] R →ₐ[C₀] R :=
    (Algebra.TensorProduct.lid C₀ R).toAlgHom.comp
      (Algebra.TensorProduct.map μ (AlgHom.id C₀ R))
  have hρ : ∀ t, ε (Φ.symm t) = ρ t := by
    intro t
    induction t with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul x r =>
      induction x with
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy, map_add]
      | tmul a c =>
        change ε (e.symm (cbc (cm.symm ((a ⊗ₜ[R₀] c) ⊗ₜ[C₀] r)))) = _
        simp only [cm, cbc, Algebra.TensorProduct.comm_symm_tmul,
          Algebra.TensorProduct.cancelBaseChange_tmul]
        rw [hε₀, Algebra.smul_def]
        change ε₀ a * r * ε₀ c = (Algebra.TensorProduct.lid C₀ R) (μ (a ⊗ₜ[R₀] c) ⊗ₜ[C₀] r)
        rw [Algebra.TensorProduct.lid_tmul, hμtmul, Algebra.smul_def]
        change ε₀ a * r * ε₀ c = ε₀ (a * c) * r
        rw [map_mul]
        ring
  -- The augmentation ideal corresponds to the extension of `ker μ`.
  have hkerρ : ∀ t, ρ t = 0 →
      t ∈ Ideal.map (Algebra.TensorProduct.includeLeft : C₀ ⊗[R₀] C₀ →ₐ[C₀] _) (RingHom.ker μ) := by
    intro t ht
    have h1 : Algebra.TensorProduct.map μ (AlgHom.id C₀ R) t = 0 := by
      apply (Algebra.TensorProduct.lid C₀ R).injective
      rw [map_zero]
      exact ht
    rw [← Algebra.TensorProduct.rTensor_ker μ hμ]
    exact h1
  have hle : Ideal.map Φ (RingHom.ker ε) ≤
      Ideal.map (Algebra.TensorProduct.includeLeft : C₀ ⊗[R₀] C₀ →ₐ[C₀] _) (RingHom.ker μ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    apply hkerρ
    rw [← hρ, RingEquiv.symm_apply_apply]
    exact hx
  have hpow : ∀ n : ℕ, Φ b ∈
      Ideal.map (Algebra.TensorProduct.includeLeft : C₀ ⊗[R₀] C₀ →ₐ[C₀] _) (RingHom.ker μ ^ n) := by
    intro n
    rw [Ideal.map_pow]
    have h := Ideal.mem_map_of_mem Φ (hb n)
    rw [Ideal.map_pow] at h
    exact Ideal.pow_right_mono hle n h
  obtain ⟨r, hr, hrb⟩ := exists_one_sub_smul_eq_zero (R₀ := C₀) (RingHom.ker μ) hflat (Φ b)
    (fun n => by
      have hmap : Ideal.map (Algebra.TensorProduct.includeLeft : C₀ ⊗[R₀] C₀ →ₐ[C₀] _)
          (RingHom.ker μ ^ (n + 1)) ≤ RingHom.ker (Algebra.TensorProduct.map
            (Ideal.Quotient.mkₐ C₀ (RingHom.ker μ ^ (n + 1))) (AlgHom.id C₀ R)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.2 hx, TensorProduct.zero_tmul]
      exact hmap (hpow (n + 1)))
  refine ⟨Φ.symm ((1 - r) ⊗ₜ[C₀] (1 : R)), ?_, ?_⟩
  · rw [hρ]
    change (Algebra.TensorProduct.lid C₀ R) (μ (1 - r) ⊗ₜ[C₀] (1 : R)) = 1
    rw [Algebra.TensorProduct.lid_tmul, map_sub, map_one, RingHom.mem_ker.1 hr, sub_zero,
      one_smul]
  · have h : ∀ t : (C₀ ⊗[R₀] C₀) ⊗[C₀] R, (1 - r) • t = ((1 - r) ⊗ₜ[C₀] (1 : R)) * t := by
      intro t
      induction t with
      | add x y hx hy => rw [smul_add, hx, hy, mul_add]
      | tmul x y => rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          smul_eq_mul]
    apply Φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply, ← h, hrb, map_zero]

end Descent

end Langlands.GroupScheme.SmoothNormalizer
