import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-! # Local structure of a centre cut out by points of ramification index one -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

section Points

/-- **Property (N) for the centre.** If the centre `J` is the intersection of the specialization
primes of points of ramification index one, then `ϖ a ∈ J²` implies `a ∈ J`. -/
theorem mem_of_mul_mem_sq {R A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] {ϖ : R} (hϖ : Irreducible ϖ) (J : Ideal A) (S : Set (Ideal A))
    (hJ : J = sInf S)
    (hS : ∀ p ∈ S, ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'')
      (_ : IsDiscreteValuationRing R'') (_ : Algebra R R'') (_ : IsLocalHom (algebraMap R R''))
      (ψ : A →ₐ[R] R''), IsRamificationIndexOne R R'' ∧
        (IsLocalRing.maximalIdeal R'').comap ψ = p)
    (a : A) (ha : algebraMap R A ϖ * a ∈ J ^ 2) : a ∈ J := by
  have hJS := hJ
  rw [hJ]
  refine Submodule.mem_sInf.mpr fun p hp => ?_
  obtain ⟨R'', _, _, _, _, _, ψ, hram, hψ⟩ := hS p hp
  have hJp : J ≤ p := hJS ▸ sInf_le hp
  have hm : IsLocalRing.maximalIdeal R'' = Ideal.span {algebraMap R R'' ϖ} := by
    rw [← hram.1, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hJm : J.map ψ ≤ IsLocalRing.maximalIdeal R'' := by
    rw [Ideal.map_le_iff_le_comap, hψ]; exact hJp
  have h1 : ψ (algebraMap R A ϖ * a) ∈ (J ^ 2).map ψ := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  have h2 := Ideal.pow_right_mono hJm 2 h1
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨r, hr⟩ := h2
  rw [map_mul, AlgHom.commutes] at hr
  have hϖ0 : algebraMap R R'' ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field R''
    rw [hm, h0, Ideal.span_singleton_eq_bot]
  have hψa : ψ a = r * algebraMap R R'' ϖ :=
    mul_left_cancel₀ hϖ0 (by rw [← hr]; ring)
  rw [← hψ, Ideal.mem_comap, hm, hψa]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Points

section Independence

/-- Let `M` be a finite free module over `B` and `K` a field which is a `B`-algebra. If a finite
family in `M` has linearly independent images in `K ⊗_B M`, then every relation among its members
has coefficients killed by an element of `B` with non-zero image in `K`. -/
theorem exists_mul_eq_zero_of_linearIndependent {B M K : Type u} [CommRing B] [AddCommGroup M]
    [Module B M] [Module.Free B M] [Module.Finite B M] [Field K] [Algebra B K] {ι : Type}
    [Fintype ι] (v : ι → M) (hli : LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] v i))
    (b : ι → B) (hb : ∑ i, b i • v i = 0) :
    ∃ t : B, algebraMap B K t ≠ 0 ∧ ∀ i, t * b i = 0 := by
  classical
  set 𝔲 := RingHom.ker (algebraMap B K) with h𝔲
  have : 𝔲.IsPrime := RingHom.ker_isPrime _
  let B' := Localization.AtPrime 𝔲
  have hunit : ∀ s : 𝔲.primeCompl, IsUnit (algebraMap B K s) := fun s =>
    isUnit_iff_ne_zero.mpr fun h => s.2 h
  letI : Algebra B' K := (IsLocalization.lift (M := 𝔲.primeCompl) (S := B') hunit).toAlgebra
  have : IsScalarTower B B' K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := 𝔲.primeCompl) (S := B') hunit x).symm
  have hmax : IsLocalRing.maximalIdeal B' ≤ RingHom.ker (algebraMap B' K) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔲 B', Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact hx
  letI : Algebra (IsLocalRing.ResidueField B') K :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal B') (algebraMap B' K) hmax).toAlgebra
  have : IsScalarTower B' (IsLocalRing.ResidueField B') K :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  let v' : ι → B' ⊗[B] M := fun i => (1 : B') ⊗ₜ[B] v i
  have hli' : LinearIndependent (IsLocalRing.ResidueField B')
      (TensorProduct.mk B' (IsLocalRing.ResidueField B') (B' ⊗[B] M) 1 ∘ v') := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let ρ := LinearMap.rTensor (B' ⊗[B] M)
      (IsScalarTower.toAlgHom B' (IsLocalRing.ResidueField B') K).toLinearMap
    let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange B B' K K M
    have hterm : ∀ j, cb (ρ (c j • (TensorProduct.mk B' (IsLocalRing.ResidueField B')
        (B' ⊗[B] M) 1 ∘ v') j)) =
        algebraMap (IsLocalRing.ResidueField B') K (c j) • ((1 : K) ⊗ₜ[B] v j) := by
      intro j
      simp only [Function.comp_apply, TensorProduct.mk_apply, v', TensorProduct.smul_tmul',
        smul_eq_mul, mul_one, ρ, cb, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom', TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        one_smul]
    have h := congrArg (fun x => cb (ρ x)) hc
    simp only [map_sum, hterm, map_zero] at h
    have := Fintype.linearIndependent_iff.mp hli _ h i
    exact (algebraMap (IsLocalRing.ResidueField B') K).injective (by rw [this, map_zero])
  have hliB' := Module.IsLocalRing.linearIndependent_of_flat v' hli'
  have hsum : ∑ i, algebraMap B B' (b i) • v' i = 0 := by
    have : ∑ i, algebraMap B B' (b i) • v' i = (1 : B') ⊗ₜ[B] ∑ i, b i • v i := by
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [v', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rw [this, hb, TensorProduct.tmul_zero]
  have h0 := Fintype.linearIndependent_iff.mp hliB' _ hsum
  choose t ht using fun i => (IsLocalization.map_eq_zero_iff 𝔲.primeCompl B' (b i)).mp (h0 i)
  refine ⟨∏ i, (t i : B), ?_, fun i => ?_⟩
  · have hmem : ∏ i, (t i : B) ∈ 𝔲.primeCompl :=
      Submonoid.prod_mem _ fun i _ => (t i).2
    exact fun h => hmem h
  · rw [← Finset.mul_prod_erase Finset.univ (fun i => (t i : B)) (Finset.mem_univ i),
      mul_comm (t i : B), mul_assoc, ht i, mul_zero]

end Independence

section Choice

/-- Choosing generators: given a map `d : α → V` to a finite-dimensional vector space and sets
`s_I ⊆ s_J`, there are `wₗ ∈ s_I` and `zⱼ ∈ s_J` such that the `d zⱼ, d wₗ` are linearly
independent, the `d wₗ` span `d(s_I)` and the `d zⱼ, d wₗ` span `d(s_J)`. -/
theorem exists_extension {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (d : α → V) (sI sJ : Set α) (hIJ : sI ⊆ sJ) :
    ∃ (n m : ℕ) (z : Fin n → α) (w : Fin m → α), (∀ l, w l ∈ sI) ∧ (∀ j, z j ∈ sJ) ∧
      LinearIndependent K (Sum.elim (d ∘ z) (d ∘ w)) ∧
      (∀ a ∈ sI, d a ∈ Submodule.span K (Set.range (d ∘ w))) ∧
      (∀ a ∈ sJ, d a ∈ Submodule.span K (Set.range (Sum.elim (d ∘ z) (d ∘ w)))) := by
  classical
  obtain ⟨bI, hbI_sub, -, hbI_span, hbI_li⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty K d) (Set.empty_subset sI)
  obtain ⟨bJ, hbJ_sub, hIJ', hbJ_span, hbJ_li⟩ :=
    exists_linearIndepOn_extension hbI_li (hbI_sub.trans hIJ)
  have : Finite bJ := LinearIndependent.finite hbJ_li
  have : Finite bI := Set.Finite.subset (Set.toFinite bJ) hIJ'
  let cJ : Set α := bJ \ bI
  have : Finite cJ := Set.Finite.subset (Set.toFinite bJ) Set.sdiff_subset
  have : Fintype bI := Fintype.ofFinite _
  have : Fintype cJ := Fintype.ofFinite _
  let eI := (Fintype.equivFin bI).symm
  let eC := (Fintype.equivFin cJ).symm
  refine ⟨Fintype.card cJ, Fintype.card bI, fun j => (eC j : α), fun l => (eI l : α),
    fun l => hbI_sub (eI l).2, fun j => hbJ_sub (eC j).2.1, ?_, ?_, ?_⟩
  · let f : Fin (Fintype.card cJ) ⊕ Fin (Fintype.card bI) → bJ :=
      Sum.elim (fun j => ⟨eC j, (eC j).2.1⟩) (fun l => ⟨eI l, hIJ' (eI l).2⟩)
    have hf : Function.Injective f := by
      rintro (j | l) (j' | l') h <;> have h' := congrArg Subtype.val h <;>
        simp only [f, Sum.elim_inl, Sum.elim_inr] at h'
      · exact congrArg Sum.inl (eC.injective (Subtype.ext h'))
      · exact absurd (h' ▸ (eI l').2) (eC j).2.2
      · exact absurd (h'.symm ▸ (eI l).2) (eC j').2.2
      · exact congrArg Sum.inr (eI.injective (Subtype.ext h'))
    have := hbJ_li.comp f hf
    convert this using 1
    funext k
    rcases k with j | l <;> rfl
  · intro a ha
    have := hbI_span ⟨a, ha, rfl⟩
    refine Submodule.span_mono ?_ this
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨eI.symm ⟨x, hx⟩, ?_⟩
    simp
  · intro a ha
    have := hbJ_span ⟨a, ha, rfl⟩
    refine Submodule.span_mono ?_ this
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxI : x ∈ bI
    · exact ⟨Sum.inr (eI.symm ⟨x, hxI⟩), by simp⟩
    · exact ⟨Sum.inl (eC.symm ⟨x, hx, hxI⟩), by simp⟩

end Choice

end Langlands.AlgebraicGeometry.DvrSmoothening
