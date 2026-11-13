import Langlands.CommutativeAlgebra.ApproximateQuotientRigidity
import Langlands.CommutativeAlgebra.ArtinReesSyzygyApproximation
import Langlands.CommutativeAlgebra.EtaleApproximationModel
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement
import Langlands.CommutativeAlgebra.LocalPresentationModSquare
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing

/-! # Finite-type algebraic charts of complete local algebras

Assuming etale approximation for maximal localizations of finite-type `ℤ`-algebras,
every complete Noetherian local algebra `A` over a finite-type `ℤ`-algebra `R`, with
residue field of finite type over `R`, has a finite-type `R`-algebra `T` with a
maximal ideal `m_T`, receiving a given finite-type algebra `B → A`, such that `A` and
`T` agree modulo the squares of their maximal ideals compatibly with `B`, and every
lift `A → T / m_T ^ n` of this identification is an isomorphism modulo `m_A ^ n`. -/

universe u

open IsLocalRing

namespace Langlands.CommutativeAlgebra.CompleteLocalAlgebraicChart

open MaximalLocalizationCompletion ApproximateQuotientRigidity

set_option maxHeartbeats 1600000 in
/-- **Algebraic charts from etale approximation.** -/
theorem exists_algebraicChart
    (happrox : FiniteTypeIntEtaleCompletionApproximationStatement.{u})
    {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R]
    {K : Type u} [Field K] [Algebra R K] [Algebra.FiniteType R K]
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra R A]
    (ε : A →ₐ[R] K) (hε : Function.Surjective ε)
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (β : B →ₐ[R] A) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T), Algebra.FiniteType R T ∧
      ∃ (εT : T →ₐ[R] K) (mT : Ideal T), Function.Surjective εT ∧ RingHom.ker εT = mT ∧
      ∃ (βT : B →ₐ[R] T) (φ₂ : A →ₐ[R] T ⧸ mT ^ 2),
        φ₂.comp β = (Ideal.Quotient.mkₐ R (mT ^ 2)).comp βT ∧
        (∀ a t, φ₂ a = Ideal.Quotient.mk _ t → εT t = ε a) ∧
        ∀ (n : ℕ) (hn : 2 ≤ n) (φ : A →ₐ[R] T ⧸ mT ^ n),
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hn)).comp φ = φ₂ →
            Function.Surjective φ ∧ RingHom.ker φ = maximalIdeal A ^ n := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  -- a presentation of `A` modulo the square of its maximal ideal
  obtain ⟨ι, _, σA, hsq⟩ :=
    LocalPresentationModSquare.exists_mvPolynomial_surjective_mod_sq ε hε
  have hkerε : ∀ a, ε a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε, RingHom.mem_ker]
    rfl
  have hsurjS : Function.Surjective (ε.comp σA) := by
    intro k
    obtain ⟨a, rfl⟩ := hε k
    obtain ⟨s, hs⟩ := hsq a
    refine ⟨s, ?_⟩
    have : ε (a - σA s) = 0 := (hkerε _).mpr (Ideal.pow_le_self two_ne_zero hs)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let 𝔪 : Ideal (MvPolynomial ι R) := RingHom.ker (ε.comp σA)
  have h𝔪max : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurjS
  have hσA𝔪 : ∀ s, σA.toRingHom s ∈ maximalIdeal A ↔ s ∈ 𝔪 := by
    intro s
    rw [← hkerε]
    rfl
  have hft : Algebra.FiniteType ℤ (MvPolynomial ι R) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have happ := @happrox (MvPolynomial ι R) _ (by convert hft; exact Subsingleton.elim _ _) 𝔪 _
  -- the completion of the polynomial ring and its surjection onto `A`
  let P := Localization.AtPrime 𝔪
  let 𝔫 := maximalIdeal (AdicCompletion (maximalIdeal P) P)
  let σ : MvPolynomial ι R →+* AdicCompletion (maximalIdeal P) P :=
    algebraMap (MvPolynomial ι R) _
  let π := completionLift 𝔪 σA.toRingHom hσA𝔪
  have hπσ : ∀ s, π (σ s) = σA s := completionLift_algebraMap 𝔪 σA.toRingHom hσA𝔪
  have hπs := completionLift_surjective 𝔪 σA.toRingHom hσA𝔪 hsq
  have hπ := completionLift_comap_pow 𝔪 σA.toRingHom hσA𝔪 hsq
  have : IsNoetherianRing (AdicCompletion (maximalIdeal P) P) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  have hσ1 : ∀ n x, ∃ s, x - σ s ∈ 𝔫 ^ n := fun n x =>
    exists_sub_algebraMap_mem_pow_completion 𝔪 x n
  have hσ2 : ∀ n s, σ s ∈ 𝔫 ^ n → s ∈ 𝔪 ^ n := fun n s h =>
    mem_pow_of_algebraMap_completion_mem_pow 𝔪 h
  have hσ3 : 𝔫 = 𝔪.map σ := maximalIdeal_completion_eq_map 𝔪
  have hkerπ : RingHom.ker π ≤ 𝔫 := by
    refine le_trans ?_ (IsLocalRing.le_maximalIdeal (J := (maximalIdeal A).comap π) ?_)
    · intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
      exact Ideal.zero_mem _
    · intro h
      have : (1 : AdicCompletion (maximalIdeal P) P) ∈ (maximalIdeal A).comap π := by
        rw [h]; trivial
      rw [Ideal.mem_comap, map_one] at this
      exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hπ𝔫 : ∀ x ∈ 𝔫, π x ∈ maximalIdeal A := by
    intro x hx
    have : x ∈ (maximalIdeal A ^ 1).comap π := by
      rw [hπ 1]; exact Ideal.mem_sup_right (by rwa [pow_one])
    simpa using this
  -- generators of the kernel and their syzygies
  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (RingHom.ker π))
  let bl := Fintype.linearCombination (AdicCompletion (maximalIdeal P) P) b
  obtain ⟨t, Ks, hKs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker bl))
  have hbl : ∀ u : Fin r → AdicCompletion (maximalIdeal P) P, bl u = ∑ j, u j * b j := by
    intro u; simp [bl, Fintype.linearCombination_apply]
  have hKsyz : ∀ u : Fin r → AdicCompletion (maximalIdeal P) P, ∑ j, u j * b j = 0 →
      u ∈ Submodule.span (AdicCompletion (maximalIdeal P) P) (Set.range Ks) := by
    intro u hu
    rw [hKs, LinearMap.mem_ker, hbl, hu]
  have hKrows : ∀ l, ∑ j, Ks l j * b j = 0 := by
    intro l
    have : Ks l ∈ LinearMap.ker bl := by rw [← hKs]; exact Submodule.subset_span ⟨l, rfl⟩
    rw [LinearMap.mem_ker, hbl] at this
    exact this
  obtain ⟨c, hc⟩ := ArtinReesSyzygyApproximation.exists_approximation_order 𝔫 b Ks hKsyz
  -- a presentation of `B` and lifts of its generators
  obtain ⟨m, ψB, hψB⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R B›
  obtain ⟨v, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (RingHom.ker ψB))
  choose ã hã using fun i : Fin m => hπs (β (ψB (MvPolynomial.X i)))
  have hπC : π.comp (σ.comp MvPolynomial.C) = algebraMap R A := by
    ext x
    simp only [RingHom.comp_apply, hπσ]
    exact σA.commutes x
  have hFJ : ∀ j, MvPolynomial.eval₂ (σ.comp MvPolynomial.C) ã (F j) ∈ RingHom.ker π := by
    intro j
    rw [RingHom.mem_ker, MvPolynomial.eval₂_comp_left, hπC]
    have h1 : (π ∘ ã) = fun i => (β.comp ψB) (MvPolynomial.X i) := funext hã
    rw [h1, ← MvPolynomial.aeval_def, show (MvPolynomial.aeval fun i =>
      (β.comp ψB) (MvPolynomial.X i)) = β.comp ψB from (MvPolynomial.aeval_unique _).symm]
    have : F j ∈ RingHom.ker ψB := by rw [← hF]; exact Submodule.subset_span ⟨j, rfl⟩
    rw [AlgHom.comp_apply, RingHom.mem_ker.mp this, map_zero]
  choose cc hcc using fun j => (Submodule.mem_span_range_iff_exists_fun _).mp
    (hb.symm ▸ hFJ j : _ ∈ Submodule.span _ (Set.range b))
  -- the finite system of equations and its solution in the completion
  let V := Fin m ⊕ Fin r ⊕ (Fin v × Fin r) ⊕ (Fin t × Fin r)
  let val : V → AdicCompletion (maximalIdeal P) P :=
    Sum.elim ã (Sum.elim b (Sum.elim (fun p => cc p.1 p.2) (fun p => Ks p.1 p.2)))
  let Y : Fin m → MvPolynomial V R := fun i => MvPolynomial.X (Sum.inl i)
  let Bv : Fin r → MvPolynomial V R := fun i => MvPolynomial.X (Sum.inr (Sum.inl i))
  let Cv : Fin v → Fin r → MvPolynomial V R :=
    fun j i => MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (j, i))))
  let Kv : Fin t → Fin r → MvPolynomial V R :=
    fun l i => MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (l, i))))
  let relB : Fin v → MvPolynomial V R := fun j =>
    MvPolynomial.rename Sum.inl (F j) - ∑ i, Cv j i * Bv i
  let relK : Fin t → MvPolynomial V R := fun l => ∑ i, Kv l i * Bv i
  let rel : Fin (v + t) → MvPolynomial V R := Fin.append relB relK
  have hrel : ∀ k, MvPolynomial.eval₂ (σ.comp MvPolynomial.C) val (rel k) = 0 := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun l => ?_) k
    · simp only [rel, Fin.append_left, relB, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, Cv, Bv, MvPolynomial.eval₂_X]
      have hvl : val ∘ Sum.inl = ã := rfl
      rw [sub_eq_zero, hvl, ← hcc j]
      simp only [smul_eq_mul]
      rfl
    · simp only [rel, Fin.append_right, relK, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
        Kv, Bv, MvPolynomial.eval₂_X]
      exact hKrows l
  -- the unramified finite-type model of an approximate solution
  obtain ⟨T₀, _, _, hT₀, σT, vT, ι₀, hισ, hvrel, hvcong, hT⟩ :=
    EtaleApproximationModel.exists_model 𝔪 happ val rel hrel (c + 2)
  let b'' : Fin r → T₀ := fun i => vT (Bv i)
  let a'' : Fin m → T₀ := fun i => vT (Y i)
  have hAR : ∀ d, ∀ z ∈ Ideal.span (Set.range (fun j => ι₀ (b'' j))), z ∈ 𝔫 ^ d →
      z ∈ RingHom.ker π ⊔ 𝔫 ^ (d + 1) := by
    have h := hc (c + 2) (by omega) (fun i => ι₀ (b'' i)) (fun l i => ι₀ (vT (Kv l i)))
      (fun l => by
        have := hvrel (Fin.natAdd v l)
        simp only [rel, Fin.append_right, relK] at this
        simp only [← map_mul, ← map_sum, b'', this, map_zero])
      (fun i => hvcong (Sum.inr (Sum.inl i)))
      (fun l i => hvcong (Sum.inr (Sum.inr (Sum.inr (l, i)))))
    intro d z hz hzd
    have := h d z hz hzd
    rwa [show Ideal.span (Set.range b) = RingHom.ker π from hb] at this
  -- the quotient `T` and its residue map
  let T := T₀ ⧸ Ideal.span (Set.range b'')
  let mT' : Ideal T := mT 𝔫 ι₀ b''
  have hστ : ∀ x, ι₀ (σT x) = σ x := hισ
  let εT₀ : T₀ →ₐ[R] K :=
    { (ε.toRingHom.comp (π.comp ι₀)) with
      commutes' := fun x => by
        have : algebraMap R T₀ x = σT (MvPolynomial.C x) := (σT.commutes x).symm
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, this, hστ, hπσ]
        rw [show (MvPolynomial.C x : MvPolynomial ι R) = algebraMap R _ x from rfl,
          σA.commutes]
        exact ε.commutes x }
  have hεT₀ : ∀ x, εT₀ x = ε (π (ι₀ x)) := fun x => rfl
  have hεT₀ker : ∀ x, εT₀ x = 0 ↔ x ∈ u₀ 𝔫 ι₀ := by
    intro x
    rw [hεT₀, hkerε, ← Ideal.mem_comap, ← pow_one (maximalIdeal A), hπ 1, pow_one,
      sup_eq_right.mpr hkerπ]
    rfl
  have hb''u : ∀ i, b'' i ∈ u₀ 𝔫 ι₀ := by
    intro i
    change ι₀ (b'' i) ∈ 𝔫
    have h1 := hvcong (Sum.inr (Sum.inl i))
    have h2 : b i ∈ 𝔫 := hkerπ (by rw [← hb]; exact Submodule.subset_span ⟨i, rfl⟩)
    have : ι₀ (b'' i) = (ι₀ (b'' i) - b i) + b i := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_self (by omega) h1) h2
  have hspan_le : Ideal.span (Set.range b'') ≤ u₀ 𝔫 ι₀ := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hb''u i
  let εT : T →ₐ[R] K := Ideal.Quotient.liftₐ _ εT₀ (fun x hx => (hεT₀ker x).mpr (hspan_le hx))
  have hεTmk : ∀ x, εT (Ideal.Quotient.mk _ x) = εT₀ x := fun x => rfl
  have hεTσ : ∀ s, εT (Ideal.Quotient.mk _ (σT s)) = ε (σA s) := by
    intro s; rw [hεTmk, hεT₀, hστ, hπσ]
  have hεTker : RingHom.ker εT = mT' := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hεTmk, hεT₀ker]
    have := mk_mem_mT_pow_iff 𝔫 ι₀ b'' 1 y
    rw [pow_one, pow_one, sup_eq_left.mpr hspan_le] at this
    exact this.symm
  have hεTsurj : Function.Surjective εT := by
    intro k
    obtain ⟨s, hs⟩ := hsurjS k
    exact ⟨Ideal.Quotient.mk _ (σT s), by rw [hεTσ]; exact hs⟩
  -- the map from `B`
  let βT₁ : MvPolynomial (Fin m) R →ₐ[R] T :=
    (Ideal.Quotient.mkₐ R _).comp (vT.comp (MvPolynomial.rename Sum.inl))
  have hβT₁ : RingHom.ker ψB ≤ RingHom.ker βT₁ := by
    rw [← hF, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change (Ideal.Quotient.mk _ (vT (MvPolynomial.rename Sum.inl (F j))) : T) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := hvrel (Fin.castAdd t j)
    simp only [rel, Fin.append_left, relB, map_sub, sub_eq_zero] at this
    rw [this, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hβT₁' : ∀ x ∈ RingHom.ker ψB, βT₁ x = 0 := fun x hx => hβT₁ hx
  let βT : B →ₐ[R] T := (Ideal.Quotient.liftₐ _ βT₁ hβT₁').comp
    (Ideal.quotientKerAlgEquivOfSurjective hψB).symm.toAlgHom
  have hβTψ : ∀ p, βT (ψB p) = βT₁ p := by
    intro p
    change Ideal.Quotient.liftₐ _ βT₁ hβT₁'
      ((Ideal.quotientKerAlgEquivOfSurjective hψB).symm (ψB p)) = _
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  -- the identification modulo squares
  let p2 : MvPolynomial ι R →ₐ[R] A ⧸ maximalIdeal A ^ 2 :=
    (Ideal.Quotient.mkₐ R _).comp σA
  have hp2 : Function.Surjective p2 := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs⟩ := hsq a
    exact ⟨s, (Ideal.Quotient.eq.mpr hs).symm⟩
  let q2 := q 𝔫 σT ι₀ b'' 2
  have hq2 : Function.Surjective q2 := q_surjective 𝔫 σT ι₀ hT b'' 2
  have hsup : RingHom.ker π ⊔ 𝔫 ^ 2 =
      Ideal.span (Set.range (fun j => ι₀ (b'' j))) ⊔ 𝔫 ^ 2 := by
    have hN : 𝔫 ^ (c + 2) ≤ 𝔫 ^ 2 := Ideal.pow_le_pow_right (by omega)
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [← hb, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : b i = ι₀ (b'' i) - (ι₀ (b'' i) - b i) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
        (Ideal.mem_sup_right (hN (hvcong (Sum.inr (Sum.inl i)))))
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show ι₀ (b'' i) ∈ RingHom.ker π ⊔ 𝔫 ^ 2
      have : ι₀ (b'' i) = b i + (ι₀ (b'' i) - b i) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (by rw [← hb]; exact Submodule.subset_span ⟨i, rfl⟩))
        (Ideal.mem_sup_right (hN (hvcong (Sum.inr (Sum.inl i)))))
  have hker2 : RingHom.ker p2 = RingHom.ker q2 := by
    ext s
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (σA s) = 0 ↔ q 𝔫 σT ι₀ b'' 2 s = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, σA_mem_pow_iff 𝔫 σ σA π (maximalIdeal A) hπσ hπ,
      q_eq_zero_iff 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT b'' hσ1, hsup]
  let φ₂ : A →ₐ[R] T ⧸ mT' ^ 2 :=
    (Ideal.quotientKerAlgEquivOfSurjective hq2).toAlgHom.comp
      ((Ideal.quotientEquivAlgOfEq R hker2).toAlgHom.comp
        ((Ideal.quotientKerAlgEquivOfSurjective hp2).symm.toAlgHom.comp
          (Ideal.Quotient.mkₐ R (maximalIdeal A ^ 2))))
  have hφ₂σ : ∀ s, φ₂ (σA s) = q2 s := by
    intro s
    change (Ideal.quotientKerAlgEquivOfSurjective hq2)
      ((Ideal.quotientEquivAlgOfEq R hker2)
        ((Ideal.quotientKerAlgEquivOfSurjective hp2).symm (p2 s))) = q2 s
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  have hφ₂sq : ∀ a a', a - a' ∈ maximalIdeal A ^ 2 → φ₂ a = φ₂ a' := by
    intro a a' h
    change (Ideal.quotientKerAlgEquivOfSurjective hq2) ((Ideal.quotientEquivAlgOfEq R hker2)
        ((Ideal.quotientKerAlgEquivOfSurjective hp2).symm (Ideal.Quotient.mk _ a))) =
      (Ideal.quotientKerAlgEquivOfSurjective hq2) ((Ideal.quotientEquivAlgOfEq R hker2)
        ((Ideal.quotientKerAlgEquivOfSurjective hp2).symm (Ideal.Quotient.mk _ a')))
    rw [Ideal.Quotient.eq.mpr h]
  have hφ₂ : ∀ a, ∃ s, a - σA s ∈ maximalIdeal A ^ 2 ∧ φ₂ a = q2 s := by
    intro a
    obtain ⟨s, hs⟩ := hsq a
    exact ⟨s, hs, (hφ₂sq a (σA s) hs).trans (hφ₂σ s)⟩
  refine ⟨T, inferInstance, inferInstance, inferInstance, εT, mT', hεTsurj, hεTker, βT, φ₂,
    ?_, ?_, ?_⟩
  · -- compatibility with `B`
    have hψ : (φ₂.comp β).comp ψB = ((Ideal.Quotient.mkₐ R (mT' ^ 2)).comp βT).comp ψB := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, hβTψ]
      rw [← hã i]
      obtain ⟨s, hs⟩ := hσ1 2 (ã i)
      have hπs2 : π (ã i) - σA s ∈ maximalIdeal A ^ 2 := by
        rw [← hπσ, ← map_sub, ← Ideal.mem_comap, hπ 2]
        exact Ideal.mem_sup_right hs
      rw [hφ₂sq _ _ hπs2, hφ₂σ]
      change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (σT s)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (vT (MvPolynomial.rename Sum.inl
          (MvPolynomial.X i))))
      rw [Ideal.Quotient.eq, ← map_sub, mk_mem_mT_pow_iff]
      refine Ideal.mem_sup_left ?_
      have hdiff : ι₀ (σT s - a'' i) ∈ 𝔫 ^ 2 := by
        rw [map_sub, hστ]
        have h1 := hvcong (Sum.inl i)
        have : σ s - ι₀ (a'' i) = -(ã i - σ s) - (ι₀ (a'' i) - ã i) := by ring
        rw [this]
        exact Ideal.sub_mem _ (neg_mem hs)
          (Ideal.pow_le_pow_right (by omega) h1)
      have := mem_u₀_pow_of_mem 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT hdiff
      simpa [a'', Y] using this
    ext x
    obtain ⟨p, rfl⟩ := hψB x
    exact DFunLike.congr_fun hψ p
  · -- residue compatibility
    intro a t' ht'
    obtain ⟨s, hs, hφs⟩ := hφ₂ a
    rw [hφs] at ht'
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (σT s)) = _ at ht'
    have hmem : t' - Ideal.Quotient.mk _ (σT s) ∈ mT' := by
      have := Ideal.Quotient.eq.mp ht'.symm
      exact Ideal.pow_le_self two_ne_zero this
    rw [← hεTker, RingHom.mem_ker, map_sub, sub_eq_zero, hεTσ] at hmem
    rw [hmem]
    have : ε (a - σA s) = 0 := (hkerε _).mpr (Ideal.pow_le_self two_ne_zero hs)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  · -- rigidity
    intro n hn φ hφ
    have hred : ∀ s, Ideal.Quotient.factor (Ideal.pow_le_pow_right hn) (φ (σA s)) = q2 s := by
      intro s
      rw [← hφ₂σ, ← hφ]
      rfl
    have hloc : ∀ a ∈ maximalIdeal A, φ a ∈ mT'.map (Ideal.Quotient.mk (mT' ^ n)) := by
      intro a ha
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ a)
      obtain ⟨s, hs, hφs⟩ := hφ₂ a
      have hsm : s ∈ 𝔪 := by
        rw [← hσA𝔪]
        change σA s ∈ maximalIdeal A
        have : σA s = a - (a - σA s) := by ring
        rw [this]
        exact Ideal.sub_mem _ ha (Ideal.pow_le_self two_ne_zero hs)
      have h2 : Ideal.Quotient.mk (mT' ^ 2) x = q2 s := by
        rw [← hφs, ← hφ, AlgHom.comp_apply, ← hx]
        rfl
      change _ = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (σT s)) at h2
      have hx2 : x - Ideal.Quotient.mk _ (σT s) ∈ mT' :=
        Ideal.pow_le_self two_ne_zero (Ideal.Quotient.eq.mp h2)
      have hσTs : (Ideal.Quotient.mk _ (σT s) : T) ∈ mT' := by
        apply Ideal.mem_map_of_mem
        change ι₀ (σT s) ∈ 𝔫
        rw [hστ, hσ3]
        exact Ideal.mem_map_of_mem _ hsm
      rw [← hx]
      apply Ideal.mem_map_of_mem
      have : x = (x - Ideal.Quotient.mk _ (σT s)) + Ideal.Quotient.mk _ (σT s) := by ring
      rw [this]
      exact Ideal.add_mem _ hx2 hσTs
    exact rigidity 𝔪 𝔫 σ σT ι₀ σA π (maximalIdeal A) hπσ hπ hπs hσ1 hσ2 hσ3 hισ hT b'' hAR
      hn φ hloc hred

set_option linter.defProp false in
/-- The implication proved by `exists_algebraicChart`, as a single term from etale
approximation over finite-type integer algebras to the algebraic charts. -/
def algebraicChartOfEtaleApproximation := @exists_algebraicChart.{u}

end Langlands.CommutativeAlgebra.CompleteLocalAlgebraicChart
