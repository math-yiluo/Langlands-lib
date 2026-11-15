import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationStatement
import Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionProof
import Mathlib

/-! # Lifting resolutions along regular-type sequences (Stacks Lemma 9.2, 07F8) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open TensorProduct

section SingularIdeal

/-- The singular ideal does not change along an isomorphism of bases. -/
theorem singularIdeal_eq_of_bijective {R₁ R₂ D : Type*} [CommRing R₁] [CommRing R₂] [CommRing D]
    [Algebra R₁ R₂] [Algebra R₂ D] [Algebra R₁ D] [IsScalarTower R₁ R₂ D]
    (h : Function.Bijective (algebraMap R₁ R₂)) :
    singularIdeal R₁ D = singularIdeal R₂ D := by
  have : Algebra.FormallyEtale R₁ R₂ :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R₁ R₂) h)
  have hloc : Algebra.smoothLocus R₁ D = Algebra.smoothLocus R₂ D := by
    ext p
    exact (Algebra.FormallySmooth.iff_restrictScalars (R := R₁) (A := R₂)
      (B := Localization.AtPrime p.asIdeal))
  rw [singularIdeal, singularIdeal, hloc]

/-- The singular ideal is compatible with base change. -/
theorem includeRight_mem_singularIdeal {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra.FinitePresentation R A] {a : A}
    (ha : a ∈ singularIdeal R A) : (1 : S) ⊗ₜ[R] a ∈ singularIdeal S (S ⊗[R] A) := by
  have := DimZeroResolutionProof.smooth_away_of_mem_singularIdeal ha
  exact DimZeroResolutionProof.mem_singularIdeal_of_smooth _
    (Algebra.Smooth.of_equiv (IsLocalization.Away.tensorProductEquivTMulRight R S a
      (Localization.Away a)))

end SingularIdeal


section StrictlyStandard

open MvPolynomial

/-- A multiple of a strictly standard element is strictly standard. -/
theorem IsStrictlyStandard.mul_right {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {a : A} (ha : IsStrictlyStandard R a) (b : A) : IsStrictlyStandard R (a * b) := by
  obtain ⟨n, m, c, hcn, hcm, f, φ, hφ, hker, hmem, g, hg, hgf⟩ := ha
  obtain ⟨g', rfl⟩ := hφ b
  refine ⟨n, m, c, hcn, hcm, f, φ, hφ, hker, Ideal.mul_mem_right _ _ hmem, g * g', by
    rw [map_mul, hg], fun j hj => ?_⟩
  rw [mul_comm g g', mul_assoc]
  exact Ideal.mul_mem_left _ _ (hgf j hj)

/-- Powers of strictly standard elements are strictly standard. -/
theorem IsStrictlyStandard.pow {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {a : A} (ha : IsStrictlyStandard R a) {k : ℕ} (hk : 0 < k) : IsStrictlyStandard R (a ^ k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add, pow_succ', ]
  exact ha.mul_right _

/-- Strictly standard elements are preserved by base change (Stacks Lemma 2.7, 07CC). -/
theorem IsStrictlyStandard.baseChange {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {a : A} (ha : IsStrictlyStandard R a) :
    IsStrictlyStandard S ((1 : S) ⊗ₜ[R] a) := by
  obtain ⟨n, m, c, hcn, hcm, f, φ, hφ, hker, hmem, g, hg, hgf⟩ := ha
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S
  let Φ : S ⊗[R] MvPolynomial (Fin n) R →ₐ[S] S ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id S S) φ
  let φS : MvPolynomial (Fin n) S →ₐ[S] S ⊗[R] A := Φ.comp e.symm.toAlgHom
  let ρ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S := MvPolynomial.map (algebraMap R S)
  have hφS : ∀ p, φS (ρ p) = (1 : S) ⊗ₜ[R] φ p := by
    intro p
    simp [φS, Φ, e, ρ, algebraTensorAlgEquiv_symm_map]
  have hΦ : Function.Surjective Φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul s y =>
      obtain ⟨p, rfl⟩ := hφ y
      exact ⟨s ⊗ₜ p, by simp [Φ]⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  have hkerΦ : RingHom.ker Φ =
      (RingHom.ker φ).map (Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin n) R →ₐ[R] S ⊗[R] MvPolynomial (Fin n) R) :=
    Algebra.TensorProduct.lTensor_ker φ hφ
  refine ⟨n, m, c, hcn, hcm, fun j => ρ (f j), φS, hΦ.comp e.symm.surjective, ?_, ?_, ρ g,
    by rw [hφS, hg], fun j hj => ?_⟩
  · -- the kernel
    have h1 : RingHom.ker φS = (RingHom.ker Φ).map (e : S ⊗[R] MvPolynomial (Fin n) R ≃+* _) := by
      ext p
      rw [Ideal.mem_map_of_equiv]
      constructor
      · intro hp
        exact ⟨e.symm p, hp, e.apply_symm_apply p⟩
      · rintro ⟨x, hx, rfl⟩
        show Φ (e.symm (e x)) = 0
        rw [e.symm_apply_apply]
        exact hx
    rw [h1, hkerΦ, hker, Ideal.map_span, Ideal.map_span, Set.image_image, ← Set.range_comp]
    congr 1
    ext x
    simp [e, ρ]
  · -- the minors
    have hdet : ∀ k : Fin c ↪o Fin n,
        φS (Matrix.det (Matrix.of fun j i : Fin c => pderiv (k i) (ρ (f (Fin.castLE hcm j))))) =
          (1 : S) ⊗ₜ[R] φ (Matrix.det (Matrix.of fun j i : Fin c =>
            pderiv (k i) (f (Fin.castLE hcm j)))) := by
      intro k
      rw [← hφS, RingHom.map_det]
      congr 2
      ext j i
      simp [ρ, pderiv_map]
    have hfun : (fun k : Fin c ↪o Fin n =>
        φS (Matrix.det fun j i : Fin c => pderiv (k i) (ρ (f (Fin.castLE hcm j))))) =
        fun k => (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
          (φ (Matrix.det fun j i : Fin c => pderiv (k i) (f (Fin.castLE hcm j)))) :=
      funext hdet
    rw [hfun, Set.range_comp']
    have := Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight :
      A →ₐ[R] S ⊗[R] A) hmem
    rw [Ideal.map_span] at this
    exact this
  · have := Ideal.mem_map_of_mem ρ (hgf j hj)
    rw [map_mul, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
      ← Set.image_comp] at this
    exact this

end StrictlyStandard

section OneStep

variable {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]

/-- The problem `R/(π⁸) → (R/(π⁸)) ⊗ A → Λ/π⁸Λ` induced by `f`. -/
noncomputable def quotMap (f : A →ₐ[R] Λ) (π : R) :
    (R ⧸ Ideal.span {π ^ 8}) ⊗[R] A →ₐ[R ⧸ Ideal.span {π ^ 8}]
      Λ ⧸ (Ideal.span {π ^ 8}).map (algebraMap R Λ) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (R ⧸ Ideal.span {π ^ 8}) (Λ ⧸ (Ideal.span {π ^ 8}).map (algebraMap R Λ)))
    ((Ideal.Quotient.mkₐ R _).comp f) (fun _ _ => .all _ _)

theorem quotMap_tmul (f : A →ₐ[R] Λ) (π : R) (a : A) :
    quotMap f π ((1 : R ⧸ Ideal.span {π ^ 8}) ⊗ₜ[R] a) = Ideal.Quotient.mk _ (f a) := by
  simp [quotMap]

theorem span_pow_map_le {π : R} {q : Ideal Λ} (hπq : algebraMap R Λ π ∈ q) :
    (Ideal.span {π ^ 8}).map (algebraMap R Λ) ≤ q := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
    SetLike.mem_coe, map_pow]
  exact Ideal.pow_mem_of_mem _ hπq 8 (by norm_num)

theorem isPrime_map_quot {π : R} (q : Ideal Λ) [q.IsPrime] (hπq : algebraMap R Λ π ∈ q) :
    (q.map (Ideal.Quotient.mk ((Ideal.span {π ^ 8}).map (algebraMap R Λ)))).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
    rw [Ideal.mk_ker]; exact span_pow_map_le hπq)

/-- The one-step lifting of Stacks Lemma 9.2 (the case `r = 1`), from Lemma 7.3 (07F0). -/
theorem canBeResolved_of_quot (h6 : StrictlyStandardDesingularizationStatement.{u})
    [IsNoetherianRing R] [Algebra.FinitePresentation R A] (f : A →ₐ[R] Λ) (q : Ideal Λ)
    [q.IsPrime] (π : R) (hR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hΛ : ∀ y : Λ, algebraMap R Λ π ^ 2 * y = 0 → algebraMap R Λ π * y = 0)
    (hss : IsStrictlyStandard R (algebraMap R A π)) (hπq : algebraMap R Λ π ∈ q)
    (hres : letI := isPrime_map_quot q hπq
      CanBeResolved (R ⧸ Ideal.span {π ^ 8}) (quotMap f π) (q.map (Ideal.Quotient.mk _))) :
    CanBeResolved R f q := by
  let := isPrime_map_quot q hπq
  obtain ⟨D, _, _, hD, gD, hD', hgh, hle, hnle⟩ := hres
  let _ : Algebra R D :=
    ((algebraMap (R ⧸ Ideal.span {π ^ 8}) D).comp (algebraMap R (R ⧸ Ideal.span {π ^ 8}))).toAlgebra
  have : IsScalarTower R (R ⧸ Ideal.span {π ^ 8}) D := .of_algebraMap_eq fun _ => rfl
  obtain ⟨B, _, _, hB, g, h, hgh', hsm, hsing⟩ := h6 R A Λ π hR hΛ f hss D
    ((gD.restrictScalars R).comp Algebra.TensorProduct.includeRight) (hD'.restrictScalars R) (by
      ext a
      have := congrArg (fun φ => φ ((1 : R ⧸ Ideal.span {π ^ 8}) ⊗ₜ[R] a)) hgh
      simp only [AlgHom.comp_apply] at this
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
        this, quotMap_tmul, Ideal.Quotient.mkₐ_eq_mk])
  set K := (Ideal.span {π ^ 8}).map (algebraMap R Λ) with hK
  have hKle : K ≤ singularRadical R h := by
    rw [hK, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, map_pow]
    refine Ideal.pow_mem_of_mem _ (Ideal.le_radical ?_) 8 (by norm_num)
    rw [← h.commutes π]
    exact Ideal.mem_map_of_mem h (DimZeroResolutionProof.mem_singularIdeal_of_smooth _ hsm)
  have hcomap : Ideal.comap (Ideal.Quotient.mk K)
      ((singularRadical R h).map (Ideal.Quotient.mk K)) = singularRadical R h := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hKle]
  have hrad : (singularRadical R h).IsRadical := Ideal.radical_isRadical _
  refine ⟨B, inferInstance, inferInstance, hB, g, h, hgh', ?_, ?_⟩
  · -- `h_A ⊆ h_B`
    show ((singularIdeal R A).map f).radical ≤ _
    refine (Ideal.radical_mono ?_).trans hrad
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    have h1 : quotMap f π ((1 : R ⧸ Ideal.span {π ^ 8}) ⊗ₜ[R] a) ∈ singularRadical _ hD' := by
      refine hle (Ideal.le_radical (Ideal.mem_map_of_mem _ ?_))
      exact includeRight_mem_singularIdeal ha
    rw [quotMap_tmul] at h1
    obtain ⟨N, hN⟩ := h1
    have h2 : (Ideal.Quotient.mk K (f a)) ^ N ∈ (singularRadical R h).map (Ideal.Quotient.mk K) :=
      hsing hN
    rw [← map_pow] at h2
    have h3 : f a ^ N ∈ singularRadical R h := by
      rw [← hcomap]
      exact h2
    exact hrad ⟨N, h3⟩
  · -- `h_B ⊄ q`
    intro hBq
    apply hnle
    have h1 : (singularIdeal (R ⧸ Ideal.span {π ^ 8}) D).map hD' ≤ q.map (Ideal.Quotient.mk K) :=
      fun x hx => Ideal.map_mono hBq (hsing hx)
    show ((singularIdeal (R ⧸ Ideal.span {π ^ 8}) D).map hD').radical ≤ _
    exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr h1

end OneStep

section Sequence

/-- The hypothesis at the bottom of the induction in Stacks Lemma 9.2, stated invariantly: for
every presentation of `R/K → Λ/KΛ` by surjections and every prime `Q` over `q`, `Q` is a minimal
prime and property PT holds for `R/K → (Λ/KΛ)_Q`. -/
def BottomCondition (R Λ : Type u) [CommRing R] [CommRing Λ] [Algebra R Λ] (q : Ideal Λ)
    (K : Ideal R) : Prop :=
  ∀ (R₁ Λ₁ : Type u) [CommRing R₁] [CommRing Λ₁] [Algebra R₁ Λ₁] (σ : R →+* R₁) (τ : Λ →+* Λ₁),
    Function.Surjective σ → Function.Surjective τ → RingHom.ker σ = K →
    RingHom.ker τ = K.map (algebraMap R Λ) →
    (∀ x, τ (algebraMap R Λ x) = algebraMap R₁ Λ₁ (σ x)) →
    ∀ (Q : Ideal Λ₁) [Q.IsPrime], Q.comap τ = q →
      Q ∈ minimalPrimes Λ₁ ∧ HasSmoothFactorizations R₁ (Localization.AtPrime Q)

theorem span_image_lt_succ {S : Type*} [CommRing S] {r : ℕ} (g : Fin (r + 1) → S) (i : Fin r) :
    Ideal.span (g '' {j | j < i.succ}) =
      Ideal.span ((fun j => g j.succ) '' {j | j < i}) ⊔ Ideal.span {g 0} := by
  rw [← Ideal.span_union]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    cases j using Fin.cases with
    | zero => exact Or.inr rfl
    | succ j => exact Or.inl ⟨j, Fin.succ_lt_succ_iff.mp hj, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j.succ, Fin.succ_lt_succ_iff.mpr hj, rfl⟩
    · exact ⟨0, Fin.succ_pos i, rfl⟩

theorem span_image_lt_zero {S : Type*} [CommRing S] {r : ℕ} (g : Fin (r + 1) → S) :
    Ideal.span (g '' {j | j < 0}) = ⊥ := by
  simp

theorem span_range_succ {S : Type*} [CommRing S] {r : ℕ} (g : Fin (r + 1) → S) :
    Ideal.span (Set.range g) = Ideal.span (Set.range fun j : Fin r => g j.succ) ⊔
      Ideal.span {g 0} := by
  rw [← Ideal.span_union]
  congr 1
  rw [Fin.range_fin_succ, Set.insert_eq, Set.union_comm]
  rfl

theorem comap_mk_map_mk {S : Type*} [CommRing S] (K I : Ideal S) :
    Ideal.comap (Ideal.Quotient.mk K) (I.map (Ideal.Quotient.mk K)) = I ⊔ K := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]

theorem algebraMap_quot_tensor {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (K : Ideal R) (x : R) :
    algebraMap (R ⧸ K) ((R ⧸ K) ⊗[R] A) (Ideal.Quotient.mk K x) =
      (1 : R ⧸ K) ⊗ₜ[R] algebraMap R A x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

/-- Stacks Lemma 9.2 (07F8), with the bottom problem resolved by Lemma 9.4 in the form of
`DimZeroResolutionStatement`. -/
theorem canBeResolved_of_sequence (h6 : StrictlyStandardDesingularizationStatement.{u})
    (n1 : DimZeroResolutionStatement.{u}) (r : ℕ) :
    ∀ (R A Λ : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing Λ]
      [IsNoetherianRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
      (f : A →ₐ[R] Λ) (q : Ideal Λ) [q.IsPrime] (π : Fin r → R),
      (∀ i, algebraMap R Λ (π i) ∈ q) →
      (∀ i (x : R), π i ^ 2 * x ∈ Ideal.span ((fun j => π j ^ 8) '' {j | j < i}) →
        π i * x ∈ Ideal.span ((fun j => π j ^ 8) '' {j | j < i})) →
      (∀ i (y : Λ), algebraMap R Λ (π i) ^ 2 * y ∈
          Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i}) →
        algebraMap R Λ (π i) * y ∈
          Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i})) →
      (∀ i, IsStrictlyStandard R (algebraMap R A (π i))) →
      BottomCondition R Λ q (Ideal.span (Set.range fun i => π i ^ 8)) →
      CanBeResolved R f q := by
  induction r with
  | zero =>
    intro R A Λ _ _ _ _ _ _ _ _ f q _ π _ _ _ _ hbot
    obtain ⟨hmin, hPT⟩ := hbot R Λ (RingHom.id R) (RingHom.id Λ) Function.surjective_id
      Function.surjective_id
      (by rw [Set.range_eq_empty, Ideal.span_empty]
          exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id)
      (by rw [Set.range_eq_empty, Ideal.span_empty, Ideal.map_bot]
          exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id)
      (fun _ => rfl) q (Ideal.comap_id q)
    by_cases hle : singularRadical R f ≤ q
    · exact n1 R A Λ f q hle hmin hPT
    · exact ⟨A, inferInstance, inferInstance, inferInstance, AlgHom.id R A, f, rfl, le_rfl, hle⟩
  | succ r ih =>
    intro R A Λ _ _ _ _ _ _ _ _ f q _ π hq hR hΛ hss hbot
    set π₀ := π 0
    have hR0 : ∀ x : R, π₀ ^ 2 * x = 0 → π₀ * x = 0 := fun x hx => by
      have := hR 0 x (by rw [span_image_lt_zero, hx]; exact Ideal.zero_mem _)
      rwa [span_image_lt_zero, Ideal.mem_bot] at this
    have hΛ0 : ∀ y : Λ, algebraMap R Λ π₀ ^ 2 * y = 0 → algebraMap R Λ π₀ * y = 0 := fun y hy => by
      have := hΛ 0 y (by rw [span_image_lt_zero, hy]; exact Ideal.zero_mem _)
      rwa [span_image_lt_zero, Ideal.mem_bot] at this
    refine canBeResolved_of_quot h6 f q π₀ hR0 hΛ0 (hss 0) (hq 0) ?_
    let := isPrime_map_quot q (hq 0)
    set K := Ideal.span {π₀ ^ 8} with hK
    set KΛ := K.map (algebraMap R Λ) with hKΛ
    have hKΛ' : KΛ = Ideal.span {algebraMap R Λ π₀ ^ 8} := by
      rw [hKΛ, hK, Ideal.map_span, Set.image_singleton, map_pow]
    have hcompat : ∀ x : R, algebraMap (R ⧸ K) (Λ ⧸ KΛ) (Ideal.Quotient.mk K x) =
        Ideal.Quotient.mk KΛ (algebraMap R Λ x) := fun x => rfl
    refine ih (R ⧸ K) ((R ⧸ K) ⊗[R] A) (Λ ⧸ KΛ) (quotMap f π₀) (q.map (Ideal.Quotient.mk KΛ))
      (fun i => Ideal.Quotient.mk K (π i.succ)) ?_ ?_ ?_ ?_ ?_
    · intro i
      rw [hcompat]
      exact Ideal.mem_map_of_mem _ (hq i.succ)
    · intro i x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hset : (fun j => Ideal.Quotient.mk K (π j.succ) ^ 8) '' {j | j < i} =
          Ideal.Quotient.mk K '' ((fun j => π j.succ ^ 8) '' {j | j < i}) := by
        rw [Set.image_image]; simp only [map_pow]
      have hspan : Ideal.span ((fun j => π j.succ ^ 8) '' {j | j < i}) ⊔ K =
          Ideal.span ((fun j => π j ^ 8) '' {j | j < i.succ}) :=
        (span_image_lt_succ (fun j => π j ^ 8) i).symm
      rw [hset, ← Ideal.map_span, ← map_pow, ← map_mul, ← Ideal.mem_comap, comap_mk_map_mk,
        hspan] at hx
      rw [hset, ← Ideal.map_span, ← map_mul, ← Ideal.mem_comap, comap_mk_map_mk, hspan]
      exact hR i.succ x hx
    · intro i y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hset : (fun j => algebraMap (R ⧸ K) (Λ ⧸ KΛ) (Ideal.Quotient.mk K (π j.succ)) ^ 8) ''
          {j | j < i} = Ideal.Quotient.mk KΛ ''
            ((fun j => algebraMap R Λ (π j.succ) ^ 8) '' {j | j < i}) := by
        rw [Set.image_image]; simp only [hcompat, map_pow]
      have hspan : Ideal.span ((fun j => algebraMap R Λ (π j.succ) ^ 8) '' {j | j < i}) ⊔ KΛ =
          Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i.succ}) := by
        rw [hKΛ']
        exact (span_image_lt_succ (fun j => algebraMap R Λ (π j) ^ 8) i).symm
      rw [hset, ← Ideal.map_span, hcompat, ← map_pow, ← map_mul, ← Ideal.mem_comap,
        comap_mk_map_mk, hspan] at hy
      rw [hset, ← Ideal.map_span, hcompat, ← map_mul, ← Ideal.mem_comap, comap_mk_map_mk, hspan]
      exact hΛ i.succ y hy
    · intro i
      rw [algebraMap_quot_tensor]
      exact (hss i.succ).baseChange
    · intro R₁ Λ₁ _ _ _ σ τ hσ hτ hkσ hkτ hστ Q _ hQ
      have hspanK : Ideal.span (Set.range fun i : Fin r => Ideal.Quotient.mk K (π i.succ) ^ 8) =
          (Ideal.span (Set.range fun i : Fin r => π i.succ ^ 8)).map (Ideal.Quotient.mk K) := by
        rw [Ideal.map_span, ← Set.range_comp]; simp only [Function.comp_def, map_pow]
      have hcomp : (algebraMap (R ⧸ K) (Λ ⧸ KΛ)).comp (Ideal.Quotient.mk K) =
          (Ideal.Quotient.mk KΛ).comp (algebraMap R Λ) := RingHom.ext hcompat
      refine hbot R₁ Λ₁ (σ.comp (Ideal.Quotient.mk K)) (τ.comp (Ideal.Quotient.mk KΛ))
        (hσ.comp Ideal.Quotient.mk_surjective) (hτ.comp Ideal.Quotient.mk_surjective) ?_ ?_
        (fun x => hστ (Ideal.Quotient.mk K x)) Q ?_
      · rw [← RingHom.comap_ker, hkσ, hspanK, comap_mk_map_mk, span_range_succ (fun i => π i ^ 8)]
      · rw [← RingHom.comap_ker, hkτ, hspanK, Ideal.map_map, hcomp, ← Ideal.map_map,
          comap_mk_map_mk, span_range_succ (fun i => π i ^ 8), Ideal.map_sup]
      · rw [← Ideal.comap_comap, hQ, comap_mk_map_mk, sup_eq_left.mpr (span_pow_map_le (hq 0))]

end Sequence

end Langlands.CommutativeAlgebra.Popescu
