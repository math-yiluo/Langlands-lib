import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Integral points detect divisibility on smooth algebras

Over a Henselian local ring with algebraically closed residue field, an element of a smooth
algebra that lies in the maximal ideal at every integral point lies in the extended maximal
ideal. Over a discrete valuation ring this gives divisibility from pointwise divisibility. -/

noncomputable section

universe u v w

open TensorProduct

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section Field

variable {k : Type u} {T : Type v} [Field k] [IsAlgClosed k] [CommRing T] [Algebra k T]
  [Algebra.FiniteType k T] [IsReduced T]

/-- A nonzero element of a reduced finite-type algebra over an algebraically closed field is
nonzero at some rational point. -/
theorem exists_algHom_ne_zero {t : T} (ht : t ≠ 0) : ∃ φ : T →ₐ[k] k, φ t ≠ 0 := by
  have : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal T).IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [Ideal.mem_bot] at hn ⊢
    exact IsReduced.eq_zero x ⟨n, hn⟩
  have hjac : (⊥ : Ideal T).jacobson = ⊥ := IsJacobsonRing.out ‹_› hrad
  have hnot : t ∉ (⊥ : Ideal T).jacobson := by
    rw [hjac, Ideal.mem_bot]
    exact ht
  rw [Ideal.jacobson, Submodule.mem_sInf] at hnot
  push Not at hnot
  obtain ⟨J, ⟨-, hJ⟩, htJ⟩ := hnot
  let := Ideal.Quotient.field J
  have : Module.Finite k (T ⧸ J) := finite_of_finite_type_of_isJacobsonRing k (T ⧸ J)
  have : Algebra.IsIntegral k (T ⧸ J) := Algebra.IsIntegral.of_finite k _
  let e : k ≃ₐ[k] T ⧸ J := AlgEquiv.ofBijective (Algebra.ofId k (T ⧸ J))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := T ⧸ J))
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k J), ?_⟩
  intro h
  apply htJ
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h' : e.symm (Ideal.Quotient.mk J t) = 0 := h
  rw [map_eq_zero_iff _ e.symm.injective] at h'
  exact h'

end Field

section Henselian

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)]
  {A : Type u} [CommRing A] [Algebra R A] [Algebra.Smooth R A]

/-- **Key lemma.** On a smooth algebra over a Henselian local ring with algebraically closed
residue field, an element lying in the maximal ideal at every integral point lies in the
extension of the maximal ideal. -/
theorem mem_map_maximalIdeal_of_forall {a : A}
    (ha : ∀ σ : A →ₐ[R] R, σ a ∈ IsLocalRing.maximalIdeal R) :
    a ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
  set k := IsLocalRing.ResidueField R
  set 𝔪 := IsLocalRing.maximalIdeal R
  have hk : Function.Surjective (algebraMap R k) := IsLocalRing.residue_surjective
  -- the special fibre `k ⊗[R] A` is reduced and of finite type over `k`
  have : IsReduced (k ⊗[R] A) :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain k (k ⊗[R] A)
  by_contra hmem
  have hne : (1 : k) ⊗ₜ[R] a ≠ 0 := by
    intro h0
    apply hmem
    have he := Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A 𝔪 a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A 𝔪)
        (Ideal.Quotient.mk (𝔪.map (algebraMap R A)) a) = 0 := by
      rw [he]
      exact h0
    exact (map_eq_zero_iff _ (AlgEquiv.injective _)).mp this
  obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero (k := k) hne
  let ψ : A →ₐ[R] k := (φ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨σ, hσ⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_smooth hk ψ
  have h1 : algebraMap R k (σ a) = φ ((1 : k) ⊗ₜ[R] a) := by
    have := congrArg (fun f : A →ₐ[R] k => f a) hσ
    exact this
  apply hφ
  rw [← h1]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr (ha σ)

/-- Divisibility by a power of a uniformiser can be tested at integral points. -/
theorem dvd_of_forall_dvd_pow {ϖ : R} (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [IsDomain R] (hϖ0 : ϖ ≠ 0) :
    ∀ (n : ℕ) (g : A), (∀ σ : A →ₐ[R] R, ϖ ^ n ∣ σ g) → algebraMap R A (ϖ ^ n) ∣ g := by
  intro n
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    have hmem : g ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
      apply mem_map_maximalIdeal_of_forall
      intro σ
      rw [hϖ, Ideal.mem_span_singleton]
      exact (dvd_pow_self ϖ n.succ_ne_zero).trans (hg σ)
    rw [hϖ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem
    obtain ⟨g', rfl⟩ := hmem
    have hg' : ∀ σ : A →ₐ[R] R, ϖ ^ n ∣ σ g' := by
      intro σ
      have := hg σ
      rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, pow_succ',
        mul_dvd_mul_iff_left hϖ0] at this
      exact this
    obtain ⟨c, hc⟩ := ih g' hg'
    refine ⟨c, ?_⟩
    rw [hc, pow_succ', map_mul, mul_assoc]

end Henselian

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {A : Type u} [CommRing A] [Algebra R A] [Algebra.Smooth R A]

/-- Divisibility by a nonzero element of a Henselian discrete valuation ring with
algebraically closed residue field can be tested at integral points of a smooth algebra. -/
theorem dvd_of_forall_dvd {s : R} (hs : s ≠ 0) {g : A}
    (hg : ∀ σ : A →ₐ[R] R, s ∣ σ g) : algebraMap R A s ∣ g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hg' : ∀ σ : A →ₐ[R] R, ϖ ^ n ∣ σ g := fun σ =>
    (Dvd.intro_left _ rfl).trans (hg σ)
  obtain ⟨c, hc⟩ := dvd_of_forall_dvd_pow hmax hϖ.ne_zero n g hg'
  refine ⟨algebraMap R A (↑u⁻¹ : R) * c, ?_⟩
  have hu : algebraMap R A (u : R) * algebraMap R A (↑u⁻¹ : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hc, map_mul]
  linear_combination (-(algebraMap R A (ϖ ^ n) * c)) * hu

end DVR

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
