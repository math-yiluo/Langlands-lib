import Langlands.CommutativeAlgebra.Popescu.SingularIdealFactorizationStatement

/-! # Proof of Stacks Lemma 16.2.8 (07EU) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

namespace SingularIdealFactorization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If `a` lies in the singular ideal of a finitely presented algebra, then `A_a` is formally
smooth over `R`. -/
lemma formallySmooth_away_of_mem_singularIdeal [Algebra.FinitePresentation R A] {a : A}
    (ha : a ∈ singularIdeal R A) : Algebra.FormallySmooth R (Localization.Away a) := by
  rw [← Algebra.basicOpen_subset_smoothLocus_iff]
  intro p hp
  by_contra h
  exact (PrimeSpectrum.mem_basicOpen a p).mp hp
    ((PrimeSpectrum.mem_vanishingIdeal _ _).mp ha p h)

variable {n : ℕ}

/-- The relation `∑ aᵢ Xᵢ - 1`. -/
noncomputable def unitRel (a : Fin n → A) : MvPolynomial (Fin n) A :=
  ∑ i, C (a i) * X i - 1

/-- The algebra `A[X₁, …, Xₙ]/(∑ aᵢ Xᵢ - 1)`. -/
abbrev UnitHyp (a : Fin n → A) : Type _ :=
  MvPolynomial (Fin n) A ⧸ Ideal.span {unitRel a}

lemma sum_eq_one (a : Fin n → A) :
    ∑ i, algebraMap A (UnitHyp a) (a i) * Ideal.Quotient.mk _ (X i) = 1 := by
  have h : Ideal.Quotient.mk (Ideal.span {unitRel a}) (∑ i, C (a i) * X i - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [map_sub, map_sum, map_one, sub_eq_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  rfl

/-- `A[X₁, …, Xₙ]/(∑ aᵢ Xᵢ - 1)` is formally smooth over `A`. -/
lemma formallySmooth_unitHyp (a : Fin n → A) : Algebra.FormallySmooth A (UnitHyp a) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ J hJ φ => ?_
  choose c hc using fun i => Ideal.Quotient.mk_surjective (φ (Ideal.Quotient.mk _ (X i)))
  set e : C := ∑ i, algebraMap A C (a i) * c i - 1 with he
  have heJ : e ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 := congrArg φ (sum_eq_one a)
    rw [map_sum, map_one] at h1
    rw [he, map_sub, map_sum, map_one, ← h1, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hc, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]
  have he2 : e * e = 0 := by
    have : e * e ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul heJ heJ
    rw [hJ] at this
    exact (Submodule.mem_bot _).mp this
  let ψ₀ : MvPolynomial (Fin n) A →ₐ[A] C := aeval fun i => c i * (1 - e)
  have hψ₀ : ψ₀ (unitRel a) = 0 := by
    have : ∑ i, algebraMap A C (a i) * (c i * (1 - e)) = (e + 1) * (1 - e) := by
      rw [he, sub_add_cancel, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    simp only [ψ₀, unitRel, map_sub, map_sum, map_mul, aeval_C, aeval_X, map_one, this]
    linear_combination (-1 : C) * he2
  let ψ : UnitHyp a →ₐ[A] C := Ideal.Quotient.liftₐ _ ψ₀ fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hψ₀, mul_zero]
  refine ⟨ψ, ?_⟩
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr heJ
  show Ideal.Quotient.mk J (aeval (fun i => c i * (1 - e)) (X i)) =
    φ (Ideal.Quotient.mk _ (X i))
  rw [← hc, aeval_X, map_mul, map_sub, map_one, this, sub_zero, mul_one]

section FinitePresentation

variable [Algebra.FinitePresentation R A]

instance finitePresentation_unitHyp (a : Fin n → A) :
    Algebra.FinitePresentation R (UnitHyp a) :=
  Algebra.FinitePresentation.quotient ⟨{unitRel a}, by rw [Finset.coe_singleton]⟩

/-- If `aᵢ ∈ H_{A/R}`, then the localization of `A[X]/(∑ aⱼ Xⱼ - 1)` at `aᵢ` is formally smooth
over `R`. -/
lemma formallySmooth_away_unitHyp (a : Fin n → A) (i : Fin n) (hi : a i ∈ singularIdeal R A) :
    Algebra.FormallySmooth R (Localization.Away (algebraMap A (UnitHyp a) (a i))) := by
  let M := Submonoid.powers (a i)
  have : IsLocalization (Algebra.algebraMapSubmonoid (UnitHyp a) M)
      (Localization.Away (algebraMap A (UnitHyp a) (a i))) := by
    show IsLocalization ((Submonoid.powers (a i)).map (algebraMap A (UnitHyp a))) _
    rw [Submonoid.map_powers]
    exact Localization.isLocalization
  let : Algebra (Localization.Away (a i)) (Localization.Away (algebraMap A (UnitHyp a) (a i))) :=
    localizationAlgebra M (UnitHyp a)
  have : IsScalarTower A (Localization.Away (a i))
      (Localization.Away (algebraMap A (UnitHyp a) (a i))) :=
    isScalarTower_localizationAlgebra M (UnitHyp a)
  have : Algebra.FormallySmooth A (UnitHyp a) := formallySmooth_unitHyp a
  have : Algebra.FormallySmooth (Localization.Away (a i))
      (Localization.Away (algebraMap A (UnitHyp a) (a i))) :=
    Algebra.FormallySmooth.localization_map M (A := UnitHyp a)
  have : Algebra.FormallySmooth R (Localization.Away (a i)) :=
    formallySmooth_away_of_mem_singularIdeal hi
  have : IsScalarTower R (Localization.Away (a i))
      (Localization.Away (algebraMap A (UnitHyp a) (a i))) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away (a i)),
      ← IsScalarTower.algebraMap_apply A (Localization.Away (a i)),
      ← IsScalarTower.algebraMap_apply R A]
  exact Algebra.FormallySmooth.comp R (Localization.Away (a i)) _

/-- If every `aᵢ` lies in `H_{A/R}`, then `A[X]/(∑ aᵢ Xᵢ - 1)` is smooth over `R`. -/
lemma smooth_unitHyp (a : Fin n → A) (ha : ∀ i, a i ∈ singularIdeal R A) :
    Algebra.Smooth R (UnitHyp a) := by
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro P
  have : ∃ i, algebraMap A (UnitHyp a) (a i) ∉ P.asIdeal := by
    by_contra! h
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← sum_eq_one a]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (h i)
  obtain ⟨i, hi⟩ := this
  exact (Algebra.basicOpen_subset_smoothLocus_iff.mpr (formallySmooth_away_unitHyp a i (ha i)))
    ((PrimeSpectrum.mem_basicOpen _ _).mpr hi)

end FinitePresentation

end SingularIdealFactorization

open SingularIdealFactorization in
/-- Stacks Lemma 16.2.8 (07EU). -/
theorem singularIdealFactorization : SingularIdealFactorizationStatement.{u} := by
  intro R A Λ _ _ _ _ _ _ f hf
  have h1 : (1 : Λ) ∈ (singularIdeal R A).map f := by rw [hf]; trivial
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at h1
  obtain ⟨n, μ, y, hy⟩ := h1
  choose a ha hfa using fun i => (y i).2
  let : Algebra A Λ := f.toRingHom.toAlgebra
  have : IsScalarTower R A Λ := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have hrel : aeval μ (unitRel a) = 0 := by
    simp only [unitRel, map_sub, map_sum, map_mul, aeval_C, aeval_X, map_one]
    rw [sub_eq_zero, ← hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hfa i, mul_comm]
    rfl
  let h₀ : UnitHyp a →ₐ[A] Λ := Ideal.Quotient.liftₐ _ (aeval μ) fun x hx => by
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hrel, mul_zero]
  refine ⟨UnitHyp a, inferInstance, inferInstance, smooth_unitHyp a ha,
    IsScalarTower.toAlgHom R A (UnitHyp a), h₀.restrictScalars R, ?_⟩
  ext x
  exact h₀.commutes x

end Langlands.CommutativeAlgebra.Popescu
