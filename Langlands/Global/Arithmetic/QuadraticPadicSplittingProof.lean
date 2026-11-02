import Langlands.Global.Arithmetic.SplitQuadraticPrerequisites
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Actual splitting from two quadratic p-adic embeddings -/

noncomputable section

namespace Langlands.Global

open NumberField IsDedekindDomain
open AdelicFunctoriality
open scoped NumberField TensorProduct AdelicFunctoriality.FiniteExtension

universe u v

-- The two rational-prime helpers were contributed by Worker 60.
private theorem rationalPrime_asIdeal (p : ℕ) [Fact p.Prime] :
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      ⟨p, Fact.out⟩).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  change (Ideal.span {(p : ℤ)}).map
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem natCast_mem_iff_liesOver (p : ℕ) [Fact p.Prime]
    {K : Type u} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K)) :
    (p : 𝓞 K) ∈ q.asIdeal ↔
      q.asIdeal.LiesOver
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
          ⟨p, Fact.out⟩).asIdeal := by
  let r := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
    ⟨p, Fact.out⟩
  have hr : r.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := rationalPrime_asIdeal p
  constructor
  · intro hp
    constructor
    apply r.isMaximal.eq_of_le
    · exact Ideal.comap_ne_top _ q.isPrime.ne_top
    · rw [hr, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      simpa only [map_natCast] using hp
  · intro h
    have := h
    have hp : (p : 𝓞 ℚ) ∈ r.asIdeal := by
      rw [hr]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver q.asIdeal r.asIdeal (p : 𝓞 ℚ)).mp hp

private def tensorPair {K : Type u} {B : Type v} [Field K] [Field B]
    [Algebra ℚ K] [Algebra ℚ B] (φ ψ : K →ₐ[ℚ] B) :
    B ⊗[ℚ] K →ₐ[B] B × B :=
  (Algebra.TensorProduct.lift (AlgHom.id B B) φ (fun _ _ => mul_comm ..)).prod
    (Algebra.TensorProduct.lift (AlgHom.id B B) ψ (fun _ _ => mul_comm ..))

private theorem tensorPair_bijective {K : Type u} {B : Type v} [Field K] [Field B]
    [Algebra ℚ K] [Algebra ℚ B] [FiniteDimensional ℚ K]
    (hdeg : Module.finrank ℚ K = 2) (φ ψ : K →ₐ[ℚ] B) (hne : φ ≠ ψ) :
    Function.Bijective (tensorPair φ ψ) := by
  classical
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
  have hdelta : φ x - ψ x ≠ 0 := sub_ne_zero.mpr hx
  have hsurj : Function.Surjective (tensorPair φ ψ) := by
    rintro ⟨s, t⟩
    let c : B := (s - t) / (φ x - ψ x)
    refine ⟨(s - c * φ x) ⊗ₜ[ℚ] (1 : K) + c ⊗ₜ[ℚ] x, ?_⟩
    apply Prod.ext
    · change (s - c * φ x) * φ 1 + c * φ x = s
      rw [map_one, mul_one]
      ring
    · change (s - c * φ x) * ψ 1 + c * ψ x = t
      rw [map_one, mul_one]
      dsimp [c]
      field_simp
      ring
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (tensorPair φ ψ).toLinearMap hsurj
  simp [Module.finrank_prod, hdeg]

private theorem two_actual_places {K : Type u} [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 ℚ)) (hdeg : Module.finrank ℚ K = 2)
    (φ ψ : K →ₐ[ℚ] r.adicCompletion ℚ) (hne : φ ≠ ψ) :
    ∃ q₁ q₂ : FinitePlacesAbove K r, q₁ ≠ q₂ := by
  classical
  let a := AlgEquiv.ofBijective (tensorPair φ ψ) (tensorPair_bijective hdeg φ ψ hne)
  let b := AlgEquiv.ofBijective (finiteTensorMap (L := K) r)
    ((completedTensorComparison ℚ K).1 r)
  let g := a.symm.trans b
  let e := g ((1, 0) : r.adicCompletion ℚ × r.adicCompletion ℚ)
  have he : e * e = e := by
    dsimp [e]
    rw [← map_mul]
    simp
  have hzero : e ≠ 0 := by
    intro h
    have h' : ((1, 0) : r.adicCompletion ℚ × r.adicCompletion ℚ) = 0 :=
      g.injective (h.trans (map_zero g).symm)
    exact one_ne_zero (congrArg Prod.fst h')
  have hone : e ≠ 1 := by
    intro h
    have h' : ((1, 0) : r.adicCompletion ℚ × r.adicCompletion ℚ) = 1 :=
      g.injective (h.trans (map_one g).symm)
    exact zero_ne_one (congrArg Prod.snd h')
  have hexzero : ∃ i, e i ≠ 0 := by
    by_contra! h
    exact hzero (funext h)
  have hexone : ∃ j, e j ≠ 1 := by
    by_contra! h
    exact hone (funext h)
  obtain ⟨i, hi⟩ := hexzero
  obtain ⟨j, hj⟩ := hexone
  refine ⟨i, j, ?_⟩
  intro hij
  subst j
  have hm : e i * (e i - 1) = 0 := by
    rw [mul_sub, mul_one]
    exact sub_eq_zero.mpr (congrFun he i)
  exact hj (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hi))

private theorem two_places_degree_one {K : Type u} [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 ℚ)) (hdeg : Module.finrank ℚ K = 2)
    (q₁ q₂ : FinitePlacesAbove K r) (hne : q₁ ≠ q₂) :
    (∀ q : FinitePlacesAbove K r, q = q₁ ∨ q = q₂) ∧
      Module.finrank (r.adicCompletion ℚ) (q₁.1.adicCompletion K) = 1 ∧
      Module.finrank (r.adicCompletion ℚ) (q₂.1.adicCompletion K) = 1 := by
  classical
  let d : FinitePlacesAbove K r → ℕ := fun q =>
    Module.finrank (r.adicCompletion ℚ) (q.1.adicCompletion K)
  have hpos : ∀ q, 1 ≤ d q := fun q =>
    Nat.succ_le_of_lt (Module.finrank_pos :
      0 < Module.finrank (r.adicCompletion ℚ) (q.1.adicCompletion K))
  have hsum : ∑ q, d q ≤ 2 := by
    simpa [d, hdeg] using (finiteLocalDegree_sum_le (L := K) r)
  have hpair : d q₁ + d q₂ ≤ 2 := by
    calc
      _ = ∑ q ∈ ({q₁, q₂} : Finset (FinitePlacesAbove K r)), d q := by
        simp [hne]
      _ ≤ ∑ q, d q := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 2 := hsum
  have hd₁ := hpos q₁
  have hd₂ := hpos q₂
  refine ⟨?_, ?_, ?_⟩
  · intro q
    by_contra! h
    have htriple : d q + (d q₁ + d q₂) ≤ 2 := by
      calc
        _ = ∑ x ∈ ({q, q₁, q₂} : Finset (FinitePlacesAbove K r)), d x := by
          simp [h.1, h.2, hne]
        _ ≤ ∑ x, d x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ ≤ 2 := hsum
    have hd := hpos q
    omega
  · change d q₁ = 1
    omega
  · change d q₂ = 1
    omega

private theorem completion_degree_one {K : Type u} [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 ℚ)) (q : FinitePlacesAbove K r)
    (h : Module.finrank (r.adicCompletion ℚ) (q.1.adicCompletion K) = 1) :
    ∃ e : q.1.adicCompletion K ≃+* r.adicCompletion ℚ,
      Continuous e ∧ Continuous e.symm := by
  let _ : NontriviallyNormedField (r.adicCompletion ℚ) :=
    Valued.toNontriviallyNormedField (r.adicCompletion ℚ) (WithZero (Multiplicative ℤ))
  let a : r.adicCompletion ℚ ≃ₐ[r.adicCompletion ℚ] q.1.adicCompletion K :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)
  have ha : Continuous a := by
    change Continuous (FiniteExtension.completionMap r q.1)
    exact FiniteExtension.continuous_completionMap r q.1
  have ha' : Continuous a.symm := by
    let f : q.1.adicCompletion K →ₗ[r.adicCompletion ℚ] r.adicCompletion ℚ :=
      a.symm.toLinearEquiv
    change Continuous f
    exact LinearMap.continuous_of_finiteDimensional f
  exact ⟨a.toRingEquiv.symm, ha', ha⟩

/-- Two distinct rational embeddings of a quadratic number field into `ℚ_p`
give two actual primes and continuous equivalences of both completions with `ℚ_p`. -/
theorem quadraticPadicSplitting : QuadraticPadicSplittingStatement.{u} := by
  classical
  intro p hp K _ _ hdeg ⟨φ, ψ, hne⟩
  let r : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩
  let e : Padic p ≃A[ℚ] r.adicCompletion ℚ :=
    Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩
  let φ' : K →ₐ[ℚ] r.adicCompletion ℚ := e.toAlgEquiv.toAlgHom.comp φ
  let ψ' : K →ₐ[ℚ] r.adicCompletion ℚ := e.toAlgEquiv.toAlgHom.comp ψ
  have hne' : φ' ≠ ψ' := by
    intro h
    apply hne
    ext x
    exact e.injective (DFunLike.congr_fun h x)
  obtain ⟨q₁, q₂, hq⟩ := two_actual_places r hdeg φ' ψ' hne'
  obtain ⟨hex, hd₁, hd₂⟩ := two_places_degree_one r hdeg q₁ q₂ hq
  obtain ⟨a₁, ha₁, ha₁'⟩ := completion_degree_one r q₁ hd₁
  obtain ⟨a₂, ha₂, ha₂'⟩ := completion_degree_one r q₂ hd₂
  let f₁ := a₁.trans e.symm.toAlgEquiv.toRingEquiv
  let f₂ := a₂.trans e.symm.toAlgEquiv.toRingEquiv
  refine ⟨q₁.1, q₂.1, f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hq (Subtype.ext h)
  · exact (natCast_mem_iff_liesOver p q₁.1).mpr q₁.2
  · exact (natCast_mem_iff_liesOver p q₂.1).mpr q₂.2
  · intro q h
    let q' : FinitePlacesAbove K r := ⟨q, (natCast_mem_iff_liesOver p q).mp h⟩
    exact (hex q').elim
      (fun h => Or.inl (congrArg Subtype.val h))
      (fun h => Or.inr (congrArg Subtype.val h))
  · exact e.symm.continuous.comp ha₁
  · exact ha₁'.comp e.continuous
  · exact e.symm.continuous.comp ha₂
  · exact ha₂'.comp e.continuous

end Langlands.Global
