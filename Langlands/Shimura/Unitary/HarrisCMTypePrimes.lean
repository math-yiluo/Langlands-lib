import Langlands.Global.CMType
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.Integral

/-!
# Primes cut out by complex embeddings and Harris's set `Φ_p`

An embedding `φ` of a number field `K` into a valued field `C` determines the
prime ideal of algebraic integers `x` with `v (φ x) < 1`. When `C` is
algebraically closed, every prime above the prime of an embedding of a
subfield comes from an extension of that embedding.

For a ring homomorphism `θ : ℂ →+* Q̄_p`, a complex embedding `φ` of `K` gives
the prime `harrisPrime p θ φ` above `p`. The set `Φ_p` of Harris (1999) §4
attached to a CM type `Φ` is the image of `Φ`. For Harris's type, induced from
an embedding `τ` of an imaginary quadratic subfield, `Φ_p` is the set of primes
above the prime `u` of `τ`, and it is disjoint from the conjugate set exactly
when `p` splits.
-/

noncomputable section

namespace Langlands.Shimura

open NumberField IsDedekindDomain

universe u v w

section EmbeddingIdeal

variable {C : Type u} [Field C] {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation C Γ₀)
variable {K : Type v} [Field K]

/-- Algebraic integers have valuation at most one under every embedding. -/
theorem valuation_embedding_le_one (φ : K →+* C) (x : 𝓞 K) :
    v (φ (algebraMap (𝓞 K) K x)) ≤ 1 := by
  have hx : IsIntegral ℤ (φ (algebraMap (𝓞 K) K x)) :=
    (RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hx.tower_top

/-- The ideal of algebraic integers whose image under `φ` has valuation
less than one. -/
def embeddingIdeal (φ : K →+* C) : Ideal (𝓞 K) where
  carrier := {x | v (φ (algebraMap (𝓞 K) K x)) < 1}
  add_mem' {a b} ha hb := by
    change v (φ (algebraMap (𝓞 K) K (a + b))) < 1
    rw [map_add, map_add]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change v (φ (algebraMap (𝓞 K) K (c * x))) < 1
    rw [map_mul, map_mul, map_mul]
    exact mul_lt_of_le_one_of_lt (valuation_embedding_le_one v φ c) hx

@[simp]
theorem mem_embeddingIdeal (φ : K →+* C) (x : 𝓞 K) :
    x ∈ embeddingIdeal v φ ↔ v (φ (algebraMap (𝓞 K) K x)) < 1 := Iff.rfl

instance embeddingIdeal_isPrime (φ : K →+* C) : (embeddingIdeal v φ).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : 𝓞 K) ∈ embeddingIdeal v φ := h ▸ Submodule.mem_top
    simp at h1
  · rw [mem_embeddingIdeal, map_mul, map_mul, map_mul] at hxy
    rcases (valuation_embedding_le_one v φ x).lt_or_eq with hx | hx
    · exact Or.inl hx
    · right
      rw [hx, one_mul] at hxy
      exact hxy

theorem natCast_mem_embeddingIdeal (φ : K →+* C) {p : ℕ} (hp : v (p : C) < 1) :
    (p : 𝓞 K) ∈ embeddingIdeal v φ := by
  simpa using hp

variable {F : Type*} [Field F] [Algebra F K]

/-- Contracting the prime of an embedding gives the prime of its restriction. -/
theorem under_embeddingIdeal (φ : K →+* C) :
    (embeddingIdeal v φ).under (𝓞 F) = embeddingIdeal v (φ.comp (algebraMap F K)) := by
  ext x
  simp only [Ideal.mem_comap, mem_embeddingIdeal, RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F K]

instance liesOver_embeddingIdeal (φ : K →+* C) :
    (embeddingIdeal v φ).LiesOver (embeddingIdeal v (φ.comp (algebraMap F K))) :=
  ⟨(under_embeddingIdeal v φ).symm⟩

variable [NumberField F] [NumberField K]

theorem embeddingIdeal_ne_bot (φ : K →+* C) {p : ℕ} (hp0 : p ≠ 0) (hp : v (p : C) < 1) :
    embeddingIdeal v φ ≠ ⊥ := by
  intro h
  have hmem := natCast_mem_embeddingIdeal v φ hp
  rw [h, Ideal.mem_bot] at hmem
  exact hp0 (by exact_mod_cast hmem)

/-- The finite place of `K` determined by an embedding into a field with a
valuation of positive residue characteristic dividing `p`. -/
def embeddingPrime (φ : K →+* C) {p : ℕ} (hp0 : p ≠ 0) (hp : v (p : C) < 1) :
    HeightOneSpectrum (𝓞 K) :=
  ⟨embeddingIdeal v φ, inferInstance, embeddingIdeal_ne_bot v φ hp0 hp⟩

@[simp]
theorem embeddingPrime_asIdeal (φ : K →+* C) {p : ℕ} (hp0 : p ≠ 0) (hp : v (p : C) < 1) :
    (embeddingPrime v φ hp0 hp).asIdeal = embeddingIdeal v φ := rfl

/-- Galois conjugation of the prime of an embedding. -/
theorem comap_galRestrict_embeddingIdeal {M : Type*} [Field M] [NumberField M] [Algebra F M]
    (ψ : M →+* C) (g : Gal(M/F)) :
    (embeddingIdeal v ψ).comap (galRestrict (𝓞 F) F M (𝓞 M) g) =
      embeddingIdeal v (ψ.comp (g : M →+* M)) := by
  ext x
  simp only [Ideal.mem_comap, mem_embeddingIdeal, RingHom.coe_comp, Function.comp_apply,
    algebraMap_galRestrict_apply]
  rfl

variable [IsAlgClosed C]

/-- Every prime above the prime of `χ` is the prime of an extension of `χ`. -/
theorem exists_embedding_of_liesOver (χ : F →+* C) (w : Ideal (𝓞 K)) [w.IsPrime]
    [w.LiesOver (embeddingIdeal v χ)] :
    ∃ φ : K →+* C, φ.comp (algebraMap F K) = χ ∧ w = embeddingIdeal v φ := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosure F L := ⟨AlgebraicClosure.isAlgClosed K, Algebra.IsAlgebraic.trans F K L⟩
  let M := IntermediateField.normalClosure F K L
  have : IsGalois F M := IsGalois.mk
  have : FiniteDimensional ℚ M := Module.Finite.trans F M
  have : NumberField M := ⟨⟩
  let : Algebra F C := χ.toAlgebra
  let Φ : M →ₐ[F] C := IsAlgClosed.lift
  obtain ⟨W, -, hW, hWw⟩ := Ideal.exists_ideal_over_prime_of_isIntegral w (⊥ : Ideal (𝓞 M))
    (by simp [Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 M))])
  have hΦ : (Φ : M →+* C).comp (algebraMap F M) = χ := by
    ext x
    exact Φ.commutes x
  have h1 : embeddingIdeal v (Φ : M →+* C) ∈ (embeddingIdeal v χ).primesOver (𝓞 M) :=
    ⟨inferInstance, ⟨by rw [under_embeddingIdeal, hΦ]⟩⟩
  have h2 : W ∈ (embeddingIdeal v χ).primesOver (𝓞 M) := by
    refine ⟨hW, ⟨?_⟩⟩
    rw [← Ideal.under_under (B := 𝓞 K), hWw]
    exact Ideal.LiesOver.over
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F M (𝓞 M) h1 h2
  refine ⟨(Φ : M →+* C).comp ((σ : M →+* M).comp (algebraMap K M)), ?_, ?_⟩
  · ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply]
    change Φ (σ (algebraMap F M x)) = χ x
    rw [σ.commutes]
    exact Φ.commutes x
  · rw [← hWw, ← hσ, comap_galRestrict_embeddingIdeal, under_embeddingIdeal]
    rfl

/-- In `𝓞 ℚ` at most one prime ideal contains a given prime number. -/
theorem rat_prime_eq_of_natCast_mem {p : ℕ} (hp : p.Prime) {P Q : Ideal (𝓞 ℚ)} [P.IsPrime]
    [Q.IsPrime] (hP : (p : 𝓞 ℚ) ∈ P) (hQ : (p : 𝓞 ℚ) ∈ Q) : P = Q := by
  let e := Rat.ringOfIntegersEquiv
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  let J : Ideal (𝓞 ℚ) := (Ideal.span {(p : ℤ)}).comap e
  have hJ : J.IsMaximal := Ideal.comap_isMaximal_of_surjective e e.surjective
  have hle : ∀ I : Ideal (𝓞 ℚ), I.IsPrime → (p : 𝓞 ℚ) ∈ I → J = I := by
    intro I hI hpI
    refine hJ.eq_of_le hI.ne_top fun x hx => ?_
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hx)
    have hx' : x = e.symm a * (p : 𝓞 ℚ) := by
      apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, ha]
    rw [hx']
    exact I.mul_mem_left _ hpI
  exact (hle P inferInstance hP).symm.trans (hle Q inferInstance hQ)

/-- Every prime of `K` above `p` is the prime of a complex embedding. -/
theorem exists_embedding_of_natCast_mem [CharZero C] {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) < 1) (w : Ideal (𝓞 K)) [w.IsPrime] (hw : (p : 𝓞 K) ∈ w) :
    ∃ φ : K →+* C, w = embeddingIdeal v φ := by
  have : w.LiesOver (embeddingIdeal v (algebraMap ℚ C)) := by
    refine ⟨rat_prime_eq_of_natCast_mem hp ?_ ?_⟩
    · exact natCast_mem_embeddingIdeal v _ hv
    · simpa [Ideal.under, Ideal.mem_comap] using hw
  obtain ⟨φ, -, h⟩ := exists_embedding_of_liesOver v (algebraMap ℚ C) w
  exact ⟨φ, h⟩

end EmbeddingIdeal

section Harris

open Global ComplexConjugate

variable (p : ℕ) [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)

/-- The valuation of `ℂ` transported from `Q̄_p` along an embedding `θ : ℂ → Q̄_p`. -/
def harrisValuation : Valuation ℂ NNReal :=
  (PadicAlgCl.valued p).v.comap θ

theorem harrisValuation_apply (z : ℂ) :
    harrisValuation p θ z = (PadicAlgCl.valued p).v (θ z) := rfl

theorem harrisValuation_natCast_lt_one : harrisValuation p θ (p : ℂ) < 1 := by
  rw [harrisValuation_apply, map_natCast, PadicAlgCl.valuation_p p]
  have h1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact (div_lt_one (zero_lt_one.trans h1)).mpr h1

variable {K : Type v} [Field K] [NumberField K]

/-- The finite place of `K` above `p` induced by a complex embedding through `θ`. -/
def harrisPrime (φ : K →+* ℂ) : HeightOneSpectrum (𝓞 K) :=
  embeddingPrime (harrisValuation p θ) φ (Fact.out : p.Prime).ne_zero
    (harrisValuation_natCast_lt_one p θ)

theorem harrisPrime_asIdeal (φ : K →+* ℂ) :
    (harrisPrime p θ φ).asIdeal = embeddingIdeal (harrisValuation p θ) φ := rfl

theorem natCast_mem_harrisPrime (φ : K →+* ℂ) : (p : 𝓞 K) ∈ (harrisPrime p θ φ).asIdeal :=
  natCast_mem_embeddingIdeal _ φ (harrisValuation_natCast_lt_one p θ)

/-- The primes of `K` above `p` are exactly the primes of complex embeddings. -/
theorem range_harrisPrime :
    Set.range (harrisPrime p θ (K := K)) = {w | (p : 𝓞 K) ∈ w.asIdeal} := by
  ext w
  constructor
  · rintro ⟨φ, rfl⟩
    exact natCast_mem_harrisPrime p θ φ
  · intro hw
    obtain ⟨φ, h⟩ := exists_embedding_of_natCast_mem (harrisValuation p θ) Fact.out
      (harrisValuation_natCast_lt_one p θ) w.asIdeal hw
    exact ⟨φ, HeightOneSpectrum.ext h.symm⟩

variable {F : Type*} [Field F] [NumberField F] [Algebra F K]

instance liesOver_harrisPrime (φ : K →+* ℂ) :
    (harrisPrime p θ φ).asIdeal.LiesOver (harrisPrime p θ (φ.comp (algebraMap F K))).asIdeal :=
  liesOver_embeddingIdeal _ φ

/-- The primes of `K` above the prime of `τ` are the primes of the embeddings
extending `τ`. -/
theorem harrisPrime_liesOver_iff (τ : F →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) :
    w.asIdeal.LiesOver (harrisPrime p θ τ).asIdeal ↔
      ∃ φ : K →+* ℂ, φ.comp (algebraMap F K) = τ ∧ harrisPrime p θ φ = w := by
  constructor
  · intro hw
    have : w.asIdeal.LiesOver (embeddingIdeal (harrisValuation p θ) τ) := hw
    obtain ⟨φ, hφ, h⟩ := exists_embedding_of_liesOver (harrisValuation p θ) τ w.asIdeal
    exact ⟨φ, hφ, HeightOneSpectrum.ext h.symm⟩
  · rintro ⟨φ, rfl, rfl⟩
    exact liesOver_harrisPrime p θ φ

/-- The set `Φ_p` of primes of `K` above `p` determined by a CM type `Φ`. -/
def cmTypePrimes [IsCMField K] (Φ : CMType K) : Set (HeightOneSpectrum (𝓞 K)) :=
  harrisPrime p θ '' (Φ : Set (K →+* ℂ))

theorem mem_cmTypePrimes [IsCMField K] (Φ : CMType K) (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ cmTypePrimes p θ Φ ↔ ∃ φ ∈ Φ, harrisPrime p θ φ = w := Iff.rfl

/-- The primes of `Φ` and of its conjugate exhaust the primes above `p`. -/
theorem cmTypePrimes_union_conjugate [IsCMField K] (Φ : CMType K) :
    cmTypePrimes p θ Φ ∪ cmTypePrimes p θ Φ.conjugate = {w | (p : 𝓞 K) ∈ w.asIdeal} := by
  rw [← range_harrisPrime, cmTypePrimes, cmTypePrimes, ← Set.image_union, ← Set.image_univ]
  congr 1
  ext σ
  by_cases h : σ ∈ Φ <;> simp [h]

section Conjugation

variable [IsCMField K]

/-- Complex conjugation of a CM field, acting on its finite places. -/
def conjPrime (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.comap (IsCMField.ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K)
    (IsCMField.ringOfIntegersComplexConj K).surjective w

theorem conjPrime_asIdeal (w : HeightOneSpectrum (𝓞 K)) :
    (conjPrime w).asIdeal =
      w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K) := rfl

/-- Complex conjugation of finite places is an involution. -/
theorem conjPrime_conjPrime (w : HeightOneSpectrum (𝓞 K)) : conjPrime (conjPrime w) = w := by
  apply HeightOneSpectrum.ext
  ext x
  have hx :
      IsCMField.ringOfIntegersComplexConj K (IsCMField.ringOfIntegersComplexConj K x) = x := by
    ext
    simp
  simp only [conjPrime_asIdeal, Ideal.mem_comap, RingHom.coe_coe, hx]

/-- The prime of the conjugate embedding is the complex conjugate prime. -/
theorem harrisPrime_conjugate (φ : K →+* ℂ) :
    harrisPrime p θ (ComplexEmbedding.conjugate φ) = conjPrime (harrisPrime p θ φ) := by
  apply HeightOneSpectrum.ext
  ext x
  simp [harrisPrime_asIdeal, conjPrime_asIdeal]

/-- The primes of the conjugate CM type are the conjugates of the primes of `Φ`. -/
theorem cmTypePrimes_conjugate (Φ : CMType K) :
    cmTypePrimes p θ Φ.conjugate = conjPrime '' cmTypePrimes p θ Φ := by
  ext w
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨harrisPrime p θ (ComplexEmbedding.conjugate σ),
      ⟨_, (CMType.mem_conjugate_iff Φ σ).mpr hσ, rfl⟩, ?_⟩
    rw [harrisPrime_conjugate, conjPrime_conjPrime]
  · rintro ⟨-, ⟨σ, hσ, rfl⟩, rfl⟩
    refine ⟨ComplexEmbedding.conjugate σ, SetLike.mem_coe.mpr ?_, harrisPrime_conjugate p θ σ⟩
    rw [CMType.mem_conjugate, CMType.mem_conjugate_iff, not_not]
    exact hσ

end Conjugation

section ImaginaryQuadratic

variable [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]

/-- An imaginary quadratic field has exactly the two complex embeddings `τ` and `τ̄`. -/
theorem eq_or_eq_conjugate_of_quadratic (σ τ : F →+* ℂ) :
    σ = τ ∨ σ = ComplexEmbedding.conjugate τ := by
  rcases (CMType.ofImaginaryQuadratic τ).mem_or_conjugate_mem σ with h | h
  · exact Or.inl h
  · right
    rw [CMType.mem_ofImaginaryQuadratic] at h
    rw [← h]
    simp

omit [Algebra F K] in
/-- The conjugate of Harris's CM type is induced from the conjugate embedding. -/
theorem inducedFromImaginaryQuadratic_conjugate [IsCMField K] (ι : F →+* K) (τ : F →+* ℂ) :
    (CMType.inducedFromImaginaryQuadratic ι τ).conjugate =
      CMType.inducedFromImaginaryQuadratic ι (ComplexEmbedding.conjugate τ) := by
  ext σ
  rw [CMType.mem_conjugate, CMType.mem_inducedFromImaginaryQuadratic,
    CMType.mem_inducedFromImaginaryQuadratic]
  rcases eq_or_eq_conjugate_of_quadratic (σ.comp ι) τ with h | h <;> rw [h]
  · exact iff_of_false (not_not.mpr rfl) fun h' =>
      IsTotallyComplex.complexEmbedding_not_isReal τ h'.symm
  · exact iff_of_true (IsTotallyComplex.complexEmbedding_not_isReal τ) rfl

/-- The primes of an imaginary quadratic field above `p` are `u` and `ū`, the
primes of `τ` and of its conjugate. -/
theorem setOf_natCast_mem_eq_pair (τ : F →+* ℂ) :
    {w : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ w.asIdeal} =
      {harrisPrime p θ τ, harrisPrime p θ (ComplexEmbedding.conjugate τ)} := by
  rw [← range_harrisPrime p θ]
  ext w
  constructor
  · rintro ⟨σ, rfl⟩
    rcases eq_or_eq_conjugate_of_quadratic σ τ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    exacts [⟨_, rfl⟩, ⟨_, rfl⟩]

/-- The prime `p` splits in the imaginary quadratic field exactly when `u ≠ ū`. -/
theorem ncard_setOf_natCast_mem_eq_two_iff (τ : F →+* ℂ) :
    {w : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ w.asIdeal}.ncard = 2 ↔
      harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ) := by
  rw [setOf_natCast_mem_eq_pair p θ τ]
  constructor
  · intro h heq
    rw [heq, Set.pair_eq_singleton, Set.ncard_singleton] at h
    omega
  · exact Set.ncard_pair

variable [IsCMField K]

/-- Harris's `Φ_p`: for the CM type induced from `τ`, the associated primes are
exactly the primes of `K` above the prime `u` of `τ`. -/
theorem cmTypePrimes_inducedFromImaginaryQuadratic (τ : F →+* ℂ) :
    cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic (algebraMap F K) τ) =
      {w | w.asIdeal.LiesOver (harrisPrime p θ τ).asIdeal} := by
  ext w
  rw [mem_cmTypePrimes, Set.mem_ofPred_eq, harrisPrime_liesOver_iff]
  simp only [CMType.mem_inducedFromImaginaryQuadratic]

/-- The primes of the conjugate type are the primes of `K` above `ū`. -/
theorem cmTypePrimes_conjugate_inducedFromImaginaryQuadratic (τ : F →+* ℂ) :
    cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic (algebraMap F K) τ).conjugate =
      {w | w.asIdeal.LiesOver (harrisPrime p θ (ComplexEmbedding.conjugate τ)).asIdeal} := by
  rw [inducedFromImaginaryQuadratic_conjugate, cmTypePrimes_inducedFromImaginaryQuadratic]

/-- `Φ_p` and its conjugate are disjoint exactly when `p` splits, i.e. `u ≠ ū`. -/
theorem disjoint_cmTypePrimes_conjugate_iff (τ : F →+* ℂ) :
    Disjoint (cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic (algebraMap F K) τ))
        (cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic (algebraMap F K) τ).conjugate) ↔
      harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ) := by
  rw [cmTypePrimes_conjugate_inducedFromImaginaryQuadratic,
    cmTypePrimes_inducedFromImaginaryQuadratic, Set.disjoint_left]
  constructor
  · intro h heq
    have h1 : harrisPrime p θ (ComplexEmbedding.lift K τ) ∈
        {w : HeightOneSpectrum (𝓞 K) | w.asIdeal.LiesOver (harrisPrime p θ τ).asIdeal} :=
      (harrisPrime_liesOver_iff p θ τ _).mpr
        ⟨_, ComplexEmbedding.lift_comp_algebraMap K τ, rfl⟩
    exact h h1 (heq ▸ h1)
  · intro hne w h1 h2
    have h1' : w.asIdeal.LiesOver (harrisPrime p θ τ).asIdeal := h1
    have h2' : w.asIdeal.LiesOver (harrisPrime p θ (ComplexEmbedding.conjugate τ)).asIdeal := h2
    exact hne (HeightOneSpectrum.ext (h1'.over.trans h2'.over.symm))

/-- When `p` splits, Harris's CM type is the type of Harris 1997: the embeddings
whose restriction to the imaginary quadratic field induces the prime `u`. -/
theorem mem_inducedFromImaginaryQuadratic_iff (τ : F →+* ℂ)
    (hsplit : harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ))
    (σ : K →+* ℂ) :
    σ ∈ CMType.inducedFromImaginaryQuadratic (algebraMap F K) τ ↔
      harrisPrime p θ (σ.comp (algebraMap F K)) = harrisPrime p θ τ := by
  rw [CMType.mem_inducedFromImaginaryQuadratic]
  constructor
  · intro h
    rw [h]
  · intro h
    rcases eq_or_eq_conjugate_of_quadratic (σ.comp (algebraMap F K)) τ with h' | h'
    · exact h'
    · rw [h'] at h
      exact (hsplit h.symm).elim

end ImaginaryQuadratic

end Harris


end Langlands.Shimura
