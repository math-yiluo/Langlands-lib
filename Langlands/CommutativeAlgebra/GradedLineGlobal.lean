import Langlands.CommutativeAlgebra.GradedLineFlatLocal

/-! # Global coordinates for flat graded lines -/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.CommutativeAlgebra

/-- A finite module whose maximal-ideal fibres all vanish is zero. -/
theorem subsingleton_of_all_maximal_smul_top
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ (p : Ideal R), p.IsMaximal → p • (⊤ : Submodule R M) = ⊤) :
    Subsingleton M := by
  classical
  by_contra hn
  have hann : Module.annihilator R M ≠ ⊤ := fun heq =>
    hn (Module.annihilator_eq_top_iff.1 heq)
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨r, hr, hrM⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p ⊤
      Module.Finite.fg_top (by rw [h p hp])
  have hrann : r ∈ Module.annihilator R M :=
    Module.mem_annihilator.2 fun m => hrM m Submodule.mem_top
  exact hp.ne_top ((Ideal.eq_top_iff_one _).2
    (by simpa using p.sub_mem (hle hrann) hr))

/-- A finite submodule is contained in another if this holds modulo every maximal ideal. -/
theorem le_of_all_maximal_le_sup_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {s t : Submodule R M} (hs : s.FG)
    (h : ∀ (p : Ideal R), p.IsMaximal → s ≤ t ⊔ p • s) :
    s ≤ t := by
  let Q := s.map t.mkQ
  let : Module.Finite R Q := Module.Finite.of_fg (hs.map t.mkQ)
  have hQ : Subsingleton Q :=
      subsingleton_of_all_maximal_smul_top (R := R) fun p hp => by
    apply top_unique
    intro q _
    apply (Submodule.mem_smul_top_iff p Q q).2
    have hmap := Submodule.map_mono (f := t.mkQ) (h p hp)
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_smul''] at hmap
    exact hmap q.property
  intro a ha
  have hz := congrArg Subtype.val
    (hQ.elim (⟨t.mkQ a, Submodule.mem_map_of_mem ha⟩ : Q) 0)
  simpa using hz

namespace GradedLine

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {c : A →+* LaurentPolynomial A} (hc : IsGrading R c)

local instance quotientField (p : Ideal R) [p.IsMaximal] : Field (R ⧸ p) :=
  Ideal.Quotient.field p

/-- A universal line over a maximal quotient detects the extended ideal. -/
theorem IsUniversalLine.ker_le_quotient {p : Ideal R} [p.IsMaximal]
    {ψ : A →ₐ[R] (R ⧸ p)[X]} (h : IsUniversalLine (R ⧸ p) ψ)
    (a : A) (ha : ψ a = 0) :
    a ∈ p.map (algebraMap R A) := by
  let I := p.map (algebraMap R A)
  let f : R ⧸ p →+* A ⧸ I :=
    Ideal.Quotient.lift p ((Ideal.Quotient.mk I).comp (algebraMap R A))
      fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)
  let : Algebra (R ⧸ p) (A ⧸ I) := f.toAlgebra
  have : IsScalarTower R (R ⧸ p) (A ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  obtain ⟨d, hd⟩ := (h (A ⧸ I)).2 (Ideal.Quotient.mkₐ R I)
  have heq := congrArg (fun φ : A →ₐ[R] A ⧸ I => φ a) hd
  simp only [AlgHom.comp_apply, ha, map_zero] at heq
  exact Ideal.Quotient.eq_zero_iff_mem.1 heq.symm

/-- The graded spanning argument over a field only needs a surjective scalar map. -/
theorem le_powSpan_sup_of_surjective
    {K : Type u} [Field K] [Algebra R K] {d : ℕ}
    {ψ : A →ₐ[R] K[X]} (hψ : IsFibreLine hc K d ψ) (hd : 0 < d)
    (hsurj : Function.Surjective (algebraMap R K)) (p : Ideal R)
    (hker : ∀ a, ψ a = 0 → a ∈ p.map (algebraMap R A))
    {x : A} (hx : x ∈ homog hc d) (hu : (ψ x).coeff 1 ≠ 0) (n : ℤ) :
    homog hc n ≤ powSpan x d n ⊔ p • homog hc n := by
  intro a ha
  have hxX : ψ x = Polynomial.C ((ψ x).coeff 1) * X := by
    have heq := hψ.eq_C_mul_X_pow hd (j := 1) (by rwa [Nat.cast_one, one_mul])
    rwa [pow_one] at heq
  by_cases h : ∃ j : ℕ, (j : ℤ) * d = n
  · obtain ⟨j, rfl⟩ := h
    obtain ⟨r, hr⟩ := hsurj ((ψ a).coeff j / (ψ x).coeff 1 ^ j)
    have hxj : x ^ j ∈ homog hc (j * d) := pow_mem_homog hc hx j
    have hdiff : a - r • x ^ j ∈ homog hc (j * d) :=
      Submodule.sub_mem _ ha (Submodule.smul_mem _ r hxj)
    have hψ0 : ψ (a - r • x ^ j) = 0 := by
      rw [map_sub, map_smul, map_pow, hxX, hψ.eq_C_mul_X_pow hd ha, mul_pow,
        ← Polynomial.C_pow, Algebra.smul_def, Polynomial.algebraMap_apply, hr,
        ← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ (pow_ne_zero _ hu), sub_self]
    have hmem := mem_smul_homog hc hdiff (hker _ hψ0)
    have heq : a = r • x ^ j + (a - r • x ^ j) := by abel
    rw [heq]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl, rfl⟩)) hmem
  · push Not at h
    exact Submodule.mem_sup_right (mem_smul_homog hc ha (hker _ (hψ.eq_zero ha h)))

/-- A generator of the coordinate-degree component remains nonzero on every fibre line. -/
theorem IsFibreLine.coeff_one_ne_zero_of_generator
    {K : Type u} [Field K] [Algebra R K] {d : ℕ}
    {ψ : A →ₐ[R] K[X]} (hψ : IsFibreLine hc K d ψ)
    {x : A} (hgen : homog hc d ≤ Submodule.span R {x}) :
    (ψ x).coeff 1 ≠ 0 := by
  intro hx0
  obtain ⟨a, ha⟩ := hψ.exists_coeff_one_ne_zero
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hgen (comp_mem_homog hc d a))
  apply ha
  rw [← hr, map_smul, Polynomial.coeff_smul, hx0, smul_zero]

variable (hneg : ∀ a, ∀ n < 0, (c a).coeff n = 0)
  (hzero : ∀ a, (c a).coeff 0 ∈ Set.range (algebraMap R A))

include hneg hzero in
/-- Powers of a global generator span every component when all maximal fibres are lines. -/
theorem homog_le_powSpan_of_generator [Algebra.FiniteType R A]
    {d : ℕ} (hd : 0 < d) {x : A} (hx : x ∈ homog hc d)
    (hgen : homog hc d ≤ Submodule.span R {x})
    (hfib : ∀ (p : Ideal R) [p.IsMaximal], ∃ ψ : A →ₐ[R] (R ⧸ p)[X],
      IsFibreLine hc (R ⧸ p) d ψ ∧
        ∀ a, ψ a = 0 → a ∈ p.map (algebraMap R A))
    (n : ℤ) :
    homog hc n ≤ powSpan x d n := by
  classical
  apply le_of_all_maximal_le_sup_smul (homog_fg hc hneg hzero n)
  intro p hp
  let := hp
  obtain ⟨ψ, hψ, hker⟩ := hfib p
  exact le_powSpan_sup_of_surjective hc hψ hd Ideal.Quotient.mk_surjective p hker hx
    (hψ.coeff_one_ne_zero_of_generator hc hgen) n

/-- A flat module with a nonzero fibre at every maximal ideal has faithful scalar action. -/
theorem faithfulSMul_of_flat_of_maximal_fibres
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hfib : ∀ (p : Ideal R), p.IsMaximal → p • (⊤ : Submodule R M) ≠ ⊤) :
    FaithfulSMul R M := by
  let : Module.FaithfullyFlat R M := ⟨hfib⟩
  constructor
  intro r s hrs
  have hmul : LinearMap.mulLeft R (r - s) = 0 := by
    apply (Module.FaithfullyFlat.zero_iff_rTensor_zero R M _).2
    apply TensorProduct.ext'
    intro a m
    have hsmul : (r - s) • m = 0 := by rw [sub_smul, hrs, sub_self]
    simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LinearMap.zero_apply]
    rw [← smul_eq_mul, TensorProduct.smul_tmul, hsmul,
      TensorProduct.tmul_zero]
  have heq := DFunLike.congr_fun hmul 1
  exact sub_eq_zero.1 (by simpa using heq)

include hneg hzero in
/-- Over any base ring, a global generator in the fibre coordinate degree gives a
polynomial coordinate for a flat finite type graded algebra with universal line fibres. -/
theorem aeval_bijective_of_flat_of_generator
    [Algebra.FiniteType R A] [Module.Flat R A]
    {d : ℕ} (hd : 0 < d) {x : A} (hx : x ∈ homog hc d)
    (hgen : homog hc d ≤ Submodule.span R {x})
    (huniv : ∀ (K : Type u) [Field K] [Algebra R K], ∃ ψ : A →ₐ[R] K[X],
      IsUniversalLine K ψ ∧
        ∀ (n : ℤ) (a : A), a ∈ homog hc n →
          ∀ j : ℕ, (j : ℤ) * d ≠ n → (ψ a).coeff j = 0) :
    Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  classical
  have hle : ∀ n, homog hc n ≤ powSpan x d n := by
    apply homog_le_powSpan_of_generator hc hneg hzero hd hx hgen
    intro p _
    obtain ⟨ψ, hu, hg⟩ := huniv (R ⧸ p)
    exact ⟨ψ, ⟨hg, hu.X_mem_span⟩, hu.ker_le_quotient⟩
  have hfaithful (j : ℕ) : FaithfulSMul R (homog hc ((j : ℤ) * d)) := by
    let M := homog hc ((j : ℤ) * d)
    let : Module.Flat R M := flat_homog hc _
    apply faithfulSMul_of_flat_of_maximal_fibres (R := R) (M := M)
    intro p hp heq
    let := hp
    obtain ⟨ψ, hu, hg⟩ := huniv (R ⧸ p)
    have hψ : IsFibreLine hc (R ⧸ p) d ψ := ⟨hg, hu.X_mem_span⟩
    have hxψ : ψ x ≠ 0 := by
      intro heq
      exact hψ.coeff_one_ne_zero_of_generator hc hgen
        (by rw [heq, Polynomial.coeff_zero])
    have hmem : (⟨x ^ j, pow_mem_homog hc hx j⟩ : M) ∈
        p • (⊤ : Submodule R M) := by rw [heq]; trivial
    have hmem' : x ^ j ∈ p • homog hc ((j : ℤ) * d) :=
      (Submodule.mem_smul_top_iff p M _).1 hmem
    have hmap : x ^ j ∈ p.map (algebraMap R A) := by
      change x ^ j ∈ (p.map (algebraMap R A)).restrictScalars R
      rw [← Ideal.smul_top_eq_map]
      exact (smul_mono_right p (show homog hc ((j : ℤ) * d) ≤ ⊤ from le_top)) hmem'
    have hz : ψ (x ^ j) = 0 := by
      have hleker : p.map (algebraMap R A) ≤ RingHom.ker ψ.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change ψ (algebraMap R A r) = 0
        rw [ψ.commutes, Polynomial.algebraMap_apply]
        change Polynomial.C (Ideal.Quotient.mk p r) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      exact hleker hmap
    rw [map_pow] at hz
    exact pow_ne_zero j hxψ hz
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    ext j
    rw [Polynomial.coeff_zero]
    let M := homog hc ((j : ℤ) * d)
    let : FaithfulSMul R M := hfaithful j
    have heq : homog hc ((j : ℤ) * d) = Submodule.span R {x ^ j} := by
      refine le_antisymm ?_ (Submodule.span_le.2
        (Set.singleton_subset_iff.2 (pow_mem_homog hc hx j)))
      simpa only [powSpan_mul_eq_span hd] using hle ((j : ℤ) * d)
    have hfx : f.coeff j • x ^ j = 0 := by
      rw [← comp_aeval hc hd hx f j, hf, map_zero]
    apply eq_of_smul_eq_smul (α := M)
    intro a
    apply Subtype.ext
    change f.coeff j • (a : A) = (0 : R) • (a : A)
    rw [zero_smul]
    have ha : (a : A) ∈ homog hc ((j : ℤ) * d) := a.property
    rw [heq] at ha
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 ha
    rw [← hr, smul_smul, mul_comm, ← smul_smul, hfx, smul_zero]
  · intro a
    have hmem : a ∈ (Polynomial.aeval x : R[X] →ₐ[R] A).range := by
      rw [← sum_comp hc a]
      refine Subalgebra.sum_mem _ fun n _ => ?_
      have hspan : powSpan x d n ≤
          Subalgebra.toSubmodule (Polynomial.aeval x : R[X] →ₐ[R] A).range := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨j, -, rfl⟩
        exact ⟨X ^ j, by simp⟩
      exact hspan (hle n (comp_mem_homog hc n a))
    exact hmem

include hneg hzero in
/-- Trivializing the coordinate-degree line gives a global polynomial coordinate. -/
theorem exists_aeval_bijective_of_flat_of_free_degree
    [Algebra.FiniteType R A] [Module.Flat R A]
    {d : ℕ} (hd : 0 < d) (e : R ≃ₗ[R] homog hc d)
    (huniv : ∀ (K : Type u) [Field K] [Algebra R K], ∃ ψ : A →ₐ[R] K[X],
      IsUniversalLine K ψ ∧
        ∀ (n : ℤ) (a : A), a ∈ homog hc n →
          ∀ j : ℕ, (j : ℤ) * d ≠ n → (ψ a).coeff j = 0) :
    ∃ x ∈ homog hc d, Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  let x : A := (e 1).val
  have hx : x ∈ homog hc d := (e 1).property
  have hgen : homog hc d ≤ Submodule.span R {x} := by
    intro a ha
    obtain ⟨r, hr⟩ := e.surjective (⟨a, ha⟩ : homog hc d)
    apply Submodule.mem_span_singleton.2
    refine ⟨r, ?_⟩
    have heq : r • e 1 = (⟨a, ha⟩ : homog hc d) := by
      rw [← e.map_smul, smul_eq_mul, mul_one, hr]
    exact congrArg Subtype.val heq
  exact ⟨x, hx, aeval_bijective_of_flat_of_generator hc hneg hzero hd hx hgen huniv⟩

/-- A polynomial-coordinate equivalence obtained from a trivial coordinate-degree line. -/
def polynomialEquivOfFlatOfFreeDegree
    [Algebra.FiniteType R A] [Module.Flat R A]
    {d : ℕ} (hd : 0 < d) (e : R ≃ₗ[R] homog hc d)
    (huniv : ∀ (K : Type u) [Field K] [Algebra R K], ∃ ψ : A →ₐ[R] K[X],
      IsUniversalLine K ψ ∧
        ∀ (n : ℤ) (a : A), a ∈ homog hc n →
          ∀ j : ℕ, (j : ℤ) * d ≠ n → (ψ a).coeff j = 0) :
    R[X] ≃ₐ[R] A :=
  let hex := exists_aeval_bijective_of_flat_of_free_degree hc hneg hzero hd e huniv
  AlgEquiv.ofBijective (Polynomial.aeval (Classical.choose hex)) (Classical.choose_spec hex).2

end GradedLine
end Langlands.CommutativeAlgebra
