import Langlands.Global.AdelicExponentPolynomials
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicStandardConstantTermTwist
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicStandardConstantTerm

/-! # Algebra of the cuspidal tests

Auxiliary results for the common-point forms of the cuspidal equations (8.2b) and (8.3) of
Bernstein–Lapid §8.4: polynomial families with entire coefficients, translation polynomials and
their transfer to Levi pairings, twists of polynomial orbits, right translation of constant terms
and Levi pairings, and linear combinations of automorphic functions. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-! ### Polynomial families with entire coefficients -/

section EntireFamily

open Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A family of complex polynomials whose coefficients are entire functions of the parameter. -/
def IsEntirePolynomialFamily (P : E → ℂ[X]) : Prop :=
  ∀ k : ℕ, Differentiable ℂ fun s => (P s).coeff k

theorem IsEntirePolynomialFamily.const (p : ℂ[X]) : IsEntirePolynomialFamily fun _ : E => p :=
  fun _ => differentiable_const _

theorem IsEntirePolynomialFamily.mul {P Q : E → ℂ[X]} (hP : IsEntirePolynomialFamily P)
    (hQ : IsEntirePolynomialFamily Q) : IsEntirePolynomialFamily fun s => P s * Q s := by
  intro k
  simp only [coeff_mul]
  exact Differentiable.fun_sum fun x _ => (hP x.1).mul (hQ x.2)

theorem IsEntirePolynomialFamily.pow {P : E → ℂ[X]} (hP : IsEntirePolynomialFamily P) (n : ℕ) :
    IsEntirePolynomialFamily fun s => P s ^ n := by
  induction n with
  | zero => simpa using IsEntirePolynomialFamily.const (E := E) 1
  | succ n ih => simpa [pow_succ] using ih.mul hP

theorem IsEntirePolynomialFamily.prod {κ : Type*} (I : Finset κ) {P : κ → E → ℂ[X]}
    (hP : ∀ i ∈ I, IsEntirePolynomialFamily (P i)) :
    IsEntirePolynomialFamily fun s => ∏ i ∈ I, P i s := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using IsEntirePolynomialFamily.const (E := E) 1
  | insert a I ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hP a (Finset.mem_insert_self a I)).mul
      (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

theorem IsEntirePolynomialFamily.X_sub_C {r : E → ℂ} (hr : Differentiable ℂ r) :
    IsEntirePolynomialFamily fun s => X - C (r s) := by
  intro k
  simp only [coeff_sub, coeff_X, coeff_C]
  exact (differentiable_const _).sub (by split_ifs <;> simp [hr, differentiable_const])

end EntireFamily

/-! ### Roots of products of linear factors -/

section Roots

open Polynomial

theorem exists_eq_of_eval_prod_pow_eq_zero {κ : Type*} (I : Finset κ) (r : κ → ℂ) (m : κ → ℕ)
    {z : ℂ} (hz : (∏ i ∈ I, (X - C (r i)) ^ (m i + 1)).eval z = 0) : ∃ i ∈ I, z = r i := by
  rw [eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, hi, h⟩ := hz
  rw [eval_pow, eval_sub, eval_X, eval_C] at h
  exact ⟨i, hi, sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_ne_zero _) |>.mp h)⟩

theorem monic_prod_X_sub_C_pow {κ : Type*} (I : Finset κ) (r : κ → ℂ) (m : κ → ℕ) :
    (∏ i ∈ I, (X - C (r i)) ^ (m i + 1)).Monic :=
  monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C (r i)).pow _

theorem natDegree_prod_X_sub_C_pow {κ : Type*} (I : Finset κ) (r : κ → ℂ) (m : κ → ℕ) :
    (∏ i ∈ I, (X - C (r i)) ^ (m i + 1)).natDegree = ∑ i ∈ I, (m i + 1) := by
  rw [natDegree_prod_of_monic I _ fun i _ => (monic_X_sub_C (r i)).pow _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]

theorem coeff_zero_prod_X_sub_C_pow_ne_zero {κ : Type*} (I : Finset κ) (r : κ → ℂ) (m : κ → ℕ)
    (hr : ∀ i ∈ I, r i ≠ 0) : (∏ i ∈ I, (X - C (r i)) ^ (m i + 1)).coeff 0 ≠ 0 := by
  rw [coeff_zero_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [coeff_zero_eq_eval_zero, eval_pow, eval_sub, eval_X, eval_C, zero_sub]
  exact pow_ne_zero _ (neg_ne_zero.mpr (hr i hi))

end Roots

/-! ### Translation polynomials -/

section Translation

open Polynomial

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
/-- A multiple of an annihilating translation polynomial is annihilating. -/
theorem AdelicGroupPoints.IsTranslationPolynomialSolution.of_dvd {a : AdelicGroupPoints F G} {D D' : ℂ[X]}
    {φ : AdelicGroupPoints F G → ℂ} (h : IsTranslationPolynomialSolution a D φ) (hD : D ∣ D') :
    IsTranslationPolynomialSolution a D' φ := by
  rw [isTranslationPolynomialSolution_iff_aeval] at h ⊢
  obtain ⟨q, rfl⟩ := hD
  rw [mul_comm, map_mul, Module.End.mul_apply, h, map_zero]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
/-- Translation polynomials annihilating finitely many functions: a product annihilates any
linear combination, as soon as each function is annihilated by one of its factors. -/
theorem isTranslationPolynomialSolution_sum_of_dvd {κ : Type*} (I : Finset κ)
    {a : AdelicGroupPoints F G} {D : ℂ[X]} (φ : κ → AdelicGroupPoints F G → ℂ) (c : κ → ℂ)
    (hφ : ∀ i ∈ I, IsTranslationPolynomialSolution a D (φ i)) :
    IsTranslationPolynomialSolution a D (fun g => ∑ i ∈ I, c i * φ i g) := by
  intro g
  have h : ∀ i ∈ I, ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * (c i * φ i (a ^ k * g)) =
      0 := fun i hi => by
    rw [show (∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * (c i * φ i (a ^ k * g))) =
        c i * ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ i (a ^ k * g) by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring, hφ i hi g, mul_zero]
  calc ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * ∑ i ∈ I, c i * φ i (a ^ k * g)
      = ∑ i ∈ I, ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * (c i * φ i (a ^ k * g)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero h

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
theorem AdelicGroupPoints.IsTranslationPolynomialSolution.congr {a : AdelicGroupPoints F G} {D : ℂ[X]}
    {φ ψ : AdelicGroupPoints F G → ℂ} (h : IsTranslationPolynomialSolution a D φ)
    (he : ∀ g, ψ g = φ g) : IsTranslationPolynomialSolution a D ψ := by
  have : ψ = φ := funext he
  rw [this]
  exact h

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
theorem AdelicGroupPoints.IsTranslationPolynomialSolution.zero (a : AdelicGroupPoints F G) (D : ℂ[X]) :
    IsTranslationPolynomialSolution a D (0 : AdelicGroupPoints F G → ℂ) := by
  intro g
  simp

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] in
theorem AdelicGroupPoints.IsTranslationPolynomialSolution.add {a : AdelicGroupPoints F G} {D : ℂ[X]}
    {φ ψ : AdelicGroupPoints F G → ℂ} (hφ : IsTranslationPolynomialSolution a D φ)
    (hψ : IsTranslationPolynomialSolution a D ψ) :
    IsTranslationPolynomialSolution a D (fun g => φ g + ψ g) := by
  intro g
  simp only [mul_add, Finset.sum_add_distrib, hφ g, hψ g, add_zero]

end Translation

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-! ### Transfer to Levi pairings -/

/-- If a translation polynomial in a point of `𝔄_J` annihilates `f`, it annihilates the
function `g ↦ ⟨f, test⟩_g` of its Levi pairings, provided these pairings converge
absolutely. -/
theorem isTranslationPolynomialSolution_leviPairing (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (test : AdelicGroupPoints F (𝓕.M J) → ℂ) (b : 𝓕.positiveSplitComponent J) (D : Polynomial ℂ)
    {f : AdelicGroupPoints F G → ℂ} (hf : f ∈ 𝓕.leviPairingDomain J test)
    (h : IsTranslationPolynomialSolution (map F (𝓕.P J) G (𝓕.p J) b.val) D f) :
    IsTranslationPolynomialSolution (map F (𝓕.P J) G (𝓕.p J) b.val) D
      (fun g => 𝓕.leviPairing J f g test) := by
  intro g
  let S := 𝓕.leviPairingDomain J test
  let Lp := 𝓕.leviPairingLinear J test
  have hmem (k : ℕ) : 𝓕.splitComponentRepresentation J (b ^ k) f ∈ S :=
    𝓕.splitComponent_mem_leviPairingDomain J test (b ^ k) hf
  have hval (k : ℕ) (g' : AdelicGroupPoints F G) :
      𝓕.splitComponentRepresentation J (b ^ k) f g' =
        f (map F (𝓕.P J) G (𝓕.p J) b.val ^ k * g') := by
    change f (map F (𝓕.P J) G (𝓕.p J) (b ^ k).val * g') = _
    rw [Subgroup.coe_pow, map_pow]
  have hpair (k : ℕ) : 𝓕.leviPairing J f (map F (𝓕.P J) G (𝓕.p J) b.val ^ k * g) test =
      Lp ⟨_, hmem k⟩ g := by
    change _ = 𝓕.leviPairing J (𝓕.splitComponentRepresentation J (b ^ k) f) g test
    unfold leviPairing
    rw [𝓕.leviPairingIntegrand_splitComponent J test, Subgroup.coe_pow, map_pow]
  have hzero : (∑ k ∈ Finset.range (D.natDegree + 1),
      D.coeff k • (⟨_, hmem k⟩ : S) : S).val = 0 := by
    funext g'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hval, Pi.zero_apply]
    exact h g'
  have h0 : (∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k • (⟨_, hmem k⟩ : S) : S) = 0 :=
    Subtype.ext hzero
  have := congrFun (congrArg Lp h0) g
  rw [map_sum, map_zero, Finset.sum_apply] at this
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [hpair]
  exact this

/-! ### Right translation -/

/-- The constant term commutes with right translation. -/
theorem constantTerm_mul_right (J : StandardIndex F G 𝓕.i 𝓕.ν) (f : AdelicGroupPoints F G → ℂ)
    (t g : AdelicGroupPoints F G) :
    𝓕.constantTerm J (fun x => f (x * t)) g = 𝓕.constantTerm J f (g * t) := by
  unfold StandardParabolicFamily.constantTerm AdelicGroupPoints.subgroupConstantTerm
  congr 1
  funext x
  exact congrArg f (mul_assoc _ _ _)

theorem leviPairingIntegrand_mul_right (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (f : AdelicGroupPoints F G → ℂ) (t g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    𝓕.leviPairingIntegrand J (fun x => f (x * t)) g test =
      𝓕.leviPairingIntegrand J f (g * t) test := by
  funext q
  unfold leviPairingIntegrand
  exact congrArg (· * _) (congrArg f (mul_assoc _ _ _))

/-- The Levi pairing of a right translate is the pairing at the translated external
argument. -/
theorem leviPairing_mul_right (J : StandardIndex F G 𝓕.i 𝓕.ν) (f : AdelicGroupPoints F G → ℂ)
    (t g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    𝓕.leviPairing J (fun x => f (x * t)) g test = 𝓕.leviPairing J f (g * t) test := by
  unfold leviPairing
  rw [𝓕.leviPairingIntegrand_mul_right]

/-! ### Iwasawa coverage for larger standard parabolics -/

theorem isIwasawaCompact_of_le {K : Subgroup (AdelicGroupPoints F G)}
    {Q P : StandardIndex F G 𝓕.i 𝓕.ν} (hQP : Q ≤ P) (hK : IsIwasawaCompact (𝓕.p Q) K) :
    IsIwasawaCompact (𝓕.p P) K := by
  refine ⟨hK.isCompact, Set.eq_univ_of_forall fun g => ?_⟩
  have hg : g ∈ Set.range (map F (𝓕.P Q) G (𝓕.p Q)) * (K : Set (AdelicGroupPoints F G)) := by
    rw [hK.range_mul]
    exact Set.mem_univ g
  obtain ⟨x, ⟨q, rfl⟩, k, hk, rfl⟩ := hg
  refine Set.mem_mul.mpr ⟨map F (𝓕.P P) G (𝓕.p P)
    (map F (𝓕.P Q) (𝓕.P P) (𝓕.nestedParabolicHom hQP) q), ⟨_, rfl⟩, k, hk, ?_⟩
  rw [← map_comp_apply_of_hom, 𝓕.nestedParabolicHom_comp hQP]

/-! ### Twists of polynomial orbits -/

/-- For `Q ≤ I`, left translation by a point `x` of the split component of `Q` multiplies the
height power `m_{P_I}^λ` by `x` raised to the restriction of `λ` to `P_Q`. -/
theorem heightPower_splitComponent_mul {I Q : StandardIndex F G 𝓕.i 𝓕.ν} (hQI : Q ≤ I)
    [IsClosedImmersion (𝓕.p I).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p I) K) (lam : ComplexCharacterParameter F (𝓕.P I))
    (x : AdelicGroupPoints F (𝓕.P Q)) (g : AdelicGroupPoints F G) :
    hK.heightPower lam (map F (𝓕.P Q) G (𝓕.p Q) x * g) =
      parameterPower F (𝓕.P Q) (parameterRestrict (𝓕.nestedParabolicHom hQI) lam) x *
        hK.heightPower lam g := by
  rw [parameterPower_parameterRestrict, ← 𝓕.nestedParabolicHom_comp hQI, map_comp_apply_of_hom,
    IsIwasawaCompact.heightPower, hK.height_map_mul, map_add, Complex.exp_add,
    IsIwasawaCompact.heightPower, parameterPower]

/-- Twisting by `m_{P_I}^λ` shifts the polynomial orbit exponents along a standard `Q ≤ I` by the
restriction of `λ` and keeps the degree. -/
theorem HasPolynomialOrbit.parameterTwist {I Q : StandardIndex F G 𝓕.i 𝓕.ν} (hQI : Q ≤ I)
    [IsClosedImmersion (𝓕.p I).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p I) K) (lam : ComplexCharacterParameter F (𝓕.P I))
    {mu : ComplexCharacterParameter F (𝓕.P Q)} {n : ℕ} {c : AdelicGroupPoints F G → ℂ}
    (hc : 𝓕.HasPolynomialOrbit Q mu n c) :
    𝓕.HasPolynomialOrbit Q (mu + parameterRestrict (𝓕.nestedParabolicHom hQI) lam) n
      (hK.parameterTwist c lam) := by
  intro g
  obtain ⟨p, hp, hpx⟩ := hc g
  refine ⟨hK.heightPower lam g • p, (polynomialFunctions _ n).smul_mem _ hp, fun x hx => ?_⟩
  have hx' := hpx x hx
  simp only [unnormalizedAction, IsIwasawaCompact.parameterTwist] at hx' ⊢
  rw [𝓕.heightPower_splitComponent_mul hQI hK lam x g, neg_add, parameterPower_add,
    Pi.smul_apply, smul_eq_mul, ← hx']
  have hinv : parameterPower F (𝓕.P Q) (parameterRestrict (𝓕.nestedParabolicHom hQI) lam) x *
      parameterPower F (𝓕.P Q) (-parameterRestrict (𝓕.nestedParabolicHom hQI) lam) x = 1 := by
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  linear_combination (c (map F (𝓕.P Q) G (𝓕.p Q) x * g) * hK.heightPower lam g *
    parameterPower F (𝓕.P Q) (-mu) x) * hinv

/-! ### Polynomials in the split-component action -/

theorem aeval_splitComponentRepresentation_apply (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (b : 𝓕.positiveSplitComponent J) (D : Polynomial ℂ) (f : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) :
    Polynomial.aeval (𝓕.splitComponentRepresentation J b) D f g =
      ∑ k ∈ Finset.range (D.natDegree + 1),
        D.coeff k * f (map F (𝓕.P J) G (𝓕.p J) b.val ^ k * g) := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_pow]
  change D.coeff k * f (map F (𝓕.P J) G (𝓕.p J) (b ^ k).val * g) = _
  rw [Subgroup.coe_pow, map_pow]

theorem aeval_mem_leviPairingDomain (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (test : AdelicGroupPoints F (𝓕.M J) → ℂ) (b : 𝓕.positiveSplitComponent J) (D : Polynomial ℂ)
    {f : AdelicGroupPoints F G → ℂ} (hf : f ∈ 𝓕.leviPairingDomain J test) :
    Polynomial.aeval (𝓕.splitComponentRepresentation J b) D f ∈ 𝓕.leviPairingDomain J test := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [← map_pow]
  exact 𝓕.splitComponent_mem_leviPairingDomain J test (b ^ k) hf

/-! ### Twisted Levi pairings -/

theorem leviPairing_parameterTwist_of_le {I Q : StandardIndex F G 𝓕.i 𝓕.ν} (hQI : Q ≤ I)
    [IsClosedImmersion (𝓕.p I).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p I) K) (c : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (g : AdelicGroupPoints F G)
    (test : AdelicGroupPoints F (𝓕.M Q) → ℂ) :
    𝓕.leviPairing Q (hK.parameterTwist c lam) g test =
      𝓕.leviPairing Q c g test * hK.heightPower lam g := by
  unfold leviPairing
  rw [𝓕.leviPairingIntegrand_parameterTwist I Q hK hQI, integral_mul_const]

theorem parameterTwist_mem_leviPairingDomain {I Q : StandardIndex F G 𝓕.i 𝓕.ν} (hQI : Q ≤ I)
    [IsClosedImmersion (𝓕.p I).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p I) K) {c : AdelicGroupPoints F G → ℂ}
    (lam : ComplexCharacterParameter F (𝓕.P I)) {test : AdelicGroupPoints F (𝓕.M Q) → ℂ}
    (hc : c ∈ 𝓕.leviPairingDomain Q test) :
    hK.parameterTwist c lam ∈ 𝓕.leviPairingDomain Q test := by
  intro g
  rw [𝓕.leviPairingIntegrand_parameterTwist I Q hK hQI]
  exact (hc g).mul_const _

theorem leviPairing_sub (J : StandardIndex F G 𝓕.i 𝓕.ν) {f h : AdelicGroupPoints F G → ℂ}
    (g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (𝓕.M J) → ℂ)
    (hf : Integrable (𝓕.leviPairingIntegrand J f g test)
      (normOneRationalQuotientHaarMeasure F (𝓕.M J)))
    (hh : Integrable (𝓕.leviPairingIntegrand J h g test)
      (normOneRationalQuotientHaarMeasure F (𝓕.M J))) :
    𝓕.leviPairing J (f - h) g test = 𝓕.leviPairing J f g test - 𝓕.leviPairing J h g test := by
  have hsub : 𝓕.leviPairingIntegrand J (f - h) g test =
      fun q => 𝓕.leviPairingIntegrand J f g test q - 𝓕.leviPairingIntegrand J h g test q := by
    funext q
    simp only [leviPairingIntegrand, Pi.sub_apply, sub_mul]
  unfold leviPairing
  rw [hsub, integral_sub hf hh]

/-! ### Linear combinations of automorphic functions -/

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (Langlands.Global.InfiniteAdelicGroupPoints F G))
  (rho : MatrixRepresentation G (Fin N))

theorem isAutomorphicOn_sum_smul (P : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    {f : Fin m → AdelicGroupPoints F G → ℂ} (hf : ∀ i, 𝓕.IsAutomorphicOn hsmooth Kinf rho P (f i))
    (a : Fin m → ℂ) : 𝓕.IsAutomorphicOn hsmooth Kinf rho P (∑ i, a i • f i) :=
  (Langlands.Automorphic.GroupSchemeFunctions.automorphicFunctionsOn
    (parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P)) Kinf rho hsmooth
    (Langlands.Automorphic.GroupSchemeFunctions.adelicDifferentialCommutator_of_smooth F G
      hsmooth)).sum_mem fun i _ => Submodule.smul_mem _ _ (hf i)

end StandardParabolicFamily

end Langlands.Global
