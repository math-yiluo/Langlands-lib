import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.HarmonicAnalysis.GroupAction
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Translation polynomials of adelic exponents

The algebraic passage from polynomial-exponential orbit maps to the difference
operators in Bernstein–Lapid §8.1 and the translation polynomials in §7.2. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic
  Langlands.HarmonicAnalysis

section RootPolynomial

variable {Idx : Type*}

/-- A monic polynomial with one linear factor for each label in `I`. Distinct
labels with equal roots contribute distinct factors; the empty product is `1`. -/
def translationRootPolynomial (I : Finset Idx) (root : Idx → ℂ) : Polynomial ℂ :=
  ∏ i ∈ I, (X - C (root i))

theorem translationRootPolynomial_monic (I : Finset Idx) (root : Idx → ℂ) :
    (translationRootPolynomial I root).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (root i)

theorem translationRootPolynomial_natDegree (I : Finset Idx) (root : Idx → ℂ) :
    (translationRootPolynomial I root).natDegree = I.card := by
  unfold translationRootPolynomial
  rw [natDegree_prod_of_monic I (fun i => X - C (root i)) (fun i _ => monic_X_sub_C (root i))]
  simp

theorem translationRootPolynomial_coeff_zero (I : Finset Idx) (root : Idx → ℂ) :
    (translationRootPolynomial I root).coeff 0 = ∏ i ∈ I, -root i := by
  simp [translationRootPolynomial, coeff_zero_prod]

theorem translationRootPolynomial_coeff_zero_ne_zero (I : Finset Idx) (root : Idx → ℂ)
    (h : ∀ i ∈ I, root i ≠ 0) : (translationRootPolynomial I root).coeff 0 ≠ 0 := by
  rw [translationRootPolynomial_coeff_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i hi => neg_ne_zero.mpr (h i hi)

/-- A fixed list of holomorphic roots gives holomorphic coefficients, also at root collisions. -/
theorem isHolomorphicOn_translationRootPolynomial_coeff {n : ℕ}
    {W : TopologicalSpace.Opens (Fin n → ℂ)} (I : Finset Idx) (r : Idx → W → ℂ)
    (hr : ∀ i ∈ I, IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (r i) Set.univ) (k : ℕ) :
    IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ)
      (fun s => (translationRootPolynomial I (fun i => r i s)).coeff k) Set.univ := by
  classical
  have hdiff : ∀ k, MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
      (fun s : W => (translationRootPolynomial I (fun i => r i s)).coeff k) Set.univ := by
    induction I using Finset.induction_on with
    | empty =>
      intro k
      simp only [translationRootPolynomial, Finset.prod_empty]
      exact mdifferentiableOn_const
    | @insert a I ha ih =>
      have ha' := hr a (Finset.mem_insert_self a I) (ContinuousLinearMap.id ℂ ℂ)
      have ha'' : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (r a) Set.univ := ha'
      have hI := ih fun i hi => hr i (Finset.mem_insert_of_mem hi)
      intro k
      simp only [translationRootPolynomial, Finset.prod_insert ha, mul_comm (X - C (r a _))]
      cases k with
      | zero =>
        simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
        exact (hI 0).mul ha''.neg
      | succ k =>
        simp only [coeff_mul_X_sub_C]
        exact (hI k).sub ((hI (k + 1)).mul ha'')
  intro mu
  exact (mu.differentiable.mdifferentiable.mdifferentiableOn (s := Set.univ)).comp
    (hdiff k) (Set.mapsTo_univ _ _)

end RootPolynomial

section Adelic

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- At a fixed adelic point, the exponential of an affine character parameter is entire. -/
theorem differentiable_parameterPower_affine {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F G)
    (mu : ComplexCharacterParameter F G) (a : AdelicGroupPoints F G) :
    Differentiable ℂ fun s => parameterPower F G (L s + mu) a := by
  let H := characterLog F G a
  let ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => complexParameterPairing F G (L s) H
      map_add' := fun s t => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun z s => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  simp only [parameterPower, map_add, LinearMap.add_apply]
  exact (ℓ.toContinuousLinearMap.differentiable.add (differentiable_const _)).cexp

/-- The affine exponential roots give holomorphic scalar functions on any open parameter set. -/
theorem isHolomorphicOn_parameterPower_affine {n : ℕ}
    (W : TopologicalSpace.Opens (Fin n → ℂ))
    (L : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F G)
    (mu : ComplexCharacterParameter F G) (a : AdelicGroupPoints F G) :
    IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ)
      (fun s : W => parameterPower F G (L s.1 + mu) a) Set.univ := by
  intro lf
  have hv : MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ)
      (Subtype.val : W → Fin n → ℂ) := contMDiff_subtype_val.mdifferentiable one_ne_zero
  exact ((lf.differentiable.comp (differentiable_parameterPower_affine L mu a)).mdifferentiable.comp
    hv).mdifferentiableOn

/-- Evaluating a polynomial at the linear left shift `f(g) ↦ f(a*g)` gives the
pointwise polynomial equation in `LocalFinitenessData.solutions`. -/
theorem isTranslationPolynomialSolution_iff_aeval (a : AdelicGroupPoints F G) (D : Polynomial ℂ)
    (φ : AdelicGroupPoints F G → ℂ) :
    IsTranslationPolynomialSolution a D φ ↔
      aeval (GroupAction.leftFunctions a⁻¹) D φ = 0 := by
  rw [aeval_eq_sum_range]
  constructor
  · intro h
    funext g
    simpa only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      ← map_pow, ← inv_pow, GroupAction.leftFunctions_apply, inv_inv, Pi.zero_apply] using h g
  · intro h g
    simpa only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      ← map_pow, ← inv_pow, GroupAction.leftFunctions_apply, inv_inv, Pi.zero_apply] using congrFun h g

/-- The product of the component annihilators annihilates the sum. -/
theorem isTranslationPolynomialSolution_sum_prod {Idx : Type*} (I : Finset Idx)
    (a : AdelicGroupPoints F G) (D : Idx → Polynomial ℂ) (φ : Idx → AdelicGroupPoints F G → ℂ)
    (hφ : ∀ i ∈ I, IsTranslationPolynomialSolution a (D i) (φ i)) :
    IsTranslationPolynomialSolution a (∏ i ∈ I, D i) (∑ i ∈ I, φ i) := by
  classical
  rw [isTranslationPolynomialSolution_iff_aeval, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := (isTranslationPolynomialSolution_iff_aeval a (D i) (φ i)).mp (hφ i hi)
  rw [← I.prod_erase_mul D hi, map_mul, Module.End.mul_apply, h, map_zero]

end Adelic

section PolynomialDifference

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem polynomialFunctions_mono {m n : ℕ} (hmn : m ≤ n) :
    polynomialFunctions V m ≤ polynomialFunctions V n := by
  refine Submodule.span_mono ?_
  rintro f ⟨k, hk, ℓ, rfl⟩
  exact ⟨k, hk.trans hmn, ℓ, rfl⟩

private theorem monomial_mem_polynomialFunctions {k n : ℕ} (hkn : k ≤ n)
    (ℓ : Fin k → V →ₗ[ℝ] ℝ) :
    (fun v => ∏ j, ((ℓ j v : ℝ) : ℂ)) ∈ polynomialFunctions V n :=
  Submodule.subset_span ⟨k, hkn, ℓ, rfl⟩

private theorem mul_linear_mem_succ {n : ℕ} (ℓ : V →ₗ[ℝ] ℝ) {p : V → ℂ}
    (hp : p ∈ polynomialFunctions V n) :
    (fun v => ((ℓ v : ℝ) : ℂ) * p v) ∈ polynomialFunctions V (n + 1) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, hk, fs, rfl⟩ := hp
    convert monomial_mem_polynomialFunctions (Nat.succ_le_succ hk) (Fin.cons ℓ fs) using 1
    funext v
    simp [Fin.prod_univ_succ]
  | zero =>
    convert (polynomialFunctions V (n + 1)).zero_mem using 1
    funext v
    simp
  | add p q _ _ hp hq =>
    convert (polynomialFunctions V (n + 1)).add_mem hp hq using 1
    funext v
    simp only [Pi.add_apply, mul_add]
  | smul c p _ hp =>
    convert (polynomialFunctions V (n + 1)).smul_mem c hp using 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private theorem shifted_monomial_mem (h : V) (k : ℕ) (ℓ : Fin k → V →ₗ[ℝ] ℝ) :
    (fun v => ∏ j, ((ℓ j (v + h) : ℝ) : ℂ)) ∈ polynomialFunctions V k := by
  induction k with
  | zero =>
    simpa using (monomial_mem_polynomialFunctions (V := V) (le_refl 0) ℓ)
  | succ k ih =>
    have hp := ih (fun j => ℓ j.succ)
    have h1 := mul_linear_mem_succ (ℓ 0) hp
    have h2 := (polynomialFunctions V (k + 1)).smul_mem ((ℓ 0 h : ℝ) : ℂ)
      (polynomialFunctions_mono (Nat.le_succ k) hp)
    convert (polynomialFunctions V (k + 1)).add_mem h1 h2 using 1
    funext v
    simp only [Fin.prod_univ_succ, map_add, Complex.ofReal_add, add_mul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]

/-- The forward difference `p(v+h) - p(v)` on complex-valued functions on a real vector space. -/
def polynomialDifference (h : V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun p v := p (v + h) - p v
  map_add' p q := by
    funext v
    simp only [Pi.add_apply]
    ring
  map_smul' c p := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sub]

omit [Module ℝ V] in
@[simp] theorem polynomialDifference_apply (h : V) (p : V → ℂ) (v : V) :
    polynomialDifference h p v = p (v + h) - p v := rfl

private theorem difference_monomial_mem (h : V) (k : ℕ) (ℓ : Fin (k + 1) → V →ₗ[ℝ] ℝ) :
    polynomialDifference h (fun v => ∏ j, ((ℓ j v : ℝ) : ℂ)) ∈ polynomialFunctions V k := by
  induction k with
  | zero =>
    have hc := (polynomialFunctions V 0).smul_mem ((ℓ 0 h : ℝ) : ℂ)
      (monomial_mem_polynomialFunctions (V := V) (le_refl 0) (fun j => ℓ j.elim0))
    convert hc using 1
    funext v
    simp [Complex.ofReal_add]
  | succ k ih =>
    have htail := ih (fun j => ℓ j.succ)
    have h1 := mul_linear_mem_succ (ℓ 0) htail
    have h2 := (polynomialFunctions V (k + 1)).smul_mem ((ℓ 0 h : ℝ) : ℂ)
      (shifted_monomial_mem h (k + 1) (fun j => ℓ j.succ))
    convert (polynomialFunctions V (k + 1)).add_mem h1 h2 using 1
    funext v
    simp only [polynomialDifference_apply, Fin.prod_univ_succ (n := k + 1), map_add,
      Complex.ofReal_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Taking a difference in any direction lowers the polynomial degree bound by one. -/
theorem polynomialDifference_mem {n : ℕ} (h : V) {p : V → ℂ}
    (hp : p ∈ polynomialFunctions V (n + 1)) :
    polynomialDifference h p ∈ polynomialFunctions V n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, hk, ℓ, rfl⟩ := hp
    cases k with
    | zero =>
      have hz : polynomialDifference h (fun v => ∏ j, ((ℓ j v : ℝ) : ℂ)) = 0 := by
        funext v
        simp
      rw [hz]
      exact (polynomialFunctions V n).zero_mem
    | succ k =>
      exact polynomialFunctions_mono (Nat.le_of_succ_le_succ hk) (difference_monomial_mem h k ℓ)
  | zero => rw [map_zero]; exact (polynomialFunctions V n).zero_mem
  | add p q _ _ hp hq => rw [map_add]; exact (polynomialFunctions V n).add_mem hp hq
  | smul c p _ hp => rw [map_smul]; exact (polynomialFunctions V n).smul_mem c hp

theorem polynomialDifference_eq_zero_of_mem_degree_zero (h : V) {p : V → ℂ}
    (hp : p ∈ polynomialFunctions V 0) : polynomialDifference h p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, hk, ℓ, rfl⟩ := hp
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    funext v
    simp
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp, hq, add_zero]
  | smul c p _ hp => rw [map_smul, hp, smul_zero]

end PolynomialDifference

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)

/-- The raw left shift minus the value of an unnormalized character, as a linear endomorphism
of all scalar functions. -/
def unnormalizedExponentDifference (lam : ComplexCharacterParameter F (𝓕.P J))
    (a : AdelicGroupPoints F (𝓕.P J)) : Module.End ℂ (AdelicGroupPoints F G → ℂ) :=
  GroupAction.leftFunctions (map F (𝓕.P J) G (𝓕.p J) a)⁻¹ -
    algebraMap ℂ _ (parameterPower F (𝓕.P J) lam a)

@[simp] theorem unnormalizedExponentDifference_apply
    (lam : ComplexCharacterParameter F (𝓕.P J)) (a : AdelicGroupPoints F (𝓕.P J))
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    𝓕.unnormalizedExponentDifference J lam a φ g =
      𝓕.unnormalizedAction J a φ g - parameterPower F (𝓕.P J) lam a * φ g := by
  simp only [unnormalizedExponentDifference, LinearMap.sub_apply, Pi.sub_apply,
    GroupAction.leftFunctions_apply, inv_inv, Module.algebraMap_end_apply, Pi.smul_apply,
    smul_eq_mul, unnormalizedAction]

/-- The degree bound in the polynomial characterization of an unnormalized exponent:
one common bound for all orbits, but the polynomial may depend on the base point `g`. -/
def HasPolynomialOrbit (lam : ComplexCharacterParameter F (𝓕.P J)) (k : ℕ)
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ g : AdelicGroupPoints F G, ∃ p ∈ polynomialFunctions (RealCharacterDual F (𝓕.P J)) k,
    ∀ x ∈ 𝓕.positiveSplitComponent J,
      𝓕.unnormalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x =
        p (characterLog F (𝓕.P J) x)

private theorem orbit_exponentDifference
    {lam : ComplexCharacterParameter F (𝓕.P J)} {φ : AdelicGroupPoints F G → ℂ}
    {a : AdelicGroupPoints F (𝓕.P J)} (ha : a ∈ 𝓕.positiveSplitComponent J)
    {g : AdelicGroupPoints F G} {p : RealCharacterDual F (𝓕.P J) → ℂ}
    (hp : ∀ x ∈ 𝓕.positiveSplitComponent J,
      𝓕.unnormalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x =
        p (characterLog F (𝓕.P J) x))
    {x : AdelicGroupPoints F (𝓕.P J)} (hx : x ∈ 𝓕.positiveSplitComponent J) :
    𝓕.unnormalizedAction J x (𝓕.unnormalizedExponentDifference J lam a φ) g *
          parameterPower F (𝓕.P J) (-lam) x =
      parameterPower F (𝓕.P J) lam a *
        polynomialDifference (characterLog F (𝓕.P J) a) p (characterLog F (𝓕.P J) x) := by
  have hr : parameterPower F (𝓕.P J) lam a * parameterPower F (𝓕.P J) (-lam) a = 1 := by
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  have hxa : 𝓕.unnormalizedAction J (x * a) φ g * parameterPower F (𝓕.P J) (-lam) x =
      parameterPower F (𝓕.P J) lam a *
        p (characterLog F (𝓕.P J) x + characterLog F (𝓕.P J) a) := by
    rw [← characterLog_mul, ← hp (x * a) ((𝓕.positiveSplitComponent J).mul_mem hx ha),
      parameterPower_mul]
    calc
      _ = (𝓕.unnormalizedAction J (x * a) φ g * parameterPower F (𝓕.P J) (-lam) x) *
            (parameterPower F (𝓕.P J) lam a * parameterPower F (𝓕.P J) (-lam) a) := by
          rw [hr, mul_one]
      _ = _ := by ring
  have hshift : map F (𝓕.P J) G (𝓕.p J) a * (map F (𝓕.P J) G (𝓕.p J) x * g) =
      map F (𝓕.P J) G (𝓕.p J) (x * a) * g := by
    rw [← mul_assoc, ← map_mul, 𝓕.positiveSplitComponent_mul_comm J ha hx]
  simp only [unnormalizedAction, unnormalizedExponentDifference_apply, hshift, sub_mul,
    mul_assoc (parameterPower F (𝓕.P J) lam a), polynomialDifference_apply, mul_sub]
  change (𝓕.unnormalizedAction J (x * a) φ g * parameterPower F (𝓕.P J) (-lam) x) -
      parameterPower F (𝓕.P J) lam a *
        (𝓕.unnormalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x) = _
  rw [hxa, hp x hx]

private theorem polynomialOrbit_exponentDifference {lam : ComplexCharacterParameter F (𝓕.P J)}
    {k : ℕ} {φ : AdelicGroupPoints F G → ℂ} (hφ : 𝓕.HasPolynomialOrbit J lam (k + 1) φ)
    {a : AdelicGroupPoints F (𝓕.P J)} (ha : a ∈ 𝓕.positiveSplitComponent J) :
    𝓕.HasPolynomialOrbit J lam k (𝓕.unnormalizedExponentDifference J lam a φ) := by
  intro g
  obtain ⟨p, hpd, hp⟩ := hφ g
  exact ⟨parameterPower F (𝓕.P J) lam a • polynomialDifference (characterLog F (𝓕.P J) a) p,
    (polynomialFunctions _ k).smul_mem _ (polynomialDifference_mem _ hpd),
    fun _ hx => orbit_exponentDifference 𝓕 J ha hp hx⟩

private theorem exponentDifference_of_degree_zero {lam : ComplexCharacterParameter F (𝓕.P J)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : 𝓕.HasPolynomialOrbit J lam 0 φ)
    {a : AdelicGroupPoints F (𝓕.P J)} (ha : a ∈ 𝓕.positiveSplitComponent J) :
    𝓕.unnormalizedExponentDifference J lam a φ = 0 := by
  funext g
  obtain ⟨p, hpd, hp⟩ := hφ g
  have h := orbit_exponentDifference 𝓕 J ha hp ((𝓕.positiveSplitComponent J).one_mem)
  simp only [polynomialDifference_eq_zero_of_mem_degree_zero _ hpd, Pi.zero_apply, mul_zero,
    unnormalizedAction, map_one, one_mul, parameterPower, characterLog_one, LinearMap.map_zero,
    Complex.exp_zero, mul_one] at h
  exact h

/-- Any `k + 1` differences, in arbitrary directions in the split component, annihilate an
orbit with degree bound `k`. The order is the ordinary product of endomorphisms. -/
theorem list_prod_exponentDifference_eq_zero_of_polynomialOrbit
    {lam : ComplexCharacterParameter F (𝓕.P J)} {k : ℕ} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasPolynomialOrbit J lam k φ) (xs : List (𝓕.positiveSplitComponent J))
    (hxs : xs.length = k + 1) :
    (xs.map (fun a : 𝓕.positiveSplitComponent J => 𝓕.unnormalizedExponentDifference J lam a)).prod
      φ = 0 := by
  induction xs using List.reverseRecOn generalizing k φ with
  | nil => simp at hxs
  | append_singleton xs a ih =>
    have hk : xs.length = k := by simpa only [List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] using hxs
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, Module.End.mul_apply]
    cases k with
    | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp hk
      simp only [hx, List.map_nil, List.prod_nil, Module.End.one_apply]
      exact exponentDifference_of_degree_zero 𝓕 J hφ a.2
    | succ k =>
      exact ih (polynomialOrbit_exponentDifference 𝓕 J hφ a.2) hk

/-- A normalized exponent `lam` is killed by mixed raw differences with roots taken at
`lam + ρ_P`. The required number of differences is uniform over all directions. -/
theorem HasExponent.exists_list_prod_exponentDifference_eq_zero
    {lam : ComplexCharacterParameter F (𝓕.P J)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasExponent J lam φ) :
    ∃ k : ℕ, ∀ xs : List (𝓕.positiveSplitComponent J), xs.length = k + 1 →
      (xs.map (fun a : 𝓕.positiveSplitComponent J => 𝓕.unnormalizedExponentDifference J
        (lam + halfModulusParameter F (𝓕.P J)) a)).prod φ = 0 := by
  obtain ⟨k, hk⟩ := (𝓕.hasExponent_iff J lam φ).mp hφ
  exact ⟨k, fun xs hxs =>
    𝓕.list_prod_exponentDifference_eq_zero_of_polynomialOrbit J hk xs hxs⟩

/-- A raw split-component shift obeys the pointwise power-sum equation of `Ξ_main`
with root `a^lam` and multiplicity `k + 1` for an orbit of degree at most `k`. -/
theorem isTranslationPolynomialSolution_pow_of_polynomialOrbit
    {lam : ComplexCharacterParameter F (𝓕.P J)} {k : ℕ} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasPolynomialOrbit J lam k φ) (a : 𝓕.positiveSplitComponent J) :
    IsTranslationPolynomialSolution (map F (𝓕.P J) G (𝓕.p J) a)
      ((X - C (parameterPower F (𝓕.P J) lam a)) ^ (k + 1)) φ := by
  have h := 𝓕.list_prod_exponentDifference_eq_zero_of_polynomialOrbit J hφ
    (List.replicate (k + 1) a) (List.length_replicate ..)
  rw [isTranslationPolynomialSolution_iff_aeval, map_pow, map_sub, aeval_X, aeval_C]
  simpa only [List.map_replicate, List.prod_replicate, unnormalizedExponentDifference] using h

/-- A normalized exponent `lam` gives translation equations with root `a^(lam + ρ_P)` for
the raw left shift and with a common multiplicity for every `a ∈ 𝔄_P`. -/
theorem HasExponent.exists_isTranslationPolynomialSolution_pow
    {lam : ComplexCharacterParameter F (𝓕.P J)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasExponent J lam φ) :
    ∃ k : ℕ, ∀ a : 𝓕.positiveSplitComponent J,
      IsTranslationPolynomialSolution (map F (𝓕.P J) G (𝓕.p J) a)
        ((X - C (parameterPower F (𝓕.P J) (lam + halfModulusParameter F (𝓕.P J)) a)) ^
          (k + 1)) φ := by
  obtain ⟨k, hk⟩ := (𝓕.hasExponent_iff J lam φ).mp hφ
  exact ⟨k, fun a => 𝓕.isTranslationPolynomialSolution_pow_of_polynomialOrbit J hk a⟩

end StandardParabolicFamily

end Langlands.Global
