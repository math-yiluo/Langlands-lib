import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Density of seminorms not vanishing at a given element -/

namespace Langlands.Analytic.SeparatedAnalytificationDensity

open Filter Topology

/-- A ring homomorphism into an algebraically closed field extends along an integral
algebra whose kernel it kills. -/
theorem exists_ringHom_comp_eq_of_isIntegral {R S Ω : Type*} [CommRing R] [CommRing S]
    [Field Ω] [IsAlgClosed Ω] [Algebra R S] [Algebra.IsIntegral R S] (χ : R →+* Ω)
    (hχ : RingHom.ker (algebraMap R S) ≤ RingHom.ker χ) :
    ∃ ψ : S →+* Ω, ψ.comp (algebraMap R S) = χ := by
  set p := RingHom.ker χ
  have : p.IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (fun r hr => hχ (by simpa [Ideal.under, RingHom.mem_ker] using hr))
  have : Q.LiesOver p := ⟨hQp.symm⟩
  let : Algebra (R ⧸ p) Ω := (RingHom.kerLift χ).toAlgebra
  have : FaithfulSMul (R ⧸ p) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective χ)
  have : IsDomain (S ⧸ Q) := Ideal.Quotient.isDomain Q
  let φ : (S ⧸ Q) →ₐ[R ⧸ p] Ω := IsAlgClosed.lift
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  change φ (Ideal.Quotient.mk Q (algebraMap R S r)) = χ r
  rw [← Ideal.Quotient.algebraMap_mk_of_liesOver Q p r, AlgHom.commutes]
  rfl

/-- A monic polynomial of positive degree over an algebraically closed normed field has a
root whose norm, raised to the degree, is at most the norm of the constant coefficient. -/
theorem exists_root_norm_pow_le {Ω : Type*} [NormedField Ω] [IsAlgClosed Ω]
    {q : Polynomial Ω} (hq : q.Monic) (hd : 0 < q.natDegree) :
    ∃ β, q.IsRoot β ∧ ‖β‖ ^ q.natDegree ≤ ‖q.coeff 0‖ := by
  classical
  have hspl : q.Splits := IsAlgClosed.splits q
  have hcard : q.roots.card = q.natDegree := hspl.natDegree_eq_card_roots.symm
  have hne : q.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨β, hβ, hmin⟩ := q.roots.toFinset.exists_min_image (fun x => ‖x‖₊) hne
  rw [Multiset.mem_toFinset] at hβ
  refine ⟨β, (Polynomial.mem_roots hq.ne_zero).mp hβ, ?_⟩
  have h0 : q.coeff 0 = (q.roots.map (fun a => 0 - a)).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hspl.eval_eq_prod_roots_of_monic hq]
  have hprod : ‖(q.roots.map (fun a => 0 - a)).prod‖₊ =
      (q.roots.map (fun a => ‖0 - a‖₊)).prod := by
    have := map_multiset_prod (nnnormHom (α := Ω)) (q.roots.map (fun a => 0 - a))
    simpa [Multiset.map_map] using this
  have key : ‖β‖₊ ^ q.natDegree ≤ ‖q.coeff 0‖₊ := by
    rw [h0, hprod]
    calc ‖β‖₊ ^ q.natDegree = ‖β‖₊ ^ Multiset.card (q.roots.map (fun a => ‖0 - a‖₊)) := by
          rw [Multiset.card_map, hcard]
      _ ≤ _ := Multiset.pow_card_le_prod (fun x hx => by
          obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
          simpa using hmin a (Multiset.mem_toFinset.mpr ha))
  have := NNReal.coe_le_coe.mpr key
  simpa using this

/-- A root of a monic polynomial over a normed field has norm at most the maximum of one
and the sum of the norms of the lower coefficients. -/
theorem norm_le_of_isRoot_of_monic {Ω : Type*} [NormedField Ω] {q : Polynomial Ω}
    (hq : q.Monic) {x : Ω} (hx : q.IsRoot x) :
    ‖x‖ ≤ max 1 (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) := by
  rcases le_or_gt ‖x‖ 1 with h1 | h1
  · exact le_max_of_le_left h1
  apply le_max_of_le_right
  have hn : q.natDegree ≠ 0 := by
    intro h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hq h0] at hx
    simp at hx
  have heval : x ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, q.coeff i * x ^ i := by
    have h := hx
    rw [Polynomial.IsRoot.def, hq.as_sum] at h
    simp [Polynomial.eval_finsetSum] at h
    linear_combination h
  have hx0 : 0 < ‖x‖ := by linarith
  have key : ‖x‖ ^ q.natDegree ≤
      (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) * ‖x‖ ^ (q.natDegree - 1) := by
    calc ‖x‖ ^ q.natDegree = ‖x ^ q.natDegree‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range q.natDegree, q.coeff i * x ^ i‖ := by rw [heval, norm_neg]
      _ ≤ ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i * x ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖ * ‖x‖ ^ (q.natDegree - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact pow_le_pow_right₀ h1.le (by simp at hi; omega)
      _ = _ := (Finset.sum_mul ..).symm
  have hpow : ‖x‖ ^ q.natDegree = ‖x‖ * ‖x‖ ^ (q.natDegree - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at key
  exact le_of_mul_le_mul_right key (pow_pos hx0 _)

/-- Pointwise bounded functions along an ultrafilter converge in the product topology. -/
theorem exists_tendsto_of_bounded {X : Type*} {D : Type*} (𝒰 : Ultrafilter X) (u : X → D → ℝ)
    (hb : ∀ d, ∃ B, ∀ᶠ x in (𝒰 : Filter X), u x d ∈ Set.Icc 0 B) :
    ∃ η : D → ℝ, Tendsto u 𝒰 (𝓝 η) := by
  choose B hB using hb
  have : ∀ d, ∃ y, Tendsto (fun x => u x d) 𝒰 (𝓝 y) := fun d => by
    obtain ⟨y, -, hy⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B d)).ultrafilter_le_nhds
      (𝒰.map (fun x => u x d)) (by rw [Filter.le_principal_iff]; exact hB d)
    exact ⟨y, hy⟩
  choose η hη using this
  exact ⟨η, tendsto_pi_nhds.mpr hη⟩

section Seminorms

variable {D : Type*} [CommRing D]

/-- The multiplicative seminorm `d ↦ ‖ψ d‖` of a ring homomorphism into a normed field. -/
def normComp {Ω : Type*} [NormedField Ω] (ψ : D →+* Ω) : MulRingSeminorm D where
  toFun d := ‖ψ d‖
  map_zero' := by simp
  add_le' a b := by simpa using norm_add_le (ψ a) (ψ b)
  neg' a := by simp
  map_one' := by simp
  map_mul' a b := by simp

@[simp] theorem normComp_apply {Ω : Type*} [NormedField Ω] (ψ : D →+* Ω) (d : D) :
    normComp ψ d = ‖ψ d‖ := rfl

variable (D) in
/-- The real functions on `D` satisfying the axioms of a multiplicative ring seminorm. -/
def seminormFunctions : Set (D → ℝ) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ a b, f (a + b) ≤ f a + f b) ∧ (∀ a, f (-a) = f a) ∧
    ∀ a b, f (a * b) = f a * f b}

theorem mem_seminormFunctions (ν : MulRingSeminorm D) : ⇑ν ∈ seminormFunctions D :=
  ⟨map_zero ν, map_one ν, map_add_le_add ν, map_neg_eq_map ν, map_mul ν⟩

variable (D) in
theorem isClosed_seminormFunctions : IsClosed (seminormFunctions D) := by
  have e : seminormFunctions D =
      {f : D → ℝ | f 0 = 0} ∩ ({f | f 1 = 1} ∩
        ((⋂ a, ⋂ b, {f | f (a + b) ≤ f a + f b}) ∩ ((⋂ a, {f | f (-a) = f a}) ∩
          ⋂ a, ⋂ b, {f | f (a * b) = f a * f b}))) := by
    ext f
    simp only [seminormFunctions, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  have h0 : IsClosed {f : D → ℝ | f 0 = 0} := isClosed_eq (continuous_apply 0) continuous_const
  have h1 : IsClosed {f : D → ℝ | f 1 = 1} := isClosed_eq (continuous_apply 1) continuous_const
  have h2 : IsClosed (⋂ a, ⋂ b, {f : D → ℝ | f (a + b) ≤ f a + f b}) := by
    refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
    exact isClosed_le (continuous_apply (a + b))
      ((continuous_apply a).add (continuous_apply b))
  have h3 : IsClosed (⋂ a, {f : D → ℝ | f (-a) = f a}) :=
    isClosed_iInter fun a => isClosed_eq (continuous_apply (-a)) (continuous_apply a)
  have h4 : IsClosed (⋂ a, ⋂ b, {f : D → ℝ | f (a * b) = f a * f b}) := by
    refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
    exact isClosed_eq (continuous_apply (a * b))
      ((continuous_apply a).mul (continuous_apply b))
  exact h0.inter (h1.inter (h2.inter (h3.inter h4)))

/-- A function satisfying the seminorm axioms, as a multiplicative ring seminorm. -/
def ofSeminormFunctions {f : D → ℝ} (hf : f ∈ seminormFunctions D) : MulRingSeminorm D where
  toFun := f
  map_zero' := hf.1
  add_le' := hf.2.2.1
  neg' := hf.2.2.2.1
  map_one' := hf.2.1
  map_mul' := hf.2.2.2.2

@[simp] theorem coe_ofSeminormFunctions {f : D → ℝ} (hf : f ∈ seminormFunctions D) :
    ⇑(ofSeminormFunctions hf) = f := rfl

/-- The kernel of a multiplicative ring seminorm, as a prime ideal. -/
def kernel (ν : MulRingSeminorm D) : Ideal D where
  carrier := {a | ν a = 0}
  add_mem' {a b} ha hb := le_antisymm
    ((map_add_le_add ν a b).trans (by simp [show ν a = 0 from ha, show ν b = 0 from hb]))
    (apply_nonneg ν _)
  zero_mem' := map_zero ν
  smul_mem' c a ha := by
    change ν (c * a) = 0
    rw [map_mul, show ν a = 0 from ha, mul_zero]

theorem mem_kernel {ν : MulRingSeminorm D} {a : D} : a ∈ kernel ν ↔ ν a = 0 := Iff.rfl

theorem kernel_isPrime (ν : MulRingSeminorm D) : (kernel ν).IsPrime where
  ne_top' h := by
    have : (1 : D) ∈ kernel ν := h ▸ Submodule.mem_top
    rw [mem_kernel, map_one] at this
    exact one_ne_zero this
  mem_or_mem' {a b} h := by
    rw [mem_kernel, map_mul] at h
    exact mul_eq_zero.mp h

end Seminorms

section Extension

open Polynomial

/-- A ring homomorphism into an algebraically closed normed field extends along an
integral extension of an integrally closed domain, so that the image of a chosen element
`e` has norm, raised to the degree of its minimal polynomial, at most the norm of the
image of the constant coefficient of that minimal polynomial. -/
theorem exists_ringHom_extend_root {P D Ω : Type*} [CommRing P] [IsDomain P]
    [IsIntegrallyClosed P] [CommRing D] [IsDomain D] [Algebra P D] [Algebra.IsIntegral P D]
    [FaithfulSMul P D] [NormedField Ω] [IsAlgClosed Ω] (e : D) (φ : P →+* Ω) :
    ∃ ψ : D →+* Ω, ψ.comp (algebraMap P D) = φ ∧
      ‖ψ e‖ ^ (minpoly P e).natDegree ≤ ‖φ ((minpoly P e).coeff 0)‖ := by
  have he : IsIntegral P e := Algebra.IsIntegral.isIntegral e
  have hm : (minpoly P e).Monic := minpoly.monic he
  have hmap : ((minpoly P e).map φ).Monic := hm.map φ
  have hdeg : ((minpoly P e).map φ).natDegree = (minpoly P e).natDegree := hm.natDegree_map φ
  obtain ⟨β, hβ, hβn⟩ := exists_root_norm_pow_le hmap
    (by rw [hdeg]; exact minpoly.natDegree_pos he)
  rw [hdeg, coeff_map] at hβn
  let ρ : P[X] →+* Ω := eval₂RingHom φ β
  let : Algebra P[X] D := (aeval e).toRingHom.toAlgebra
  have h1 : algebraMap P[X] D X = e := by
    change aeval e X = e
    exact aeval_X e
  have h2 : ∀ r : P, algebraMap P[X] D (C r) = algebraMap P D r := fun r => by
    change aeval e (C r) = _
    exact aeval_C e r
  have : IsScalarTower P P[X] D := IsScalarTower.of_algebraMap_eq fun r => (h2 r).symm
  have : Algebra.IsIntegral P[X] D := Algebra.IsIntegral.tower_top P
  have hker : RingHom.ker (algebraMap P[X] D) ≤ RingHom.ker ρ := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    obtain ⟨r, rfl⟩ := minpoly.isIntegrallyClosed_dvd he (p := p) hp
    have h0 : ρ (minpoly P e) = 0 := by
      change eval₂ φ β (minpoly P e) = 0
      rw [← eval_map]
      exact hβ
    rw [map_mul, h0, zero_mul]
  obtain ⟨ψ, hψ⟩ := exists_ringHom_comp_eq_of_isIntegral ρ hker
  have hψe : ψ e = β := by
    calc ψ e = (ψ.comp (algebraMap P[X] D)) X := by rw [RingHom.comp_apply, h1]
      _ = ρ X := by rw [hψ]
      _ = β := eval₂_X φ β
  refine ⟨ψ, ?_, by rw [hψe]; exact hβn⟩
  ext r
  calc ψ (algebraMap P D r) = (ψ.comp (algebraMap P[X] D)) (C r) := by
        rw [RingHom.comp_apply, h2]
    _ = ρ (C r) := by rw [hψ]
    _ = φ r := eval₂_C φ β

end Extension

/-- In a finite algebra, a maximal ideal contains an element lying in no other prime ideal
with the same contraction. -/
theorem exists_mem_eq_of_mem_of_under_eq {P D : Type*} [CommRing P] [CommRing D]
    [Algebra P D] [Module.Finite P D] (𝔪 : Ideal D) [h𝔪 : 𝔪.IsMaximal] :
    ∃ e ∈ 𝔪, ∀ Q : Ideal D, Q.IsPrime → Q.under P = 𝔪.under P → e ∈ Q → Q = 𝔪 := by
  classical
  set S := (𝔪.under P).primesOver D \ {𝔪}
  have hS : S.Finite := (Algebra.QuasiFinite.finite_primesOver (𝔪.under P)).sdiff
  have hnot : ¬ ((𝔪 : Set D) ⊆
      ⋃ Q ∈ (↑hS.toFinset : Set (Ideal D)), ((id Q : Ideal D) : Set D)) := by
    rw [Ideal.subset_union_prime (s := hS.toFinset) (f := id) ⊥ ⊥ ?_]
    · rintro ⟨Q, hQ, hle⟩
      rw [Set.Finite.mem_toFinset] at hQ
      obtain ⟨⟨hQp, -⟩, hne⟩ := hQ
      exact hne (h𝔪.eq_of_le hQp.ne_top hle).symm
    · intro Q hQ _ _
      rw [Set.Finite.mem_toFinset] at hQ
      exact hQ.1.1
  obtain ⟨e, he𝔪, heQ⟩ := Set.not_subset.mp hnot
  refine ⟨e, he𝔪, fun Q hQ hQu heQ' => ?_⟩
  by_contra hne
  apply heQ
  rw [Set.mem_iUnion₂]
  refine ⟨Q, ?_, heQ'⟩
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  exact ⟨⟨hQ, ⟨hQu.symm⟩⟩, hne⟩

section Main

open MvPolynomial

variable {K Ω D : Type*} [NormedField K] [NontriviallyNormedField Ω] [IsAlgClosed Ω]
  [Algebra K Ω] [CommRing D] [IsDomain D] [Algebra K D]

/-- The core density statement over a Noether normalization: a rigid point `χ` with kernel
`𝔪` is the kernel of a limit of seminorms `d ↦ ‖ψ d‖` that do not vanish at `g`. -/
theorem exists_mulRingSeminorm_kernel_eq_of_finite
    (hΩ : ∀ c : K, ‖algebraMap K Ω c‖ = ‖c‖) {s : ℕ}
    [Algebra (MvPolynomial (Fin s) K) D] [IsScalarTower K (MvPolynomial (Fin s) K) D]
    [Module.Finite (MvPolynomial (Fin s) K) D] [FaithfulSMul (MvPolynomial (Fin s) K) D]
    (𝔪 : Ideal D) [𝔪.IsMaximal] (χ : D →ₐ[K] Ω) (hχ : RingHom.ker χ = 𝔪)
    {g : D} (hg : g ≠ 0) :
    ∃ η : MulRingSeminorm D, (∀ c : K, η (algebraMap K D c) = ‖c‖) ∧ kernel η = 𝔪 ∧
      ⇑η ∈ closure {f : D → ℝ | ∃ ν : MulRingSeminorm D,
        (∀ c : K, ν (algebraMap K D c) = ‖c‖) ∧ ν g ≠ 0 ∧ ⇑ν = f} := by
  classical
  have hιK : ∀ c : K, algebraMap (MvPolynomial (Fin s) K) D (C c) = algebraMap K D c :=
    fun c => by rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  -- the rigid point on the Noether normalization
  let t : Fin s → Ω := fun i => χ (algebraMap (MvPolynomial (Fin s) K) D (X i))
  have ht : ∀ p, χ (algebraMap (MvPolynomial (Fin s) K) D p) = aeval t p := by
    intro p
    have : χ.comp (IsScalarTower.toAlgHom K (MvPolynomial (Fin s) K) D) = aeval t :=
      MvPolynomial.algHom_ext fun i => by
        rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, aeval_X]
    exact DFunLike.congr_fun this p
  -- an element of `𝔪` lying in no other prime over the same contraction
  obtain ⟨e, he𝔪, heu⟩ := exists_mem_eq_of_mem_of_under_eq (P := MvPolynomial (Fin s) K) 𝔪
  -- a nonzero multiple of `g` coming from the Noether normalization
  have hgI : (Ideal.span {g}).under (MvPolynomial (Fin s) K) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hg (Ideal.mem_span_singleton_self g)
      (Algebra.IsIntegral.isIntegral g)
  obtain ⟨cg, hcgmem, hcg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hgI
  rw [Ideal.mem_under, Ideal.mem_span_singleton'] at hcgmem
  obtain ⟨h, hh⟩ := hcgmem
  -- the minimal polynomial of `e`
  set m := minpoly (MvPolynomial (Fin s) K) e with hm
  have hd : 0 < m.natDegree := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral e)
  have ha0𝔪 : algebraMap (MvPolynomial (Fin s) K) D (m.coeff 0) ∈ 𝔪 := by
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := m)
    have h1 := congrArg (Polynomial.aeval e) hq
    rw [map_sub, hm, minpoly.aeval, Polynomial.aeval_C, map_mul, Polynomial.aeval_X,
      zero_sub, ← hm] at h1
    have h2 : algebraMap (MvPolynomial (Fin s) K) D (m.coeff 0) =
        -(e * Polynomial.aeval e q) := by
      rw [← h1, neg_neg]
    rw [h2]
    exact 𝔪.neg_mem (𝔪.mul_mem_right _ he𝔪)
  have ha0 : aeval t (m.coeff 0) = 0 := by
    rw [← ht, ← RingHom.mem_ker, hχ]
    exact ha0𝔪
  -- the extensions `ψ x` of the points `x` of affine space
  have hψ : ∀ x : Fin s → Ω, ∃ ψ : D →+* Ω,
      ψ.comp (algebraMap (MvPolynomial (Fin s) K) D) = (aeval x).toRingHom ∧
      ‖ψ e‖ ^ m.natDegree ≤ ‖(aeval x).toRingHom (m.coeff 0)‖ := fun x =>
    exists_ringHom_extend_root (P := MvPolynomial (Fin s) K) e (aeval x).toRingHom
  choose ψ hψι hψe using hψ
  have hψι' : ∀ x p, ψ x (algebraMap (MvPolynomial (Fin s) K) D p) = aeval x p :=
    fun x p => DFunLike.congr_fun (hψι x) p
  have hext : ∀ x (c : K), ‖ψ x (algebraMap K D c)‖ = ‖c‖ := fun x c => by
    rw [← hιK c, hψι' x, aeval_C, hΩ]
  -- continuity of evaluation
  have hevalmap : ∀ (x : Fin s → Ω) (p : MvPolynomial (Fin s) K),
      aeval x p = eval x (MvPolynomial.map (algebraMap K Ω) p) := fun x p => by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]
  have hcont : ∀ p : MvPolynomial (Fin s) K, Continuous fun x : Fin s → Ω => aeval x p :=
    fun p => by
      simp_rw [hevalmap]
      exact MvPolynomial.continuous_eval _
  -- `t` is in the closure of the points where `cg` does not vanish
  have hcgmap : MvPolynomial.map (algebraMap K Ω) cg ≠ 0 := by
    intro h0
    apply hcg0
    exact MvPolynomial.map_injective _ (algebraMap K Ω).injective (by rw [h0, map_zero])
  have hS : t ∈ closure {x : Fin s → Ω | aeval x cg ≠ 0} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    apply hcgmap
    refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε)
      (fun i => infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds _ hε)) fun x hx => ?_
    rw [map_zero, ← hevalmap]
    by_contra hne
    have h1 := hcon x hne
    have h2 : dist t x < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      rw [dist_comm]
      exact hx i (Set.mem_univ i)
    linarith
  have : (𝓝[{x : Fin s → Ω | aeval x cg ≠ 0}] t).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hS
  let 𝒰 : Ultrafilter (Fin s → Ω) := Ultrafilter.of (𝓝[{x : Fin s → Ω | aeval x cg ≠ 0}] t)
  have h𝒰 : (𝒰 : Filter (Fin s → Ω)) ≤ 𝓝[{x : Fin s → Ω | aeval x cg ≠ 0}] t :=
    Ultrafilter.of_le _
  have h𝒰t : (𝒰 : Filter (Fin s → Ω)) ≤ 𝓝 t := h𝒰.trans nhdsWithin_le_nhds
  have h𝒰S : ∀ᶠ x in (𝒰 : Filter (Fin s → Ω)), aeval x cg ≠ 0 := h𝒰 self_mem_nhdsWithin
  -- pointwise bounds
  have hb : ∀ d : D, ∃ B, ∀ᶠ x in (𝒰 : Filter (Fin s → Ω)),
      (fun x => ⇑(normComp (ψ x))) x d ∈ Set.Icc 0 B := by
    intro d
    set q := minpoly (MvPolynomial (Fin s) K) d with hqdef
    have hq : q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral d)
    let F : (Fin s → Ω) → ℝ :=
      fun x => max 1 (∑ i ∈ Finset.range q.natDegree, ‖aeval x (q.coeff i)‖)
    have hF : Continuous F :=
      continuous_const.max (continuous_finsetSum _ fun i _ => (hcont _).norm)
    refine ⟨F t + 1, ?_⟩
    have hev : ∀ᶠ x in (𝒰 : Filter (Fin s → Ω)), F x < F t + 1 :=
      h𝒰t (hF.continuousAt.eventually_lt continuousAt_const (lt_add_one _))
    filter_upwards [hev] with x hx
    refine ⟨apply_nonneg _ _, ?_⟩
    have hroot : (q.map (aeval x).toRingHom).IsRoot (ψ x d) := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← hψι x, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hqdef, minpoly.aeval, map_zero]
    have h1 := norm_le_of_isRoot_of_monic (hq.map _) hroot
    rw [hq.natDegree_map] at h1
    simp only [Polynomial.coeff_map] at h1
    change ‖ψ x d‖ ≤ F t + 1
    exact h1.trans hx.le
  -- the limit seminorm
  obtain ⟨η₀, hη₀⟩ := exists_tendsto_of_bounded 𝒰 (fun x => ⇑(normComp (ψ x))) hb
  have hmem : η₀ ∈ seminormFunctions D :=
    (isClosed_seminormFunctions D).mem_of_tendsto hη₀
      (Eventually.of_forall fun x => mem_seminormFunctions _)
  let η := ofSeminormFunctions hmem
  have hη : ∀ d, Tendsto (fun x => ‖ψ x d‖) (𝒰 : Filter (Fin s → Ω)) (𝓝 (η d)) :=
    fun d => tendsto_pi_nhds.mp hη₀ d
  have hηP : ∀ p, η (algebraMap (MvPolynomial (Fin s) K) D p) = ‖aeval t p‖ := fun p =>
    tendsto_nhds_unique (hη _) ((((hcont p).norm.tendsto t).mono_left h𝒰t).congr
      fun x => by rw [hψι' x p])
  have hηe : η e = 0 := by
    have h1 : η e ^ m.natDegree ≤ ‖aeval t (m.coeff 0)‖ :=
      le_of_tendsto_of_tendsto' ((hη e).pow _) (((hcont _).norm.tendsto t).mono_left h𝒰t)
        fun x => hψe x
    rw [ha0, norm_zero] at h1
    exact (pow_eq_zero_iff hd.ne').mp (le_antisymm h1 (pow_nonneg (apply_nonneg η e) _))
  refine ⟨η, fun c => tendsto_nhds_unique (hη _)
    ((tendsto_const_nhds (x := ‖c‖)).congr fun x => (hext x c).symm), ?_, ?_⟩
  · apply heu _ (kernel_isPrime η) _ (mem_kernel.mpr hηe)
    ext p
    rw [Ideal.mem_under, Ideal.mem_under, mem_kernel, hηP, norm_eq_zero, ← ht, ← hχ,
      RingHom.mem_ker]
  · apply mem_closure_of_tendsto hη₀
    filter_upwards [h𝒰S] with x hx
    refine ⟨normComp (ψ x), fun c => hext x c, ?_, rfl⟩
    intro h0
    rw [normComp_apply, norm_eq_zero] at h0
    apply hx
    rw [← hψι', ← hh, map_mul, h0, mul_zero]

/-- **Density lemma.** Let `D` be a domain of finite type over a normed field `K`, let `I` be
a proper ideal and `g ≠ 0`. Given an algebraically closed nontrivially normed field `Ω`
extending the norm of `K`, there is a multiplicative seminorm on `D` extending the norm of
`K`, vanishing on `I`, and lying in the closure (for pointwise convergence) of the
seminorms extending the norm of `K` that do not vanish at `g`. -/
theorem exists_mulRingSeminorm_mem_closure_of_isAlgClosed
    (hΩ : ∀ c : K, ‖algebraMap K Ω c‖ = ‖c‖) [Algebra.FiniteType K D]
    (I : Ideal D) (hI : I ≠ ⊤) {g : D} (hg : g ≠ 0) :
    ∃ η : MulRingSeminorm D, (∀ c : K, η (algebraMap K D c) = ‖c‖) ∧ (∀ a ∈ I, η a = 0) ∧
      ⇑η ∈ closure {f : D → ℝ | ∃ ν : MulRingSeminorm D,
        (∀ c : K, ν (algebraMap K D c) = ‖c‖) ∧ ν g ≠ 0 ∧ ⇑ν = f} := by
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
  let := Ideal.Quotient.field 𝔪
  have : Module.Finite K (D ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing K (D ⧸ 𝔪)
  let χ₀ : (D ⧸ 𝔪) →ₐ[K] Ω := IsAlgClosed.lift
  have hinj : Function.Injective χ₀ := χ₀.toRingHom.injective
  let χ : D →ₐ[K] Ω := χ₀.comp (Ideal.Quotient.mkₐ K 𝔪)
  have hχ : RingHom.ker χ = 𝔪 := by
    ext a
    rw [RingHom.mem_ker, AlgHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨s, ι, hιinj, hιfin⟩ := exists_finite_inj_algHom_of_fg K D
  let : Algebra (MvPolynomial (Fin s) K) D := ι.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin s) K) D :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  have : Module.Finite (MvPolynomial (Fin s) K) D := hιfin
  have : FaithfulSMul (MvPolynomial (Fin s) K) D :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hιinj
  obtain ⟨η, hext, hker, hcl⟩ := exists_mulRingSeminorm_kernel_eq_of_finite hΩ (s := s) 𝔪 χ hχ hg
  exact ⟨η, hext, fun a ha => mem_kernel.mp (hker ▸ hI𝔪 ha), hcl⟩

end Main

/-- **Density lemma** over a complete ultrametric nontrivially normed field: let `D` be a
domain of finite type over `K`, `I` a proper ideal and `g ≠ 0`. There is a multiplicative
seminorm on `D` extending the norm of `K`, vanishing on `I`, and lying in the closure (for
pointwise convergence) of the seminorms extending the norm of `K` that do not vanish
at `g`. -/
theorem exists_mulRingSeminorm_mem_closure {K D : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [IsUltrametricDist K] [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] (I : Ideal D) (hI : I ≠ ⊤) {g : D} (hg : g ≠ 0) :
    ∃ η : MulRingSeminorm D, (∀ c : K, η (algebraMap K D c) = ‖c‖) ∧ (∀ a ∈ I, η a = 0) ∧
      ⇑η ∈ closure {f : D → ℝ | ∃ ν : MulRingSeminorm D,
        (∀ c : K, ν (algebraMap K D c) = ‖c‖) ∧ ν g ≠ 0 ∧ ⇑ν = f} := by
  let := spectralNorm.nontriviallyNormedField K (AlgebraicClosure K)
  exact exists_mulRingSeminorm_mem_closure_of_isAlgClosed (Ω := AlgebraicClosure K)
    (fun c => spectralNorm_extends c) I hI hg

end Langlands.Analytic.SeparatedAnalytificationDensity
