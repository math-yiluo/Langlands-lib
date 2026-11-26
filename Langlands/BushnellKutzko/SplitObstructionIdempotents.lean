import Langlands.BushnellKutzko.FundamentalStratum
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic
import Langlands.BushnellKutzko.SplitObstructionRiccati
import Nyll.ValuedFieldTheory.Valuation.Henselian.CoprimeFactorLifting

/-! # Idempotents attached to a split fundamental stratum

For a split fundamental stratum `[𝔅, n, n−1, b]` in `End_E(V)`, with `E` a finite extension
of a nonarchimedean local field, the element `y_b = π_E^{n/g} b^{e/g}` lies in `𝔅` and its
characteristic polynomial has integral coefficients. The reduction has two distinct monic
irreducible factors, so Hensel's lemma (over the complete ring `𝔬_E`) splits the integral
characteristic polynomial into two coprime monic factors of positive degree. The resulting
complementary idempotents are polynomials in `y_b` with coefficients in `𝔬_E`; they are
nonzero, lie in `𝔅`, commute with `b`, and the block `e₁ End_E(V) e₂` has graded injective
commutator with `b`.

This is the splitting construction recalled in Bushnell–Kutzko (1993), (2.3.9)–(2.3.10),
printed p. 60, without the coarsening of the chain to `gcd(n, e) = 1` used there: the
graded injectivity of the commutator, the content of (2.3.8)(iii) used in the proof of
(2.3.12), is obtained directly from the idempotent `e₂ ∈ 𝔬_E[y_b]`.
-/

noncomputable section

open ValuativeRel Polynomial
open scoped Pointwise

namespace Langlands.BushnellKutzko.SplitObstruction

universe uF uV uE

/-! ### Generic polynomial facts -/

section Generic

/-- Reducing the image of an integral polynomial gives its coefficientwise reduction. -/
theorem reduceIntegralPolynomial_map {O K : Type*} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (Φ : O[X]) :
    reduceIntegralPolynomial O K (Φ.map (algebraMap O K)) =
      Φ.map (Ideal.Quotient.mk (Ring.jacobson O)) := by
  classical
  ext n
  simp only [reduceIntegralPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_map]
  by_cases hn : n ∈ (Φ.map (algebraMap O K)).support
  · rw [Finset.sum_eq_single n]
    · simp only [↓reduceIte]
      split
      · rename_i h
        congr 1
        apply hinj
        simpa using Classical.choose_spec h
      · rename_i h
        exact (h ⟨Φ.coeff n, by simp⟩).elim
    · intro i _ hin
      simp [hin]
    · intro h
      exact (h hn).elim
  · rw [Finset.sum_eq_zero]
    · have h0 : (Φ.map (algebraMap O K)).coeff n = 0 := Polynomial.notMem_support_iff.mp hn
      rw [coeff_map] at h0
      have h0' : Φ.coeff n = 0 := hinj (by rw [h0, map_zero])
      rw [h0', map_zero]
    · intro i hi
      have hin : i ≠ n := by
        rintro rfl
        exact hn hi
      simp [hin]

/-- An endomorphism preserving a lattice over a principal ideal domain has an integral
characteristic polynomial. -/
theorem exists_integral_charpoly {O K V : Type*} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) [M.IsLattice K] (x : Module.End K V) (hx : ∀ v ∈ M, x v ∈ M) :
    ∃ Φ : O[X], Φ.Monic ∧ Φ.map (algebraMap O K) = x.charpoly := by
  classical
  have : Module.Finite O M := Module.Finite.iff_fg.mpr (Submodule.IsLattice.fg (A := K))
  let b := Module.Free.chooseBasis O M
  let bK := b.extendOfIsLattice K
  let x₀ : M →ₗ[O] M := (x.restrictScalars O).restrict hx
  refine ⟨(LinearMap.toMatrix b b x₀).charpoly, Matrix.charpoly_monic _, ?_⟩
  have hmat : (LinearMap.toMatrix b b x₀).map (algebraMap O K) = LinearMap.toMatrix bK bK x := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    set c := b.repr (x₀ (b j)) with hc
    have hxj : x (bK j) = ∑ k, algebraMap O K (c k) • bK k := by
      have hsum : ∑ k, c k • b k = x₀ (b j) := b.sum_repr (x₀ (b j))
      have h2 : ((x₀ (b j) : M) : V) = x (bK j) := by
        rw [Module.Basis.extendOfIsLattice_apply]
        rfl
      calc x (bK j) = ((x₀ (b j) : M) : V) := h2.symm
        _ = ((∑ k, c k • b k : M) : V) := by rw [hsum]
        _ = ∑ k, algebraMap O K (c k) • bK k := by
          rw [Submodule.coe_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Submodule.coe_smul, Module.Basis.extendOfIsLattice_apply, algebraMap_smul]
    rw [hxj, Module.Basis.repr_sum_self]
  rw [← Matrix.charpoly_map, hmat, LinearMap.charpoly_toMatrix]

/-- A polynomial of positive degree dividing the characteristic polynomial of an
endomorphism is not invertible at that endomorphism. -/
theorem not_isUnit_aeval_of_dvd_charpoly {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (x : Module.End K V) {h : K[X]}
    (hdeg : 0 < h.natDegree) (hdvd : h ∣ x.charpoly) : ¬ IsUnit (aeval x h) := by
  classical
  intro hu
  let b := Module.finBasis K V
  let M := LinearMap.toMatrixAlgEquiv b x
  let Ω := AlgebraicClosure K
  let φ := (Algebra.ofId K Ω).mapMatrix (m := Fin (Module.finrank K V))
  have hM : M.charpoly = x.charpoly := by
    have hMeq : M = LinearMap.toMatrix b b x := rfl
    rw [hMeq]
    exact LinearMap.charpoly_toMatrix x b
  have huM : IsUnit (aeval M h) := by
    rw [show aeval M h = LinearMap.toMatrixAlgEquiv b (aeval x h) from
      aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b) x h]
    exact hu.map _
  have huΩ : IsUnit (aeval (φ M) h) := by
    rw [aeval_algHom_apply]
    exact huM.map φ
  have hdeg' : (h.map (algebraMap K Ω)).degree ≠ 0 := by
    rw [degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (h.map (algebraMap K Ω)) hdeg'
  have hφM : φ M = M.map (algebraMap K Ω) := rfl
  have hcp : (φ M).charpoly = x.charpoly.map (algebraMap K Ω) := by
    rw [hφM, Matrix.charpoly_map, hM]
  have hroot : (φ M).charpoly.IsRoot c := by
    obtain ⟨d, hd⟩ := hdvd
    rw [hcp, hd, Polynomial.map_mul, IsRoot, eval_mul, hc.eq_zero, zero_mul]
  have hspec : c ∈ spectrum Ω (φ M) := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have h0 := spectrum.subset_polynomial_aeval (φ M) (h.map (algebraMap K Ω)) ⟨c, hspec, rfl⟩
  simp only [hc.eq_zero] at h0
  rw [spectrum.zero_mem_iff, aeval_map_algebraMap] at h0
  exact h0 huΩ

/-- Two distinct monic irreducible divisors of a monic polynomial over a field give a
factorization into coprime monic factors of positive degree. -/
theorem exists_coprime_split {k : Type*} [Field k] {φ p q : k[X]} (hφ : φ.Monic)
    (hp : p.Monic) (hq : q.Monic) (hpi : Irreducible p) (hqi : Irreducible q) (hpq : p ≠ q)
    (hpφ : p ∣ φ) (hqφ : q ∣ φ) :
    ∃ g h : k[X], g.Monic ∧ h.Monic ∧ φ = g * h ∧ IsCoprime g h ∧
      0 < g.natDegree ∧ 0 < h.natDegree := by
  classical
  have hfin : FiniteMultiplicity p φ :=
    finiteMultiplicity_of_degree_pos_of_monic
      (natDegree_pos_iff_degree_pos.mp hpi.natDegree_pos) hp hφ.ne_zero
  obtain ⟨c, hc, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set m := multiplicity p φ
  have hcm : c.Monic := Monic.of_mul_monic_left (hp.pow m) (hc ▸ hφ)
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, pow_zero, one_mul] at hc
    exact hnd (hc ▸ hpφ)
  have hqc : q ∣ c := by
    rcases hqi.prime.dvd_or_dvd (hc ▸ hqφ) with h | h
    · have hqp : q ∣ p := hqi.prime.dvd_of_dvd_pow h
      exact (hpq (eq_of_monic_of_associated hp hq (hqi.associated_of_dvd hpi hqp).symm)).elim
    · exact h
  refine ⟨p ^ m, c, hp.pow m, hcm, hc, (hpi.coprime_iff_not_dvd.mpr hnd).pow_left, ?_, ?_⟩
  · rw [hp.natDegree_pow]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hm) hpi.natDegree_pos
  · exact lt_of_lt_of_le hqi.natDegree_pos (natDegree_le_of_dvd hqc hcm.ne_zero)

end Generic

/-! ### The integer ring of the extension -/

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]


omit [Module F V] [IsScalarTower F E V] in
/-- The integer ring of a finite extension is Henselian along its maximal ideal. -/
theorem henselianRing_subfieldIntegers [FiniteDimensional F E] :
    HenselianRing (subfieldIntegers F E) (Ring.jacobson (subfieldIntegers F E)) := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  let := Langlands.LocalField.FiniteExtension.normedField F E
  let := Langlands.LocalField.FiniteExtension.valuativeRel F E
  have := Langlands.LocalField.FiniteExtension.isLocalField F E
  have h : IsAdicComplete 𝓂[E] 𝒪[E] := inferInstance
  let e := (subfieldIntegerEquiv F E).symm
  have h2 : IsAdicComplete (Ideal.map e 𝓂[E]) (subfieldIntegers F E) :=
    (IsAdicComplete.congr_ringEquiv 𝓂[E] e).mpr h
  have hmax : (Ideal.map e 𝓂[E]).IsMaximal := Ideal.map_isMaximal_of_equiv e
  have heq : Ideal.map e 𝓂[E] = Ring.jacobson (subfieldIntegers F E) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact IsLocalRing.eq_maximalIdeal hmax
  rw [← heq]
  infer_instance

/-! ### Lattice chains over the integer ring -/

section Chain

variable (𝓜 : LatticeChain (subfieldIntegers F E) E V) (π : RingPrimeElement (subfieldIntegers F E))

local notation "Q" => 𝓜.endFiltration

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
/-- The chosen prime element moves the chain by one period. -/
theorem prime_smul_mem_lattice (i : ℤ) {v : V} (hv : v ∈ 𝓜.lattice i) :
    (algebraMap (subfieldIntegers F E) E π.1) • v ∈ 𝓜.lattice (i + 𝓜.period) := by
  rw [𝓜.lattice_add_period]
  have hπJ : π.1 ∈ Ring.jacobson (subfieldIntegers F E) := by
    have h : π.1 ∈ Ideal.span ({π.1} : Set (subfieldIntegers F E)) :=
      Ideal.subset_span (Set.mem_singleton _)
    rwa [π.2.2] at h
  rw [algebraMap_smul]
  exact Submodule.smul_mem_smul hπJ hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
theorem prime_inv_smul_mem_lattice (i : ℤ) {v : V} (hv : v ∈ 𝓜.lattice (i + 𝓜.period)) :
    (algebraMap (subfieldIntegers F E) E π.1)⁻¹ • v ∈ 𝓜.lattice i := by
  have hπ0 : algebraMap (subfieldIntegers F E) E π.1 ≠ 0 := fun h => π.2.1 (Subtype.ext h)
  have hJ : Ring.jacobson (subfieldIntegers F E) = Ideal.span {π.1} := π.2.2.symm
  rw [𝓜.lattice_add_period, hJ, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [← algebraMap_smul E π.1 w, smul_smul, inv_mul_cancel₀ hπ0, one_smul]
  exact hw

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
/-- Integer powers of the prime element move the chain by the corresponding multiple of
the period. -/
theorem prime_zpow_smul_mem_lattice (k i : ℤ) {v : V} (hv : v ∈ 𝓜.lattice i) :
    (algebraMap (subfieldIntegers F E) E π.1) ^ k • v ∈ 𝓜.lattice (i + k * 𝓜.period) := by
  have hπ0 : algebraMap (subfieldIntegers F E) E π.1 ≠ 0 := fun h => π.2.1 (Subtype.ext h)
  induction k using Int.induction_on with
  | zero => simpa using hv
  | succ k ih =>
    have hpow : (algebraMap (subfieldIntegers F E) E π.1) ^ ((k : ℤ) + 1) =
        algebraMap (subfieldIntegers F E) E π.1 *
          (algebraMap (subfieldIntegers F E) E π.1) ^ (k : ℤ) := by
      rw [zpow_add_one₀ hπ0, mul_comm]
    rw [hpow, mul_smul]
    have h := prime_smul_mem_lattice 𝓜 π _ ih
    convert h using 2
    ring
  | pred k ih =>
    have hpow : (algebraMap (subfieldIntegers F E) E π.1) ^ (-(k : ℤ) - 1) =
        (algebraMap (subfieldIntegers F E) E π.1)⁻¹ *
          (algebraMap (subfieldIntegers F E) E π.1) ^ (-(k : ℤ)) := by
      rw [zpow_sub_one₀ hπ0, mul_comm]
    rw [hpow, mul_smul]
    apply prime_inv_smul_mem_lattice 𝓜 π
    convert ih using 2
    ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
theorem prime_zpow_smul_mem_endFiltration (k m : ℤ) {x : Module.End E V} (hx : x ∈ Q m) :
    (algebraMap (subfieldIntegers F E) E π.1) ^ k • x ∈ Q (m + k * 𝓜.period) := by
  intro i v hv
  rw [LinearMap.smul_apply]
  have h := prime_zpow_smul_mem_lattice 𝓜 π k (i + m) (hx i v hv)
  convert h using 2
  ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
theorem pow_mem_endFiltration {m : ℤ} {x : Module.End E V} (hx : x ∈ Q m) (k : ℕ) :
    x ^ k ∈ Q (k * m) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact 𝓜.mem_order_iff_mem_endFiltration.mp 𝓜.order.one_mem
  | succ k ih =>
    rw [pow_succ]
    have h := 𝓜.mul_mem_endFiltration ih hx
    convert h using 2
    push_cast
    ring

end Chain

/-! ### The element `y_b` of a stratum -/

section Element

variable (D : Stratum (subfieldIntegers F E) E V) (π : RingPrimeElement (subfieldIntegers F E))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
/-- The exponents of `y_b` balance: `n · (e/g) = (n/g) · e`. -/
theorem fundamental_exponents :
    (D.n : ℤ) * ((D.chain.period / Nat.gcd D.chain.period D.n.natAbs : ℕ) : ℤ) =
      D.n / (Nat.gcd D.chain.period D.n.natAbs : ℤ) * D.chain.period := by
  set e := D.chain.period
  set g := Nat.gcd e D.n.natAbs
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ D.chain.period_pos
  obtain ⟨e', he'⟩ := Nat.gcd_dvd_left e D.n.natAbs
  obtain ⟨n', hn'⟩ : (g : ℤ) ∣ D.n := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right e D.n.natAbs)
  have h1 : e / g = e' := by
    rw [show e = g * e' from he']
    exact Nat.mul_div_cancel_left e' hgpos
  have h2 : D.n / (g : ℤ) = n' := by
    rw [hn']
    exact Int.mul_ediv_cancel_left n' (by exact_mod_cast hgpos.ne')
  rw [h1, h2, hn']
  have : (e : ℤ) = g * e' := by exact_mod_cast he'
  rw [this]
  ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V]
  [IsScalarTower F E V] in
/-- The element `y_b` lies in the order of the chain. -/
theorem fundamentalElement_mem_order (hb : D.b ∈ D.chain.endFiltration (-D.n)) :
    D.fundamentalElement π ∈ D.chain.endFiltration 0 := by
  have h1 := pow_mem_endFiltration D.chain hb
    (D.chain.period / Nat.gcd D.chain.period D.n.natAbs)
  have h2 := prime_zpow_smul_mem_endFiltration D.chain π
    (D.n / (Nat.gcd D.chain.period D.n.natAbs : ℤ))
    (((D.chain.period / Nat.gcd D.chain.period D.n.natAbs : ℕ) : ℤ) * -D.n) h1
  have hexp := fundamental_exponents D
  dsimp only [Stratum.fundamentalElement]
  convert h2 using 2
  linear_combination hexp

end Element

/-! ### The idempotents -/

omit [Module F V] [IsScalarTower F E V] in
set_option maxHeartbeats 1000000 in
/-- **The splitting idempotents.** A split fundamental stratum `D` over the integers of a
finite extension `E` gives complementary nonzero idempotents of the order, commuting with
`D.b`, such that on the block `e₁ End_E(V) e₂` the commutator with `D.b` is injective on
each graded step: it maps `𝔔^i ∖ 𝔔^{i+1}` outside `𝔔^{i−n+1}`. -/
theorem exists_split_idempotents [FiniteDimensional F E] (D : Stratum (subfieldIntegers F E) E V)
    (hsplit : D.IsSplit) (hb : D.b ∈ D.chain.endFiltration (-D.n)) :
    ∃ e₁ e₂ : Module.End E V, e₁ + e₂ = 1 ∧ e₁ * e₂ = 0 ∧ e₁ ≠ 0 ∧ e₂ ≠ 0 ∧
      e₁ ∈ D.chain.endFiltration 0 ∧ e₂ ∈ D.chain.endFiltration 0 ∧
      Commute e₁ D.b ∧ Commute e₂ D.b ∧
      ∀ (i : ℤ) (x : Module.End E V), x ∈ D.chain.endFiltration i → e₁ * x * e₂ = x →
        D.b * x - x * D.b ∈ D.chain.endFiltration (i - D.n + 1) →
        x ∈ D.chain.endFiltration (i + 1) := by
  classical
  obtain ⟨-, π, p, q, hpm, hqm, hpi, hqi, hpq, hpφ, hqφ⟩ := hsplit
  have hfd : FiniteDimensional E V := D.chain.finiteDimensional
  have hDVR := subfieldIntegers_isDiscreteValuationRing F E
  have hfrac := subfieldIntegers_isFractionRing F E
  have hhens := henselianRing_subfieldIntegers (F := F) (E := E)
  have hmax : (Ring.jacobson (subfieldIntegers F E)).IsMaximal := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    infer_instance
  have hinj : Function.Injective (algebraMap (subfieldIntegers F E) E) := fun a b h => Subtype.ext h
  set Y := D.fundamentalElement π with hYdef
  have hY : Y ∈ D.chain.endFiltration 0 := fundamentalElement_mem_order D π hb
  have hlat : (D.chain.lattice 0).IsLattice E := D.chain.isLattice 0
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_integral_charpoly (D.chain.lattice 0) Y
    (fun v hv => by simpa using hY 0 v hv)
  have hred : D.fundamentalPolynomial π = Φ.map (Ideal.Quotient.mk (Ring.jacobson (subfieldIntegers F E))) := by
    unfold Stratum.fundamentalPolynomial
    rw [← hΦ]
    exact reduceIntegralPolynomial_map hinj Φ
  let : Field ((subfieldIntegers F E) ⧸ Ring.jacobson (subfieldIntegers F E)) := Ideal.Quotient.field _
  have hφm : (D.fundamentalPolynomial π).Monic := by
    rw [hred]
    exact hΦm.map _
  obtain ⟨g, h, hgm, hhm, hgh, hcop, hg0, hh0⟩ :=
    exists_coprime_split hφm hpm hqm hpi hqi hpq hpφ hqφ
  obtain ⟨f₁, f₂, hf₁m, hf₂m, hΦf, hdeg₁, hdeg₂, -, -, hcop'⟩ :=
    ValuationTheory.Henselian.exists_coprime_factor_lift Φ g h hΦm hgm hhm
      (by rw [← hred, hgh]) hcop
  obtain ⟨u, v, huv⟩ := hcop'
  set e₁ := aeval Y (v * f₂) with he₁
  set e₂ := aeval Y (u * f₁) with he₂
  have hsum : e₁ + e₂ = 1 := by
    rw [he₁, he₂, ← map_add, add_comm, huv, map_one]
  have hCH : aeval Y Φ = 0 := by
    rw [← aeval_map_algebraMap E, hΦ, LinearMap.aeval_self_charpoly]
  have h12 : e₁ * e₂ = 0 := by
    rw [he₁, he₂, ← map_mul, show v * f₂ * (u * f₁) = v * u * Φ by rw [hΦf]; ring, map_mul,
      hCH, mul_zero]
  have hmemO : ∀ r : (subfieldIntegers F E)[X], aeval Y r ∈ D.chain.endFiltration 0 := by
    intro r
    have h := Algebra.adjoin_le (S := D.chain.order) (Set.singleton_subset_iff.mpr hY)
      (aeval_mem_adjoin_singleton (subfieldIntegers F E) Y (p := r))
    exact h
  have hYb : Commute Y D.b := by
    rw [hYdef]
    unfold Stratum.fundamentalElement
    exact ((Commute.refl D.b).pow_left _).smul_left _
  have hcommb : ∀ r : (subfieldIntegers F E)[X], Commute (aeval Y r) D.b := by
    intro r
    have hYc : Y ∈ Subalgebra.centralizer (subfieldIntegers F E) ({D.b} : Set (Module.End E V)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hYb.eq.symm
    have h := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hYc)
      (aeval_mem_adjoin_singleton (subfieldIntegers F E) Y (p := r))
    rw [Subalgebra.mem_centralizer_iff] at h
    exact (h D.b (Set.mem_singleton _)).symm
  -- nontriviality
  have hnu : ∀ f : (subfieldIntegers F E)[X], f.Monic → 0 < f.natDegree → f ∣ Φ → ¬ IsUnit (aeval Y f) := by
    intro f hfm hf0 hfΦ hu
    apply not_isUnit_aeval_of_dvd_charpoly Y (h := f.map (algebraMap (subfieldIntegers F E) E))
    · rw [hfm.natDegree_map]
      exact hf0
    · rw [← hΦ]
      exact Polynomial.map_dvd _ hfΦ
    · rw [aeval_map_algebraMap]
      exact hu
  have hunit : ∀ a f : (subfieldIntegers F E)[X], aeval Y (a * f) = 1 → IsUnit (aeval Y f) := by
    intro a f haf
    have h1 : aeval Y f * aeval Y a = 1 := by rw [← map_mul, mul_comm, haf]
    have h2 : aeval Y a * aeval Y f = 1 := by rw [← map_mul, haf]
    exact ⟨⟨aeval Y f, aeval Y a, h1, h2⟩, rfl⟩
  have hne₁ : e₁ ≠ 0 := by
    intro h0
    have he₂1 : e₂ = 1 := by rw [← hsum, h0, zero_add]
    exact hnu f₁ hf₁m (by rw [hdeg₁]; exact hg0) ⟨f₂, hΦf⟩ (hunit u f₁ he₂1)
  have hne₂ : e₂ ≠ 0 := by
    intro h0
    have he₁1 : e₁ = 1 := by rw [← hsum, h0, add_zero]
    exact hnu f₂ hf₂m (by rw [hdeg₂]; exact hh0) ⟨f₁, by rw [hΦf, mul_comm]⟩
      (hunit v f₂ he₁1)
  refine ⟨e₁, e₂, hsum, h12, hne₁, hne₂, hmemO _, hmemO _, hcommb _, hcommb _, ?_⟩
  -- graded injectivity
  intro i x hx hx12 hbx
  have hexp := fundamental_exponents D
  have hYc : Y = (algebraMap (subfieldIntegers F E) E π.1) ^
      (D.n / (Nat.gcd D.chain.period D.n.natAbs : ℤ)) •
      D.b ^ (D.chain.period / Nat.gcd D.chain.period D.n.natAbs) := rfl
  have hpow : ∀ k : ℕ, D.b ^ k * x - x * D.b ^ k ∈ D.chain.endFiltration (i + 1 - D.n * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have heq : D.b ^ (k + 1) * x - x * D.b ^ (k + 1) =
          D.b * (D.b ^ k * x - x * D.b ^ k) + (D.b * x - x * D.b) * D.b ^ k := by
        rw [pow_succ']
        noncomm_ring
      rw [heq]
      apply add_mem
      · have h := D.chain.mul_mem_endFiltration hb ih
        convert h using 2
        push_cast
        ring
      · have h := D.chain.mul_mem_endFiltration hbx (pow_mem_endFiltration D.chain hb k)
        convert h using 2
        push_cast
        ring
  have hYx : Y * x - x * Y ∈ D.chain.endFiltration (i + 1) := by
    have h := prime_zpow_smul_mem_endFiltration D.chain π
      (D.n / (Nat.gcd D.chain.period D.n.natAbs : ℤ))
      (i + 1 - D.n * ((D.chain.period / Nat.gcd D.chain.period D.n.natAbs : ℕ) : ℤ)) (hpow _)
    rw [hYc, smul_mul_assoc, mul_smul_comm, ← smul_sub]
    convert h using 2
    linear_combination hexp
  -- polynomials in `Y` satisfy the same congruence
  let T : Subalgebra (subfieldIntegers F E) (Module.End E V) :=
    { carrier := {z | z ∈ D.chain.endFiltration 0 ∧
        z * x - x * z ∈ D.chain.endFiltration (i + 1)}
      mul_mem' := by
        rintro z w ⟨hz0, hz⟩ ⟨hw0, hw⟩
        refine ⟨by simpa using D.chain.mul_mem_endFiltration hz0 hw0, ?_⟩
        have heq : z * w * x - x * (z * w) = z * (w * x - x * w) + (z * x - x * z) * w := by
          noncomm_ring
        rw [heq]
        apply add_mem
        · simpa using D.chain.mul_mem_endFiltration hz0 hw
        · simpa using D.chain.mul_mem_endFiltration hz hw0
      add_mem' := by
        rintro z w ⟨hz0, hz⟩ ⟨hw0, hw⟩
        refine ⟨add_mem hz0 hw0, ?_⟩
        have heq : (z + w) * x - x * (z + w) = (z * x - x * z) + (w * x - x * w) := by
          noncomm_ring
        rw [heq]
        exact add_mem hz hw
      algebraMap_mem' := by
        intro a
        refine ⟨D.chain.order.algebraMap_mem a, ?_⟩
        rw [Algebra.commutes, sub_self]
        exact zero_mem _ }
  have hYT : Y ∈ T := ⟨hY, hYx⟩
  have he₂T : e₂ ∈ T :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hYT) (aeval_mem_adjoin_singleton (subfieldIntegers F E) Y)
  have h21 : e₂ * e₁ = 0 := mul_eq_zero_of_complement hsum h12
  have h22 : e₂ * e₂ = e₂ := idempotent_right_of_complement hsum h12
  have hx1 : e₂ * x = 0 := by rw [← hx12, ← mul_assoc, ← mul_assoc, h21, zero_mul, zero_mul]
  have hx2 : x * e₂ = x := by rw [← hx12, mul_assoc, h22]
  have h := he₂T.2
  rw [hx1, hx2, zero_sub] at h
  simpa using neg_mem h

end Langlands.BushnellKutzko.SplitObstruction
