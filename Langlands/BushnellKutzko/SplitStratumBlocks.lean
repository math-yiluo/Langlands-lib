import Langlands.BushnellKutzko.SplitObstructionIdempotents

/-! # Block data of a split fundamental stratum

Let `[𝔄, n, n−1, b]` be a split fundamental stratum over a Henselian discrete valuation ring
with `n > 0` and `gcd(n, e(𝔄)) = 1`. Hensel's lemma splits the integral characteristic
polynomial of `y_b = π^n b^e` into coprime monic factors, one of which reduces to a power of an
irreducible polynomial different from `X`. The corresponding idempotents `e₁, e₂` lie in `𝔄`
and commute with `b`; the commutator with `b` is injective on each graded step of both
off-diagonal blocks; and on the first block `b` is invertible, so that a product of powers of
`π` and `b` gives an element `ζ` of `𝔓` with an inverse `ζ'` on the first block lying
in `𝔓^{−1}`.
-/

noncomputable section

open Polynomial

namespace Langlands.BushnellKutzko.SplitBlocks

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

section Chain

variable (𝓛 : LatticeChain O K V) (π : RingPrimeElement O)

local notation "Q" => 𝓛.endFiltration

omit [IsScalarTower O K V] in
private theorem prime_mem_jacobson : π.1 ∈ Ring.jacobson O := by
  have h : π.1 ∈ Ideal.span ({π.1} : Set O) := Ideal.subset_span (Set.mem_singleton _)
  rwa [π.2.2] at h

theorem prime_smul_mem_lattice (i : ℤ) {v : V} (hv : v ∈ 𝓛.lattice i) :
    (algebraMap O K π.1) • v ∈ 𝓛.lattice (i + 𝓛.period) := by
  rw [𝓛.lattice_add_period, algebraMap_smul]
  exact Submodule.smul_mem_smul (prime_mem_jacobson π) hv

theorem prime_inv_smul_mem_lattice [IsDomain O] [FaithfulSMul O K]
    (i : ℤ) {v : V} (hv : v ∈ 𝓛.lattice (i + 𝓛.period)) :
    (algebraMap O K π.1)⁻¹ • v ∈ 𝓛.lattice i := by
  have hπ0 : algebraMap O K π.1 ≠ 0 := by
    intro h
    apply π.2.1
    have := (map_eq_zero_iff (algebraMap O K) (FaithfulSMul.algebraMap_injective O K)).mp h
    exact this
  have hJ : Ring.jacobson O = Ideal.span {π.1} := π.2.2.symm
  rw [𝓛.lattice_add_period, hJ, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [← algebraMap_smul K π.1 w, smul_smul, inv_mul_cancel₀ hπ0, one_smul]
  exact hw

theorem prime_zpow_smul_mem_lattice [IsDomain O] [FaithfulSMul O K]
    (k i : ℤ) {v : V} (hv : v ∈ 𝓛.lattice i) :
    (algebraMap O K π.1) ^ k • v ∈ 𝓛.lattice (i + k * 𝓛.period) := by
  have hπ0 : algebraMap O K π.1 ≠ 0 := by
    intro h
    exact π.2.1 ((map_eq_zero_iff (algebraMap O K) (FaithfulSMul.algebraMap_injective O K)).mp h)
  induction k using Int.induction_on with
  | zero => simpa using hv
  | succ k ih =>
    have hpow : (algebraMap O K π.1) ^ ((k : ℤ) + 1) =
        algebraMap O K π.1 * (algebraMap O K π.1) ^ (k : ℤ) := by
      rw [zpow_add_one₀ hπ0, mul_comm]
    rw [hpow, mul_smul]
    have h := prime_smul_mem_lattice 𝓛 π _ ih
    convert h using 2
    ring
  | pred k ih =>
    have hpow : (algebraMap O K π.1) ^ (-(k : ℤ) - 1) =
        (algebraMap O K π.1)⁻¹ * (algebraMap O K π.1) ^ (-(k : ℤ)) := by
      rw [zpow_sub_one₀ hπ0, mul_comm]
    rw [hpow, mul_smul]
    apply prime_inv_smul_mem_lattice 𝓛 π
    convert ih using 2
    ring

theorem prime_zpow_smul_mem_endFiltration [IsDomain O] [FaithfulSMul O K]
    (k m : ℤ) {x : Module.End K V} (hx : x ∈ Q m) :
    (algebraMap O K π.1) ^ k • x ∈ Q (m + k * 𝓛.period) := by
  intro i v hv
  rw [LinearMap.smul_apply]
  have h := prime_zpow_smul_mem_lattice 𝓛 π k (i + m) (hx i v hv)
  convert h using 2
  ring

theorem pow_mem_endFiltration {m : ℤ} {x : Module.End K V} (hx : x ∈ Q m) (k : ℕ) :
    x ^ k ∈ Q (k * m) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact 𝓛.mem_order_iff_mem_endFiltration.mp 𝓛.order.one_mem
  | succ k ih =>
    rw [pow_succ]
    have h := 𝓛.mul_mem_endFiltration ih hx
    convert h using 2
    push_cast
    ring

end Chain

/-! ### Arithmetic and polynomial lemmas -/

/-- For coprime `n` and `e > 0` there are `t ≥ 0` and `s` with `t n − s e = 1`. -/
theorem exists_shift_exponents {n e : ℕ} (he : 0 < e) (hcop : Nat.Coprime n e) :
    ∃ (t : ℕ) (s : ℤ), (t : ℤ) * n - s * e = 1 := by
  have h := Nat.gcd_eq_gcd_ab n e
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  refine ⟨(Nat.gcdA n e % e).toNat, -(Nat.gcdB n e + n * (Nat.gcdA n e / e)), ?_⟩
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ he'.ne')]
  have := Int.emod_add_ediv_mul (Nat.gcdA n e) e
  linear_combination (n : ℤ) * this - h

/-- An irreducible monic polynomial other than `X` has nonzero constant coefficient. -/
theorem coeff_zero_ne_zero_of_irreducible {k : Type*} [Field k] {p : k[X]} (hp : p.Monic)
    (hpi : Irreducible p) (hpX : p ≠ X) : p.coeff 0 ≠ 0 := by
  intro h0
  have hX : (X : k[X]) ∣ p := X_dvd_iff.mpr h0
  exact hpX (eq_of_monic_of_associated hp monic_X
    (irreducible_X.associated_of_dvd hpi hX).symm)

/-- A refinement of `SplitObstruction.exists_coprime_split`: the first factor is a power of the
given irreducible divisor, so its constant coefficient is nonzero when that divisor is not
`X`. -/
theorem exists_coprime_split_coeff {k : Type*} [Field k] {φ p q : k[X]} (hφ : φ.Monic)
    (hp : p.Monic) (hq : q.Monic) (hpi : Irreducible p) (hqi : Irreducible q) (hpq : p ≠ q)
    (hpφ : p ∣ φ) (hqφ : q ∣ φ) (hpX : p ≠ X) :
    ∃ g h : k[X], g.Monic ∧ h.Monic ∧ φ = g * h ∧ IsCoprime g h ∧
      0 < g.natDegree ∧ 0 < h.natDegree ∧ g.coeff 0 ≠ 0 := by
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
  refine ⟨p ^ m, c, hp.pow m, hcm, hc, (hpi.coprime_iff_not_dvd.mpr hnd).pow_left, ?_, ?_, ?_⟩
  · rw [hp.natDegree_pow]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hm) hpi.natDegree_pos
  · exact lt_of_lt_of_le hqi.natDegree_pos (natDegree_le_of_dvd hqc hcm.ne_zero)
  · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
    exact pow_ne_zero _ (coeff_zero_ne_zero_of_irreducible hp hpi hpX)

/-! ### The block data -/

/-- Block data of a stratum `[𝔄, n, r, b]`: complementary idempotents `e₁, e₂` of `𝔄`
commuting with `b`, graded injectivity of `x ↦ b x − x b` on both off-diagonal blocks, and an
element `ζ ∈ 𝔓` supported on the first block, commuting with `b`, with an inverse `ζ'` on the
first block lying in `𝔓^{−1}`. -/
structure SplitBlockData (D : Stratum O K V) where
  /-- The first idempotent. -/
  e₁ : Module.End K V
  /-- The second idempotent. -/
  e₂ : Module.End K V
  /-- The shift element on the first block. -/
  ζ : Module.End K V
  /-- The inverse of `ζ` on the first block. -/
  ζ' : Module.End K V
  add_eq : e₁ + e₂ = 1
  mul_eq : e₁ * e₂ = 0
  e₁_ne : e₁ ≠ 0
  e₂_ne : e₂ ≠ 0
  e₁_mem : e₁ ∈ D.chain.endFiltration 0
  e₂_mem : e₂ ∈ D.chain.endFiltration 0
  e₁_comm : Commute e₁ D.b
  e₂_comm : Commute e₂ D.b
  inj₁₂ : ∀ (i : ℤ) (x : Module.End K V), x ∈ D.chain.endFiltration i → e₁ * x * e₂ = x →
    D.b * x - x * D.b ∈ D.chain.endFiltration (i - D.n + 1) →
    x ∈ D.chain.endFiltration (i + 1)
  inj₂₁ : ∀ (i : ℤ) (x : Module.End K V), x ∈ D.chain.endFiltration i → e₂ * x * e₁ = x →
    D.b * x - x * D.b ∈ D.chain.endFiltration (i - D.n + 1) →
    x ∈ D.chain.endFiltration (i + 1)
  ζ_mem : ζ ∈ D.chain.endFiltration 1
  ζ'_mem : ζ' ∈ D.chain.endFiltration (-1)
  ζ_mul_ζ' : ζ * ζ' = e₁
  ζ'_mul_ζ : ζ' * ζ = e₁
  e₁_mul_ζ : e₁ * ζ = ζ
  ζ_mul_e₁ : ζ * e₁ = ζ
  e₁_mul_ζ' : e₁ * ζ' = ζ'
  ζ'_mul_e₁ : ζ' * e₁ = ζ'
  ζ_comm : Commute ζ D.b
  ζ'_comm : Commute ζ' D.b

variable [IsDomain O] [IsPrincipalIdealRing O] [IsLocalRing O] [IsFractionRing O K]
  [HenselianRing O (Ring.jacobson O)]

set_option maxHeartbeats 1600000 in
/-- A split fundamental stratum `[𝔄, n, n−1, b]` with `n > 0`, `gcd(n, e(𝔄)) = 1` and
`b ∈ 𝔓^{−n}` has block data. -/
theorem nonempty_splitBlockData (D : Stratum O K V) (hsplit : D.IsSplit)
    (hb : D.b ∈ D.chain.endFiltration (-D.n)) (hn : 0 < D.n)
    (hcop : Nat.Coprime D.n.natAbs D.chain.period) : Nonempty (SplitBlockData D) := by
  classical
  obtain ⟨-, π, p, q, hpm, hqm, hpi, hqi, hpq, hpφ, hqφ⟩ := hsplit
  -- choose the irreducible factor different from `X` first
  obtain ⟨p', q', hp'm, hq'm, hp'i, hq'i, hp'q', hp'φ, hq'φ, hp'X⟩ :
      ∃ p' q' : Polynomial (O ⧸ Ring.jacobson O), p'.Monic ∧ q'.Monic ∧ Irreducible p' ∧
        Irreducible q' ∧ p' ≠ q' ∧ p' ∣ D.fundamentalPolynomial π ∧
        q' ∣ D.fundamentalPolynomial π ∧ p' ≠ X := by
    by_cases hpX : p = X
    · exact ⟨q, p, hqm, hpm, hqi, hpi, hpq.symm, hqφ, hpφ, fun h => hpq (hpX.trans h.symm)⟩
    · exact ⟨p, q, hpm, hqm, hpi, hqi, hpq, hpφ, hqφ, hpX⟩
  have hfd : FiniteDimensional K V := D.chain.finiteDimensional
  have hmax : (Ring.jacobson O).IsMaximal := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    infer_instance
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).mpr hinj
  set e := D.chain.period with he
  set n := D.n with hndef
  have hgcd : Nat.gcd e n.natAbs = 1 := by rw [Nat.gcd_comm]; exact hcop
  set c : K := algebraMap O K π.1 with hc
  set Y := D.fundamentalElement π with hYdef
  have hYeq : Y = c ^ n • D.b ^ e := by
    rw [hYdef]
    unfold Stratum.fundamentalElement
    simp only [← he, ← hndef, hgcd, Nat.cast_one, Int.ediv_one, Nat.div_one, hc]
  have hY : Y ∈ D.chain.endFiltration 0 := by
    rw [hYeq]
    have h1 := pow_mem_endFiltration D.chain hb e
    have h2 := prime_zpow_smul_mem_endFiltration D.chain π n ((e : ℤ) * -n) h1
    convert h2 using 2
    ring
  have hlat : (D.chain.lattice 0).IsLattice K := D.chain.isLattice 0
  obtain ⟨Φ, hΦm, hΦ⟩ := SplitObstruction.exists_integral_charpoly (D.chain.lattice 0) Y
    (fun v hv => by simpa using hY 0 v hv)
  have hred : D.fundamentalPolynomial π = Φ.map (Ideal.Quotient.mk (Ring.jacobson O)) := by
    unfold Stratum.fundamentalPolynomial
    rw [← hYdef, ← hΦ]
    exact SplitObstruction.reduceIntegralPolynomial_map hinj Φ
  let : Field (O ⧸ Ring.jacobson O) := Ideal.Quotient.field _
  have hφm : (D.fundamentalPolynomial π).Monic := by
    rw [hred]
    exact hΦm.map _
  obtain ⟨g, h, hgm, hhm, hgh, hcop', hg0, hh0, hgc⟩ :=
    exists_coprime_split_coeff hφm hp'm hq'm hp'i hq'i hp'q' hp'φ hq'φ hp'X
  obtain ⟨f₁, f₂, hf₁m, hf₂m, hΦf, hdeg₁, hdeg₂, hf₁red, -, hcopf⟩ :=
    ValuationTheory.Henselian.exists_coprime_factor_lift Φ g h hΦm hgm hhm
      (by rw [← hred, hgh]) hcop'
  obtain ⟨u, v, huv⟩ := hcopf
  -- polynomials in `Y`
  have hmemO : ∀ r : O[X], aeval Y r ∈ D.chain.endFiltration 0 := by
    intro r
    exact Algebra.adjoin_le (S := D.chain.order) (Set.singleton_subset_iff.mpr hY)
      (aeval_mem_adjoin_singleton O Y (p := r))
  have hYb : Commute Y D.b := by
    rw [hYeq]
    exact ((Commute.refl D.b).pow_left _).smul_left _
  have hcb : ∀ r : O[X], Commute (aeval Y r) D.b := by
    intro r
    have hYc : Y ∈ Subalgebra.centralizer O ({D.b} : Set (Module.End K V)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hYb.eq.symm
    have h := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hYc)
      (aeval_mem_adjoin_singleton O Y (p := r))
    rw [Subalgebra.mem_centralizer_iff] at h
    exact (h D.b (Set.mem_singleton _)).symm
  have hcc : ∀ r r' : O[X], Commute (aeval Y r) (aeval Y r') := by
    intro r r'
    change aeval Y r * aeval Y r' = aeval Y r' * aeval Y r
    rw [← map_mul, ← map_mul, mul_comm]
  have hCH : aeval Y Φ = 0 := by
    rw [← aeval_map_algebraMap K, hΦ, LinearMap.aeval_self_charpoly]
  set P₁ : O[X] := v * f₂ with hP₁
  set P₂ : O[X] := u * f₁ with hP₂
  set e₁ := aeval Y P₁ with he₁
  set e₂ := aeval Y P₂ with he₂
  have hsum : e₁ + e₂ = 1 := by
    rw [he₁, he₂, ← map_add, add_comm, hP₁, hP₂, huv, map_one]
  have h12 : e₁ * e₂ = 0 := by
    rw [he₁, he₂, ← map_mul, show P₁ * P₂ = v * u * Φ by rw [hP₁, hP₂, hΦf]; ring, map_mul,
      hCH, mul_zero]
  have h21 : e₂ * e₁ = 0 := by rw [(hcc P₂ P₁).eq, h12]
  have h11 : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, h12, add_zero]
      _ = e₁ := by rw [hsum, mul_one]
  -- nontriviality
  have hnu : ∀ f : O[X], f.Monic → 0 < f.natDegree → f ∣ Φ → ¬ IsUnit (aeval Y f) := by
    intro f hfm hf0 hfΦ hu
    apply SplitObstruction.not_isUnit_aeval_of_dvd_charpoly Y (h := f.map (algebraMap O K))
    · rw [hfm.natDegree_map]
      exact hf0
    · rw [← hΦ]
      exact Polynomial.map_dvd _ hfΦ
    · rw [aeval_map_algebraMap]
      exact hu
  have hunit : ∀ a f : O[X], aeval Y (a * f) = 1 → IsUnit (aeval Y f) := by
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
  -- the constant coefficient of `f₁` is a unit
  have hc₀ : IsUnit (f₁.coeff 0) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.ringJacobson_eq_maximalIdeal]
    intro hmem
    apply hgc
    rw [← hf₁red, coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  obtain ⟨a₀, ha₀⟩ := hc₀
  -- the inverse of `Y` on the first block
  set Pw : O[X] := C (-(↑a₀⁻¹ : O)) * divX f₁ * P₁ with hPw
  set W := aeval Y Pw with hW
  have hYW : Y * W = e₁ := by
    have hpoly : X * Pw = C (-(↑a₀⁻¹ : O)) * v * Φ + P₁ := by
      have hX : X * divX f₁ = f₁ - C (f₁.coeff 0) := eq_sub_of_add_eq (X_mul_divX_add f₁)
      rw [hPw, hP₁, hΦf]
      have hinv : (↑a₀⁻¹ : O) * f₁.coeff 0 = 1 := by rw [← ha₀]; exact a₀.inv_mul
      calc X * (C (-(↑a₀⁻¹ : O)) * divX f₁ * (v * f₂))
          = C (-(↑a₀⁻¹ : O)) * (X * divX f₁) * (v * f₂) := by ring
        _ = C (-(↑a₀⁻¹ : O)) * (f₁ - C (f₁.coeff 0)) * (v * f₂) := by rw [hX]
        _ = C (-(↑a₀⁻¹ : O)) * v * (f₁ * f₂) + C ((↑a₀⁻¹ : O) * f₁.coeff 0) * (v * f₂) := by
          rw [C_mul, C_neg]; ring
        _ = C (-(↑a₀⁻¹ : O)) * v * (f₁ * f₂) + v * f₂ := by rw [hinv, C_1, one_mul]
    have := congrArg (aeval Y) hpoly
    rw [map_mul, aeval_X, map_add, map_mul (aeval Y) (C (-(↑a₀⁻¹ : O)) * v) Φ, hCH, mul_zero,
      zero_add] at this
    exact this
  have hW0 : W ∈ D.chain.endFiltration 0 := hmemO Pw
  have he₁W : e₁ * W = W := by
    rw [he₁, hW, ← map_mul, hPw]
    have : P₁ * (C (-(↑a₀⁻¹ : O)) * divX f₁ * P₁) = C (-(↑a₀⁻¹ : O)) * divX f₁ * (P₁ * P₁) := by
      ring
    rw [this, map_mul, map_mul (aeval Y) (C (-(↑a₀⁻¹ : O)) * divX f₁) P₁]
    congr 1
    rw [map_mul, ← he₁, h11]
  -- the inverse of `b` on the first block
  have hcb' : ∀ k : ℕ, Commute (D.b ^ k) e₁ := fun k => ((hcb P₁).pow_right k).symm
  set B₁ := D.b * e₁ with hB₁
  set B₁' := c ^ n • (D.b ^ (e - 1) * W) with hB₁'
  have he1 : 1 ≤ e := D.chain.period_pos
  have hbe : D.b * D.b ^ (e - 1) = D.b ^ e := by
    rw [← pow_succ', Nat.sub_add_cancel he1]
  have hB₁B₁' : B₁ * B₁' = e₁ := by
    rw [hB₁, hB₁', mul_smul_comm]
    calc c ^ n • (D.b * e₁ * (D.b ^ (e - 1) * W))
        = c ^ n • (D.b * D.b ^ (e - 1) * (e₁ * W)) := by
          congr 1
          rw [mul_assoc, ← mul_assoc e₁, (hcb' (e - 1)).eq.symm]
          noncomm_ring
      _ = Y * W := by rw [hbe, he₁W, hYeq, smul_mul_assoc]
      _ = e₁ := hYW
  have hWb : Commute W D.b := hcb Pw
  have hB₁'e₁ : Commute B₁' e₁ := by
    rw [hB₁']
    refine Commute.smul_left ?_ _
    exact ((hcb' (e - 1)).mul_left (hcc Pw P₁))
  have hB₁e₁ : Commute B₁ e₁ := by
    rw [hB₁]
    exact ((hcb P₁).symm).mul_left (Commute.refl e₁)
  have hB₁B₁'c : Commute B₁ B₁' := by
    rw [hB₁, hB₁']
    refine Commute.smul_right ?_ _
    refine Commute.mul_left ?_ ?_
    · exact ((Commute.refl D.b).pow_right _).mul_right hWb.symm
    · exact ((hcb' (e - 1)).symm).mul_right (hcc P₁ Pw)
  have hB₁'B₁ : B₁' * B₁ = e₁ := by rw [← hB₁B₁'c.eq, hB₁B₁']
  have hB₁mem : B₁ ∈ D.chain.endFiltration (-n) := by
    have := D.chain.mul_mem_endFiltration hb (hmemO P₁)
    simpa using this
  have hB₁'mem : B₁' ∈ D.chain.endFiltration n := by
    have h1 := pow_mem_endFiltration D.chain hb (e - 1)
    have h2 := D.chain.mul_mem_endFiltration h1 hW0
    have h3 := prime_zpow_smul_mem_endFiltration D.chain π n _ h2
    convert h3 using 2
    push_cast [Nat.cast_sub he1]
    ring
  -- exponents
  have hnpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn.ne'
  obtain ⟨t, s, hts⟩ := exists_shift_exponents D.chain.period_pos hcop
  have hnabs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn.le
  rw [hnabs] at hts
  set ζ := c ^ (-s) • (B₁' ^ t * e₁) with hζ
  set ζ' := c ^ s • (B₁ ^ t * e₁) with hζ'
  have hc0 : c ≠ 0 := by
    intro h0
    exact π.2.1 ((map_eq_zero_iff (algebraMap O K) hinj).mp h0)
  have hpowB : B₁' ^ t * e₁ * (B₁ ^ t * e₁) = e₁ := by
    have h1 : B₁' ^ t * e₁ * (B₁ ^ t * e₁) = (B₁' * B₁) ^ t * (e₁ * e₁) := by
      rw [hB₁B₁'c.symm.mul_pow]
      have hc1 : Commute e₁ (B₁ ^ t) := (hB₁e₁.symm).pow_right t
      calc B₁' ^ t * e₁ * (B₁ ^ t * e₁) = B₁' ^ t * (e₁ * B₁ ^ t) * e₁ := by noncomm_ring
        _ = B₁' ^ t * (B₁ ^ t * e₁) * e₁ := by rw [hc1.eq]
        _ = B₁' ^ t * B₁ ^ t * (e₁ * e₁) := by noncomm_ring
    have hpe : ∀ k : ℕ, e₁ ^ k * e₁ = e₁ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_assoc, h11, ih]
    rw [h1, hB₁'B₁, h11, hpe]
  have hpowB' : B₁ ^ t * e₁ * (B₁' ^ t * e₁) = e₁ := by
    have h1 : B₁ ^ t * e₁ * (B₁' ^ t * e₁) = B₁' ^ t * e₁ * (B₁ ^ t * e₁) := by
      have hc1 : Commute e₁ (B₁ ^ t) := (hB₁e₁.symm).pow_right t
      have hc2 : Commute e₁ (B₁' ^ t) := (hB₁'e₁.symm).pow_right t
      have hc3 : Commute (B₁ ^ t) (B₁' ^ t) := (hB₁B₁'c.pow_left t).pow_right t
      calc B₁ ^ t * e₁ * (B₁' ^ t * e₁) = B₁ ^ t * (e₁ * B₁' ^ t) * e₁ := by noncomm_ring
        _ = B₁ ^ t * (B₁' ^ t * e₁) * e₁ := by rw [hc2.eq]
        _ = B₁' ^ t * (B₁ ^ t * e₁) * e₁ := by
          rw [← mul_assoc (B₁ ^ t), hc3.eq, mul_assoc (B₁' ^ t)]
        _ = B₁' ^ t * (e₁ * B₁ ^ t) * e₁ := by rw [hc1.eq]
        _ = B₁' ^ t * e₁ * (B₁ ^ t * e₁) := by noncomm_ring
    rw [h1, hpowB]
  have hζζ' : ζ * ζ' = e₁ := by
    rw [hζ, hζ', smul_mul_smul_comm, ← zpow_add₀ hc0, neg_add_cancel, zpow_zero, one_smul,
      hpowB]
  have hζ'ζ : ζ' * ζ = e₁ := by
    rw [hζ, hζ', smul_mul_smul_comm, ← zpow_add₀ hc0, add_neg_cancel, zpow_zero, one_smul,
      hpowB']
  have hζmem : ζ ∈ D.chain.endFiltration 1 := by
    have h1 := pow_mem_endFiltration D.chain hB₁'mem t
    have h2 := D.chain.mul_mem_endFiltration h1 (hmemO P₁)
    have h3 := prime_zpow_smul_mem_endFiltration D.chain π (-s) _ h2
    convert h3 using 2
    linear_combination -hts
  have hζ'mem : ζ' ∈ D.chain.endFiltration (-1) := by
    have h1 := pow_mem_endFiltration D.chain hB₁mem t
    have h2 := D.chain.mul_mem_endFiltration h1 (hmemO P₁)
    have h3 := prime_zpow_smul_mem_endFiltration D.chain π s _ h2
    convert h3 using 2
    linear_combination hts
  have he₁ζ : e₁ * ζ = ζ := by
    rw [hζ, mul_smul_comm, ← mul_assoc, ((hB₁'e₁.symm).pow_right t).eq, mul_assoc, h11]
  have hζe₁ : ζ * e₁ = ζ := by rw [hζ, smul_mul_assoc, mul_assoc, h11]
  have he₁ζ' : e₁ * ζ' = ζ' := by
    rw [hζ', mul_smul_comm, ← mul_assoc, ((hB₁e₁.symm).pow_right t).eq, mul_assoc, h11]
  have hζ'e₁ : ζ' * e₁ = ζ' := by rw [hζ', smul_mul_assoc, mul_assoc, h11]
  have hB₁b : Commute B₁ D.b := ((Commute.refl D.b).mul_left (hcb P₁))
  have hB₁'b : Commute B₁' D.b :=
    (((Commute.refl D.b).pow_left _).mul_left hWb).smul_left _
  have hζb : Commute ζ D.b := ((hB₁'b.pow_left t).mul_left (hcb P₁)).smul_left _
  have hζ'b : Commute ζ' D.b := ((hB₁b.pow_left t).mul_left (hcb P₁)).smul_left _
  -- graded injectivity on both blocks
  have hgrad : ∀ (i : ℤ) (x : Module.End K V), x ∈ D.chain.endFiltration i →
      D.b * x - x * D.b ∈ D.chain.endFiltration (i - n + 1) →
      e₂ * x - x * e₂ ∈ D.chain.endFiltration (i + 1) := by
    intro i x hx hbx
    have hpow : ∀ k : ℕ, D.b ^ k * x - x * D.b ^ k ∈ D.chain.endFiltration (i + 1 - n * k) := by
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
      have h := prime_zpow_smul_mem_endFiltration D.chain π n (i + 1 - n * (e : ℤ)) (hpow e)
      rw [hYeq, smul_mul_assoc, mul_smul_comm, ← smul_sub]
      convert h using 2
      ring
    let T : Subalgebra O (Module.End K V) :=
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
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hYT) (aeval_mem_adjoin_singleton O Y)
    exact he₂T.2
  have h22 : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, h12, zero_add]
      _ = e₂ := by rw [hsum, one_mul]
  refine ⟨{
    e₁ := e₁, e₂ := e₂, ζ := ζ, ζ' := ζ', add_eq := hsum, mul_eq := h12,
    e₁_ne := hne₁, e₂_ne := hne₂, e₁_mem := hmemO _, e₂_mem := hmemO _,
    e₁_comm := hcb _, e₂_comm := hcb _, inj₁₂ := ?_, inj₂₁ := ?_, ζ_mem := hζmem,
    ζ'_mem := hζ'mem, ζ_mul_ζ' := hζζ', ζ'_mul_ζ := hζ'ζ, e₁_mul_ζ := he₁ζ,
    ζ_mul_e₁ := hζe₁, e₁_mul_ζ' := he₁ζ', ζ'_mul_e₁ := hζ'e₁, ζ_comm := hζb,
    ζ'_comm := hζ'b }⟩
  · intro i x hx hx12 hbx
    have h := hgrad i x hx hbx
    have hx1 : e₂ * x = 0 := by rw [← hx12, ← mul_assoc, ← mul_assoc, h21, zero_mul, zero_mul]
    have hx2 : x * e₂ = x := by rw [← hx12, mul_assoc, h22]
    rw [hx1, hx2, zero_sub] at h
    simpa using neg_mem h
  · intro i x hx hx21 hbx
    have h := hgrad i x hx hbx
    have hx1 : e₂ * x = x := by rw [← hx21, ← mul_assoc, ← mul_assoc, h22]
    have hx2 : x * e₂ = 0 := by rw [← hx21, mul_assoc, h12, mul_zero]
    rw [hx1, hx2, sub_zero] at h
    exact h

end Langlands.BushnellKutzko.SplitBlocks
