import Langlands.BushnellKutzko.PureStratumApproximationSeed
import Langlands.BushnellKutzko.CriticalDerivedSimpleLift
import Langlands.BushnellKutzko.FundamentalStratumPowerCondition
import Langlands.BushnellKutzko.NonsplitRefinementChain

/-! # A nonsplit fundamental stratum lies in a simple stratum (BK93 (2.3.4))

`Langlands.BushnellKutzko.PureApproximation.nonsplitRefinement` proves
`NonsplitRefinementPremise`. The namespace `NonsplitRefinement` collects the lemmas on integral
polynomials in elements of `𝔄(𝓛)`, shifting units and shift parameters used in the proof.
-/

noncomputable section

open ValuativeRel Polynomial IsLocalRing

namespace Langlands.BushnellKutzko.NonsplitRefinement

open CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

/-! ### Scalars and polynomials on the filtration -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Scalars in `𝔬_F` preserve `𝔓^j(𝓛)`. -/
theorem integer_smul_mem {x : Module.End F V} {j : ℤ} (c : 𝒪[F]) (hx : x ∈ 𝓛.endFiltration j) :
    (algebraMap 𝒪[F] F c) • x ∈ 𝓛.endFiltration j := by
  intro i v hv
  change (algebraMap 𝒪[F] F c) • x v ∈ 𝓛.lattice (i + j)
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ c (hx i v hv)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Scalars in `𝔭_F` map `𝔓^j(𝓛)` into `𝔓^{j+1}(𝓛)`. -/
theorem jacobson_smul_mem {x : Module.End F V} {j : ℤ} {c : 𝒪[F]} (hc : c ∈ Ring.jacobson 𝒪[F])
    (hx : x ∈ 𝓛.endFiltration j) : (algebraMap 𝒪[F] F c) • x ∈ 𝓛.endFiltration (j + 1) := by
  intro i v hv
  change (algebraMap 𝒪[F] F c) • x v ∈ 𝓛.lattice (i + (j + 1))
  rw [algebraMap_smul]
  have h := Submodule.smul_mem_smul hc (hx i v hv)
  rw [← 𝓛.lattice_add_period] at h
  exact 𝓛.antitone (by have := 𝓛.period_pos; omega) h

/-- `ϖ^t 𝔓^j(𝓛) ⊆ 𝔓^{j + e t}(𝓛)`. -/
theorem zpow_smul_mem {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : Module.End F V} {j : ℤ} (t : ℤ)
    (hx : x ∈ 𝓛.endFiltration j) :
    ((ϖ : F) ^ t) • x ∈ 𝓛.endFiltration (j + 𝓛.period * t) := by
  intro i v hv
  change ((ϖ : F) ^ t) • x v ∈ 𝓛.lattice (i + (j + 𝓛.period * t))
  rw [𝓛.zpow_smul_mem_iff hϖ, show i + (j + 𝓛.period * t) - 𝓛.period * t = i + j by ring]
  exact hx i v hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `x ∈ 𝔓^j(𝓛)` implies `x^k ∈ 𝔓^{kj}(𝓛)`. -/
theorem pow_mem_endFiltration {x : Module.End F V} {j : ℤ} (hx : x ∈ 𝓛.endFiltration j) (k : ℕ) :
    x ^ k ∈ 𝓛.endFiltration (k * j) := by
  induction k with
  | zero =>
    simpa using (𝓛.mem_order_iff_mem_endFiltration).mp (one_mem 𝓛.order)
  | succ k ih =>
    have h := 𝓛.mul_mem_endFiltration ih hx
    rwa [← pow_succ, show (k : ℤ) * j + j = ((k + 1 : ℕ) : ℤ) * j by push_cast; ring] at h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An integral polynomial in an element of `𝔄(𝓛)` lies in `𝔄(𝓛)`. -/
theorem aeval_map_mem_order {y : Module.End F V} (hy : y ∈ 𝓛.endFiltration 0) (R : (𝒪[F])[X]) :
    aeval y (R.map (algebraMap 𝒪[F] F)) ∈ 𝓛.endFiltration 0 := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [coeff_map]
  exact integer_smul_mem 𝓛 _ (by simpa using pow_mem_endFiltration 𝓛 hy i)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An integral polynomial with coefficients in `𝔭_F`, evaluated at an element of `𝔄(𝓛)`, lies
in `𝔓(𝓛)`. -/
theorem aeval_map_mem_one {y : Module.End F V} (hy : y ∈ 𝓛.endFiltration 0) (R : (𝒪[F])[X])
    (hR : ∀ i, R.coeff i ∈ Ring.jacobson 𝒪[F]) :
    aeval y (R.map (algebraMap 𝒪[F] F)) ∈ 𝓛.endFiltration 1 := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [coeff_map]
  have h := jacobson_smul_mem 𝓛 (hR i) (j := 0) (by simpa using pow_mem_endFiltration 𝓛 hy i)
  rwa [zero_add] at h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An element commuting with `y` commutes with every polynomial in `y`. -/
theorem commute_aeval {A : Type*} [Ring A] [Algebra F A] {x y : A} (h : Commute x y) (Q : F[X]) :
    Commute x (aeval y Q) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

/-! ### The characteristic polynomial of an element of the order -/

/-- An element of `𝔄(𝓛)` has an integral characteristic polynomial. -/
theorem exists_charpoly_eq_map [FiniteDimensional F V] {y : Module.End F V}
    (hy : y ∈ 𝓛.endFiltration 0) :
    ∃ Φ : (𝒪[F])[X], y.charpoly = Φ.map (algebraMap 𝒪[F] F) := by
  classical
  have := 𝓛.isLattice 0
  let b₀ := Module.finBasis 𝒪[F] (𝓛.lattice 0)
  let B := b₀.extendOfIsLattice F
  have hB (k : Fin (Module.finrank 𝒪[F] (𝓛.lattice 0))) : B k = (b₀ k : V) :=
    Module.Basis.extendOfIsLattice_apply F b₀ k
  have hrepr (w : 𝓛.lattice 0) (i : Fin (Module.finrank 𝒪[F] (𝓛.lattice 0))) :
      B.repr (w : V) i = algebraMap 𝒪[F] F (b₀.repr w i) := by
    conv_lhs => rw [← b₀.sum_repr w]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, Finset.sum_apply']
    rw [Finset.sum_eq_single i]
    · rw [← algebraMap_smul F, ← hB, map_smul, B.repr_self]
      simp [Algebra.algebraMap_eq_smul_one]
    · intro k _ hk
      rw [← algebraMap_smul F, ← hB, map_smul, B.repr_self]
      simp [hk]
    · simp
  have hmaps (v : V) (hv : v ∈ 𝓛.lattice 0) : y v ∈ 𝓛.lattice 0 := by
    simpa using hy 0 v hv
  let M₀ : Matrix (Fin (Module.finrank 𝒪[F] (𝓛.lattice 0)))
      (Fin (Module.finrank 𝒪[F] (𝓛.lattice 0))) 𝒪[F] :=
    Matrix.of fun i j => b₀.repr ⟨y (b₀ j), hmaps _ (b₀ j).2⟩ i
  refine ⟨M₀.charpoly, ?_⟩
  rw [← LinearMap.charpoly_toMatrix y B, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hB, Matrix.map_apply]
  exact hrepr ⟨y (b₀ j), hmaps _ (b₀ j).2⟩ i

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The reduction of an integral polynomial is the coefficientwise reduction of its integral
form. -/
theorem reduceIntegralPolynomial_map (Φ : (𝒪[F])[X]) :
    reduceIntegralPolynomial 𝒪[F] F (Φ.map (algebraMap 𝒪[F] F)) =
      Φ.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])) := by
  classical
  have hinj : Function.Injective (algebraMap 𝒪[F] F) := Subtype.val_injective
  ext n
  rw [reduceIntegralPolynomial, finsetSum_coeff, coeff_map]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hn h
  · congr 1
    exact hinj ((Classical.choose_spec h).trans (coeff_map _ _))
  · exact absurd ⟨Φ.coeff n, (coeff_map _ _).symm⟩ h
  · rw [mem_support_iff, not_not, coeff_map] at hn
    rw [(map_eq_zero_iff _ hinj).mp hn, map_zero]

/-- If the reduced characteristic polynomial of `y ∈ 𝔄(𝓛)` is `p^m` and `P` lifts `p`, then
`P(y)^m ∈ 𝔓(𝓛)`. -/
theorem aeval_pow_mem_one [FiniteDimensional F V] {y : Module.End F V}
    (hy : y ∈ 𝓛.endFiltration 0) {p : (𝒪[F] ⧸ Ring.jacobson 𝒪[F])[X]} {m : ℕ}
    (hφ : reduceIntegralPolynomial 𝒪[F] F y.charpoly = p ^ m) {P : (𝒪[F])[X]}
    (hP : P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])) = p) :
    aeval y (P.map (algebraMap 𝒪[F] F)) ^ m ∈ 𝓛.endFiltration 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_charpoly_eq_map 𝓛 hy
  rw [hΦ, reduceIntegralPolynomial_map] at hφ
  have hD : ∀ i, (P ^ m - Φ).coeff i ∈ Ring.jacobson 𝒪[F] := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, Polynomial.map_sub, Polynomial.map_pow, hP,
      hφ, sub_self, coeff_zero]
  have h0 : aeval y (Φ.map (algebraMap 𝒪[F] F)) = 0 := by
    rw [← hΦ]
    exact LinearMap.aeval_self_charpoly y
  have h := aeval_map_mem_one 𝓛 hy _ hD
  rwa [Polynomial.map_sub, map_sub, h0, sub_zero, Polynomial.map_pow, map_pow] at h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `y ∈ 𝔄(𝓛)` and `P(y)^m ∈ 𝔓(𝓛)` for an integral polynomial `P` with unit constant term,
then `y` is a unit of `𝔄(𝓛)`. -/
theorem exists_unit_of_aeval_pow_mem [FiniteDimensional F V] {y : Module.End F V}
    (hy : y ∈ 𝓛.endFiltration 0) {P : (𝒪[F])[X]} (hP₀ : IsUnit (P.coeff 0)) {m : ℕ}
    (hPm : aeval y (P.map (algebraMap 𝒪[F] F)) ^ m ∈ 𝓛.endFiltration 1) :
    ∃ u : (Module.End F V)ˣ, (u : Module.End F V) = y ∧ Shifts 𝓛 0 u := by
  set R := P ^ m with hRdef
  have hR0 : IsUnit (R.coeff 0) := by
    rw [hRdef, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
    exact hP₀.pow m
  obtain ⟨c, hc⟩ := hR0
  set w := aeval y (R.map (algebraMap 𝒪[F] F)) with hwdef
  have hw : w ∈ 𝓛.endFiltration 1 := by
    rwa [hwdef, hRdef, Polynomial.map_pow, map_pow]
  set a := aeval y (R.divX.map (algebraMap 𝒪[F] F)) with hadef
  have ha : a ∈ 𝓛.endFiltration 0 := aeval_map_mem_order 𝓛 hy _
  have hdecomp : w = algebraMap F (Module.End F V) (algebraMap 𝒪[F] F (R.coeff 0)) + y * a := by
    rw [hwdef]
    conv_lhs => rw [← X_mul_divX_add R]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_X, Polynomial.map_C, map_add, map_mul,
      aeval_X, aeval_C, hadef]
    abel
  set ci : F := algebraMap 𝒪[F] F ((c⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) with hcidef
  have hci : ci * algebraMap 𝒪[F] F (R.coeff 0) = 1 := by
    rw [hcidef, ← map_mul, ← hc, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hx : -(ci • w) ∈ 𝓛.endFiltration ((1 : ℕ) : ℤ) :=
    neg_mem (by simpa [hcidef] using integer_smul_mem 𝓛 ((c⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) hw)
  obtain ⟨g, hg, hg1⟩ := 𝓛.exists_mem_unitFiltration le_rfl hx
  have hyg : y * (-(ci • a)) = (g : Module.End F V) := by
    rw [hg1, hdecomp, smul_add, Algebra.smul_def ci (algebraMap F _ _), ← map_mul, hci, map_one,
      mul_neg, mul_smul_comm, neg_add, add_neg_cancel_left]
  set z := (-(ci • a)) * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) with hzdef
  have h1 : y * z = 1 := by
    rw [hzdef, ← mul_assoc, hyg, Units.mul_inv]
  have h2 : z * y = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨y, z, h1, h2⟩, rfl, hy, ?_⟩
  change z ∈ 𝓛.endFiltration (-0)
  rw [neg_zero]
  have hz1 : -(ci • a) ∈ 𝓛.endFiltration 0 :=
    neg_mem (by simpa [hcidef] using integer_smul_mem 𝓛 ((c⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) ha)
  have hz := 𝓛.mul_mem_endFiltration hz1 ((𝓛.mem_order_iff_mem_endFiltration).mp hg.2.1)
  rwa [add_zero] at hz

/-! ### Shifting units and shift parameters -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Integer powers of a scalar endomorphism unit. -/
theorem coe_scalarEndUnit_zpow (u : Fˣ) (t : ℤ) :
    (↑((scalarEndUnit (V := V) u) ^ t) : Module.End F V) = algebraMap F _ ((u : F) ^ t) := by
  rw [← map_zpow (Units.map (algebraMap F (Module.End F V)).toMonoidHom), Units.coe_map,
    Units.val_zpow_eq_zpow_val]
  rfl

/-- An element of valuation at least `k` lies in `𝔓^k`. -/
theorem mem_of_le_valuation {x : Module.End F V} {k : ℤ}
    (h : (k : WithTop ℤ) ≤ 𝓛.valuation x) : x ∈ 𝓛.endFiltration k := by
  by_cases h0 : x = 0
  · rw [h0]
    exact zero_mem _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨s, hs, hs'⟩ := exists_depth 𝓛 hϖ h0
  rw [𝓛.valuation_eq_of_mem_of_notMem hs hs'] at h
  exact 𝓛.endFiltration_antitone (WithTop.coe_le_coe.mp h) hs

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `g ∈ 𝔓^d` and `g^h` shifts the chain by `h d` for some `h ≥ 1`, then `g` shifts it by
`d`. -/
theorem shifts_of_pow {g : (Module.End F V)ˣ} {d : ℤ} {h : ℕ} (hh : 0 < h)
    (hg : (g : Module.End F V) ∈ 𝓛.endFiltration d) (hgh : Shifts 𝓛 (h * d) (g ^ h)) :
    Shifts 𝓛 d g := by
  refine ⟨hg, ?_⟩
  have heq : g⁻¹ = g ^ (h - 1) * (g ^ h)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    conv_lhs => rw [show h = 1 + (h - 1) by omega]
    rw [pow_add, pow_one, inv_mul_cancel_left]
  have h1 : ((g ^ (h - 1) : (Module.End F V)ˣ) : Module.End F V) ∈
      𝓛.endFiltration (((h - 1 : ℕ) : ℤ) * d) := by
    rw [Units.val_pow_eq_pow_val]
    exact pow_mem_endFiltration 𝓛 hg _
  have h2 := 𝓛.mul_mem_endFiltration h1 hgh.2
  rw [heq, Units.val_mul]
  convert h2 using 2
  push_cast [Nat.cast_sub hh]
  ring

/-- Shift parameters whose common divisor is the greatest common divisor used in
`Stratum.fundamentalElement`. -/
theorem exists_shiftParameters_eq_gcd {e : ℕ} (he : 0 < e) (n : ℤ) :
    ∃ N : ShiftParameters e (-n), N.g = Nat.gcd e n.natAbs := by
  obtain ⟨N⟩ := exists_shiftParameters he (-n)
  refine ⟨N, ?_⟩
  have hcop : IsCoprime N.k (N.h : ℤ) := ⟨N.u, N.v, N.bezout⟩
  have h1 : Int.gcd N.k N.h = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hn : n.natAbs = N.g * N.k.natAbs := by
    have h := congrArg Int.natAbs N.depth_eq
    rwa [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast] at h
  have h2 : Nat.gcd N.k.natAbs N.h = 1 := by simpa [Int.gcd] using h1
  have key : ∀ e' : ℕ, e' = N.h * N.g → Nat.gcd e' n.natAbs = N.g := by
    rintro e' rfl
    rw [hn, mul_comm N.h N.g, Nat.gcd_mul_left, Nat.gcd_comm, h2, mul_one]
  exact (key e N.period_eq).symm

end Langlands.BushnellKutzko.NonsplitRefinement

namespace Langlands.BushnellKutzko.PureApproximation

open NonsplitRefinement CriticalDerived

universe uF uV

/-- **BK93 (2.3.4).** A nonsplit fundamental stratum `[𝓛, n, n-1, b]` is contained in a simple
stratum `[𝓜, n', n'-1, c]` on a chain `𝓜` containing every lattice of `𝓛`, with
`n / e(𝓛) = n' / e(𝓜)`. -/
theorem nonsplitRefinement : NonsplitRefinementPremise.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S hS
  obtain ⟨⟨hr, hnil⟩, π, p, m, hpmon, hpirr, -, hφ⟩ := hS
  have hϖ : Irreducible π.1 :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      (by rw [← jacobson_integer_eq_maximalIdeal F, π.2.2])
  set ϖ : 𝒪[F] := π.1 with hϖdef
  set ϖu := LatticeChain.uniformizerAsUnit hϖ with hϖudef
  set πE : (Module.End F V)ˣ := scalarEndUnit ϖu with hπEdef
  set 𝓛 := S.chain with h𝓛def
  obtain ⟨N, hNg⟩ := exists_shiftParameters_eq_gcd 𝓛.period_pos S.n
  have hhk : (N.h : ℤ) * (-S.n) + -N.k * (𝓛.period : ℤ) = 0 := N.residual_degree
  have hdepth : -S.n = (N.g : ℤ) * N.k := N.depth_eq
  have hper : 𝓛.period = N.h * N.g := N.period_eq
  -- the element `y = ϖ^{n/g} b^{e/g}`
  set y := S.fundamentalElement π with hydef
  have hy_eq : y = ((ϖ : F) ^ (-N.k)) • S.b ^ N.h := by
    have h1 : S.n / ((Nat.gcd S.chain.period S.n.natAbs : ℕ) : ℤ) = -N.k := by
      rw [← hNg]
      exact Int.ediv_eq_of_eq_mul_left (by exact_mod_cast N.g_pos.ne') (by linarith)
    have h2 : S.chain.period / Nat.gcd S.chain.period S.n.natAbs = N.h := by
      rw [← hNg]
      exact Nat.div_eq_of_eq_mul_left N.g_pos hper
    simp only [hydef, Stratum.fundamentalElement, h1, h2]
    rfl
  have hb : S.b ∈ 𝓛.endFiltration (-S.n) :=
    mem_of_le_valuation 𝓛 (by exact_mod_cast S.valuation_ge)
  have hbh : S.b ^ N.h ∈ 𝓛.endFiltration ((N.h : ℤ) * (-S.n)) := pow_mem_endFiltration 𝓛 hb _
  have hy0 : y ∈ 𝓛.endFiltration 0 := by
    rw [hy_eq]
    have h := zpow_smul_mem 𝓛 hϖ (-N.k) hbh
    rwa [show (N.h : ℤ) * (-S.n) + 𝓛.period * -N.k = 0 by linarith] at h
  have hφ' : reduceIntegralPolynomial 𝒪[F] F y.charpoly = p ^ m := hφ
  -- the residual polynomial is not `X`
  have hpX : p ≠ X := by
    rintro rfl
    have hXm := aeval_pow_mem_one 𝓛 hy0 hφ' (P := X) (by simp)
    simp only [Polynomial.map_X, aeval_X] at hXm
    have hbpow : S.b ^ (N.h * m) ∈ 𝓛.endFiltration (((N.h * m : ℕ) : ℤ) * (-S.n) + 1) := by
      have h1 : S.b ^ (N.h * m) = ((ϖ : F) ^ (N.k * m)) • y ^ m := by
        rw [hy_eq, _root_.smul_pow, smul_smul, ← zpow_natCast ((ϖ : F) ^ (-N.k)), ← zpow_mul,
          ← zpow_add₀ (coe_uniformizer_ne_zero hϖ),
          show N.k * (m : ℤ) + -N.k * (m : ℤ) = 0 by ring, zpow_zero, one_smul, ← pow_mul]
      rw [h1]
      have h2 := zpow_smul_mem 𝓛 hϖ (N.k * m) hXm
      convert h2 using 2
      push_cast
      linear_combination (m : ℤ) * hhk
    obtain ⟨y', hy', hnil'⟩ := 𝓛.exists_isNilpotent_add_of_pow_mem_endFiltration hb hbpow
    refine hnil (S.b + y') ?_ hnil'
    change S.b + y' - S.b ∈ S.chain.endFiltration (-S.r)
    rw [add_sub_cancel_left, hr, show -(S.n - 1) = -S.n + 1 by ring]
    exact hy'
  -- a monic lift of `p` with unit constant coefficient
  have : Nontrivial (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := by
    rw [jacobson_integer_eq_maximalIdeal F]
    infer_instance
  obtain ⟨P, hPmap, -, hPmon⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_set_range p).mpr (map_surjective _ Ideal.Quotient.mk_surjective p)) hpmon
  have hp0 : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr h0
    rcases hpirr.isUnit_or_isUnit hq with hX | hqu
    · exact not_isUnit_X hX
    · have hqm : q.Monic := Monic.of_mul_monic_left monic_X (hq ▸ hpmon)
      exact hpX (by rw [hq, hqm.isUnit_iff.mp hqu, mul_one])
  have hP₀ : IsUnit (P.coeff 0) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← jacobson_integer_eq_maximalIdeal F]
    intro hmem
    apply hp0
    rw [← hPmap, coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hPm := aeval_pow_mem_one 𝓛 hy0 hφ' hPmap
  -- `y` and `b` are units
  obtain ⟨yu, hyu, hyuS⟩ := exists_unit_of_aeval_pow_mem 𝓛 hy0 hP₀ hPm
  have hbh_eq : S.b ^ N.h = ((πE ^ N.k * yu : (Module.End F V)ˣ) : Module.End F V) := by
    rw [Units.val_mul, hyu, hy_eq, hπEdef, coe_scalarEndUnit_zpow, hϖudef,
      LatticeChain.coe_uniformizerAsUnit, ← Algebra.smul_def, smul_smul,
      ← zpow_add₀ (coe_uniformizer_ne_zero hϖ), add_neg_cancel, zpow_zero, one_smul]
  have hbunit : IsUnit S.b :=
    (isUnit_pow_iff N.h_pos.ne').mp (hbh_eq ▸ Units.isUnit _)
  set bu := hbunit.unit with hbudef
  have hbu : (bu : Module.End F V) = S.b := hbunit.unit_spec
  have hπ : Shifts 𝓛 𝓛.period πE := uniformizerUnit_shifts hϖ 𝓛
  have hbuh : bu ^ N.h = πE ^ N.k * yu := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hbu, hbh_eq]
  have hbuS : Shifts 𝓛 (-S.n) bu := by
    apply shifts_of_pow 𝓛 N.h_pos (by rw [hbu]; exact hb)
    rw [hbuh]
    have h := (hπ.zpow N.k).mul hyuS
    convert h using 1
    linarith
  have hcomm : Commute πE yu := by
    rw [hπEdef]
    exact scalarEndUnit_commutes ϖu yu
  have hres : N.residual bu πE = yu := by
    rw [ShiftParameters.residual, zpow_natCast, hbuh, mul_assoc, (hcomm.zpow_left (-N.k)).symm.eq,
      ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  -- the refined chain
  set z := aeval y (P.map (algebraMap 𝒪[F] F)) with hzdef
  have hz0 : z ∈ 𝓛.endFiltration 0 := aeval_map_mem_order 𝓛 hy0 P
  have hby : Commute S.b y := by
    rw [hy_eq]
    exact ((Commute.refl S.b).pow_right N.h).smul_right _
  have hbz : Commute (bu : Module.End F V) z := by
    rw [hbu]
    exact commute_aeval hby _
  have hyz : Commute (yu : Module.End F V) z := by
    rw [hyu]
    exact commute_aeval (Commute.refl y) _
  obtain ⟨𝓜, ℓ', hb𝓜, hlat, hfilt, hz𝓜, hunit⟩ := exists_refinement hϖ hz0 hPm hbuS hbz
  have hy𝓜 : Shifts 𝓜 0 yu := hunit yu hyuS hyz
  have hπ𝓜 : Shifts 𝓜 𝓜.period πE := uniformizerUnit_shifts hϖ 𝓜
  have hrel : (N.h : ℤ) * ℓ' + -N.k * (𝓜.period : ℤ) = 0 := by
    have h1 : Shifts 𝓜 ((N.h : ℤ) * ℓ' + -N.k * 𝓜.period) (N.residual bu πE) :=
      (hb𝓜.zpow N.h).mul (hπ𝓜.zpow (-N.k))
    rw [hres] at h1
    exact h1.stabilizerValuation_eq.symm.trans hy𝓜.stabilizerValuation_eq
  -- shift parameters on the refined chain
  have hcop : IsCoprime (N.h : ℤ) N.k := ⟨N.v, N.u, by linarith [N.bezout]⟩
  have hdvd : (N.h : ℤ) ∣ (𝓜.period : ℤ) * N.k := ⟨ℓ', by linarith⟩
  obtain ⟨g', hg'⟩ := hcop.dvd_of_dvd_mul_right hdvd
  have hhpos : (0 : ℤ) < N.h := by exact_mod_cast N.h_pos
  have he'pos : (0 : ℤ) < 𝓜.period := by exact_mod_cast 𝓜.period_pos
  have hg'pos : 0 < g' := by
    by_contra! hle
    nlinarith
  have hg'nat : ((g'.toNat : ℕ) : ℤ) = g' := Int.toNat_of_nonneg hg'pos.le
  have hℓ' : ℓ' = (g'.toNat : ℤ) * N.k := by
    rw [hg'nat]
    apply mul_left_cancel₀ hhpos.ne'
    linear_combination hrel + N.k * hg'
  let N' : ShiftParameters 𝓜.period ℓ' :=
    { g := g'.toNat
      h := N.h
      k := N.k
      u := N.u
      v := N.v
      g_pos := by omega
      h_pos := N.h_pos
      period_eq := by
        zify
        rw [hg'nat]
        exact hg'
      depth_eq := hℓ'
      bezout := N.bezout }
  have hzP : aeval (↑(N'.residual bu πE) : Module.End F V) (P.map (algebraMap 𝒪[F] F)) ∈
      𝓜.endFiltration 1 := by
    change aeval (↑(N.residual bu πE) : Module.End F V) (P.map (algebraMap 𝒪[F] F)) ∈ _
    rw [hres, hyu]
    exact hz𝓜
  -- the residual polynomial over the residue field
  let φ : 𝒪[F] ⧸ Ring.jacobson 𝒪[F] ≃+* ResidueField 𝒪[F] :=
    Ideal.quotEquivOfEq (jacobson_integer_eq_maximalIdeal F)
  have hresidue : residue 𝒪[F] = (φ : 𝒪[F] ⧸ Ring.jacobson 𝒪[F] →+* ResidueField 𝒪[F]).comp
      (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])) := by
    ext x
    rfl
  have hp : Irreducible (P.map (residue 𝒪[F])) := by
    rw [hresidue, ← Polynomial.map_map, hPmap]
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv φ).toMulEquiv).mpr hpirr
  obtain ⟨c, hc, ⟨hcf, hcn⟩, hck⟩ :=
    exists_simple_cyclic_lift 𝓜 bu hb𝓜 hϖ N' P hPmon hP₀ hp hzP
  have hcval : 𝓜.valuation c = (ℓ' : WithTop ℤ) :=
    𝓜.valuation_eq_of_mem_of_notMem hc.1 (hc.not_mem_succ hb𝓜.not_mem_succ)
  let T : Stratum 𝒪[F] F V :=
    ⟨𝓜, -ℓ', -ℓ' - 1, c, by omega, by rw [hcval]; exact_mod_cast (show -(-ℓ') ≤ ℓ' by omega)⟩
  refine ⟨T, ⟨⟨⟨hcf, hcn⟩, ?_⟩, ?_⟩, rfl, ?_, ?_, hlat⟩
  · change 𝓜.valuation c = _
    rw [hcval]
    exact_mod_cast (neg_neg ℓ').symm
  · change criticalExponent 𝓜 c < ((-(-ℓ' - 1) : ℤ) : WithBot ℤ)
    exact hck.trans_lt (WithBot.coe_lt_coe.mpr (by omega))
  · intro x hx
    change x - c ∈ 𝓜.endFiltration (-(-ℓ' - 1))
    have hx' : x - S.b ∈ 𝓛.endFiltration (-S.n + 1) := by
      have h : x - S.b ∈ S.chain.endFiltration (-S.r) := hx
      rwa [hr, show -(S.n - 1) = -S.n + 1 by ring] at h
    have h := sub_mem (hfilt hx') hc.2.2
    rw [hbu, sub_sub_sub_cancel_right] at h
    rwa [show -(-ℓ' - 1) = ℓ' + 1 by ring]
  · change S.n * (𝓜.period : ℤ) = -ℓ' * (𝓛.period : ℤ)
    have hper' : (𝓛.period : ℤ) = N.h * N.g := by exact_mod_cast hper
    linear_combination (-(𝓜.period : ℤ)) * hdepth + ℓ' * hper' + (N.g : ℤ) * hrel

end Langlands.BushnellKutzko.PureApproximation
