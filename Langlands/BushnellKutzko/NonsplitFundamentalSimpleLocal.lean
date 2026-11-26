import Langlands.BushnellKutzko.NonsplitFundamentalSimpleResidue
import Langlands.BushnellKutzko.NonsplitRefinementProof

/-! # The semisimplicity criterion over the integers of a local field

For a nonsplit fundamental stratum `[𝓛, n, n-1, b]` over `𝔬_F`, `exists_nonsplitData` shows
that `b` is a unit translating the chain by `-n` and that a monic lift `P` of the irreducible
residual polynomial satisfies `P(y)^m ∈ 𝔓` for the residual element `y = ϖ^{-k} b^h`. The
stratum is equivalent to a simple stratum on the same chain and levels exactly when
`P(y) ∈ 𝔓` (`aeval_mem_of_simple`, `exists_simple_of_aeval_mem`), which is exactly when the
residue centralizer is semisimple. `nonsplitSimpleCriterion_integer` is BK93 (2.4.13) over `𝔬_F`.
-/

noncomputable section

open ValuativeRel Polynomial IsLocalRing

namespace Langlands.BushnellKutzko.NonsplitSimple

open LatticeChain CriticalDerived NonsplitRefinement

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- Polynomials with integral coefficients respect congruence modulo `𝔓`. -/
theorem aeval_sub_mem_of_sub_mem {O K : Type*} [CommRing O] [Field K] [Algebra O K]
    [Module K V] [Module O V] [IsScalarTower O K V] (𝓛 : LatticeChain O K V)
    {x x' : 𝓛.order} (h : (x : Module.End K V) - x' ∈ 𝓛.endFiltration 1) (Q : O[X]) :
    ((aeval x Q : 𝓛.order) : Module.End K V) - (aeval x' Q : 𝓛.order) ∈ 𝓛.endFiltration 1 := by
  apply (𝓛.layerAction_eq_iff _ _).mp
  intro i
  have hi := (𝓛.layerAction_eq_iff x x').mpr h i
  rw [← layerHom_apply, ← aeval_algHom_apply, layerHom_apply, hi, ← layerHom_apply,
    aeval_algHom_apply, layerHom_apply]

/-- The data of BK93 (2.3.3) attached to a nonsplit fundamental stratum: `b` is a unit
translating the chain by `-n`, and a monic lift `P` of the irreducible residual polynomial has
a power killing the residual element `y = ϖ^{-k} b^h` modulo `𝔓`. -/
structure NonsplitData (S : Stratum 𝒪[F] F V) where
  ϖ : 𝒪[F]
  hϖ : Irreducible ϖ
  N : ShiftParameters S.chain.period (-S.n)
  B : (Module.End F V)ˣ
  hB : Shifts S.chain (-S.n) B
  hBb : S.b = B
  P : 𝒪[F][X]
  hPmon : P.Monic
  hP₀ : IsUnit (P.coeff 0)
  hPirr : Irreducible (P.map (residue 𝒪[F]))
  m : ℕ
  hm : 0 < m
  hPm : aeval (residualOrder S hB hϖ N) P ^ m ∈ S.chain.firstFiltrationIdeal

/-- The residual element is `ϖ^{-k} b^h`. -/
theorem coe_residualOrder_eq (S : Stratum 𝒪[F] F V) {B : (Module.End F V)ˣ}
    (hB : Shifts S.chain (-S.n) B) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (N : ShiftParameters S.chain.period (-S.n)) :
    (residualOrder S hB hϖ N : Module.End F V) =
      ((N.residual B (scalarEndUnit (uniformizerAsUnit hϖ)) : (Module.End F V)ˣ) :
        Module.End F V) := by
  rw [coe_residualOrder, residualStab, ShiftParameters.residual, ShiftParameters.residual]
  rfl

/-- The residual element is `ϖ^{-k} b^h`. -/
theorem coe_residualOrder_eq_smul (S : Stratum 𝒪[F] F V) {B : (Module.End F V)ˣ}
    (hB : Shifts S.chain (-S.n) B) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (N : ShiftParameters S.chain.period (-S.n)) (hBb : S.b = B) :
    (residualOrder S hB hϖ N : Module.End F V) = ((ϖ : F) ^ (-N.k)) • S.b ^ N.h := by
  rw [coe_residualOrder_eq, ShiftParameters.residual, Units.val_mul, coe_scalarEndUnit_zpow,
    coe_uniformizerAsUnit, zpow_natCast, Units.val_pow_eq_pow_val, ← hBb, ← Algebra.commutes,
    ← Algebra.smul_def]

/-- A nonsplit fundamental stratum over `𝔬_F` carries the data of `NonsplitData`. -/
theorem exists_nonsplitData (S : Stratum 𝒪[F] F V) (hS : S.IsNonsplit) :
    Nonempty (NonsplitData S) := by
  have := S.chain.finiteDimensional
  obtain ⟨⟨hr, hnil⟩, π, p, m, hpmon, hpirr, hm, hφ⟩ := hS
  have hϖ : Irreducible π.1 :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      (by rw [← jacobson_integer_eq_maximalIdeal F, π.2.2])
  set ϖ : 𝒪[F] := π.1 with hϖdef
  set ϖu := LatticeChain.uniformizerAsUnit hϖ with hϖudef
  set πE : (Module.End F V)ˣ := scalarEndUnit ϖu with hπEdef
  set 𝓛 := S.chain with h𝓛def
  obtain ⟨N, hNg⟩ := exists_shiftParameters_eq_gcd 𝓛.period_pos S.n
  have hhk : (N.h : ℤ) * (-S.n) + -N.k * (𝓛.period : ℤ) = 0 := N.residual_degree
  have hper : 𝓛.period = N.h * N.g := N.period_eq
  set y := S.fundamentalElement π with hydef
  have hy_eq : y = ((ϖ : F) ^ (-N.k)) • S.b ^ N.h := by
    have h1 : S.n / ((Nat.gcd S.chain.period S.n.natAbs : ℕ) : ℤ) = -N.k := by
      rw [← hNg]
      exact Int.ediv_eq_of_eq_mul_left (by exact_mod_cast N.g_pos.ne') (by linarith [N.depth_eq])
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
    rw [ShiftParameters.residual, zpow_natCast, hbuh, mul_assoc,
      (hcomm.zpow_left (-N.k)).symm.eq, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero,
      one_mul]
  let φ : 𝒪[F] ⧸ Ring.jacobson 𝒪[F] ≃+* ResidueField 𝒪[F] :=
    Ideal.quotEquivOfEq (jacobson_integer_eq_maximalIdeal F)
  have hresidue : residue 𝒪[F] = (φ : 𝒪[F] ⧸ Ring.jacobson 𝒪[F] →+* ResidueField 𝒪[F]).comp
      (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])) := by
    ext x
    rfl
  have hp : Irreducible (P.map (residue 𝒪[F])) := by
    rw [hresidue, ← Polynomial.map_map, hPmap]
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv φ).toMulEquiv).mpr hpirr
  refine ⟨⟨ϖ, hϖ, N, bu, hbuS, hbu.symm, P, hPmon, hP₀, hp, m, hm, ?_⟩⟩
  change ((aeval (residualOrder S hbuS hϖ N) P ^ m : S.chain.order) : Module.End F V) ∈
    S.chain.endFiltration 1
  rw [SubmonoidClass.coe_pow, aeval_subalgebra_coe, coe_residualOrder_eq, hres, hyu,
    ← aeval_map_algebraMap F]
  exact hPm

/-- If the stratum is equivalent to a simple stratum on the same chain and levels, then the
lifted residual polynomial kills the residual element modulo `𝔓`. -/
theorem aeval_mem_of_simple (S : Stratum 𝒪[F] F V) (D : NonsplitData S) (hr : S.r = S.n - 1)
    (T : Stratum 𝒪[F] F V) (hTc : T.chain = S.chain) (hTr : T.r = S.r)
    (hST : S.Equivalent T) (hT : T.IsSimple) :
    aeval (residualOrder S D.hB D.hϖ D.N) D.P ∈ S.chain.firstFiltrationIdeal := by
  set 𝓛 := S.chain with h𝓛
  set c := T.b with hcdef
  have hbS : S.b ∈ 𝓛.endFiltration (-S.n) := D.hBb ▸ D.hB.1
  have hbc : S.b - c ∈ 𝓛.endFiltration (-S.n + 1) := by
    have h : S.b ∈ T.coset := by
      rw [← hST]
      change S.b - S.b ∈ S.chain.endFiltration (-S.r)
      rw [sub_self]
      exact zero_mem _
    change S.b - T.b ∈ T.chain.endFiltration (-T.r) at h
    rwa [hTc, hTr, hr, show -(S.n - 1) = -S.n + 1 by ring] at h
  have hc : c ∈ 𝓛.endFiltration (-S.n) := by
    have h := sub_mem hbS (𝓛.endFiltration_antitone (show -S.n ≤ -S.n + 1 by omega) hbc)
    rwa [sub_sub_cancel] at h
  have hsym : SymbolEq 𝓛 (-S.n) c S.b := ⟨hc, hbS, by simpa using neg_mem hbc⟩
  have hpow := hsym.pow D.N.h
  have hdeg : (D.N.h : ℤ) * -S.n + 𝓛.period * -D.N.k = 0 := by
    linarith [D.N.residual_degree]
  set yc := ((D.ϖ : F) ^ (-D.N.k)) • c ^ D.N.h with hycdef
  have hyc0 : yc ∈ 𝓛.endFiltration 0 := by
    have h := zpow_smul_mem 𝓛 D.hϖ (-D.N.k) hpow.1
    rwa [hdeg] at h
  have hy := coe_residualOrder_eq_smul S D.hB D.hϖ D.N D.hBb
  have hdiff : yc - (residualOrder S D.hB D.hϖ D.N : Module.End F V) ∈ 𝓛.endFiltration 1 := by
    rw [hy, hycdef, ← smul_sub]
    have h := zpow_smul_mem 𝓛 D.hϖ (-D.N.k) hpow.2.2
    rwa [show (D.N.h : ℤ) * -S.n + 1 + 𝓛.period * -D.N.k = 1 by linarith] at h
  set z := residualOrder S D.hB D.hϖ D.N with hzdef
  let zc : 𝓛.order := ⟨yc, hyc0⟩
  have hcong := aeval_sub_mem_of_sub_mem 𝓛 (x := zc) (x' := z) hdiff D.P
  have hpowcong := aeval_sub_mem_of_sub_mem 𝓛 (x := zc) (x' := z) hdiff (D.P ^ D.m)
  rw [map_pow, map_pow] at hpowcong
  have hzm : ((aeval z D.P ^ D.m : 𝓛.order) : Module.End F V) ∈ 𝓛.endFiltration 1 := D.hPm
  have hwm : ((aeval zc D.P : 𝓛.order) : Module.End F V) ^ D.m ∈ 𝓛.endFiltration 1 := by
    have h := add_mem hpowcong hzm
    rwa [sub_add_cancel, SubmonoidClass.coe_pow] at h
  set w := ((aeval zc D.P : 𝓛.order) : Module.End F V) with hwdef
  have hw0' : w ∈ 𝓛.endFiltration 0 := (aeval zc D.P).2
  -- `w` lies in the field generated by `c`
  have hycE : yc ∈ elementAlgebra c :=
    Subalgebra.smul_mem _ (pow_mem (Algebra.self_mem_adjoin_singleton F c) _) _
  have hwE : w ∈ elementAlgebra c := by
    rw [hwdef, aeval_subalgebra_coe, ← aeval_map_algebraMap F]
    change aeval ((⟨yc, hycE⟩ : elementAlgebra c) : Module.End F V) _ ∈ _
    rw [← aeval_subalgebra_coe]
    exact Subtype.mem _
  obtain ⟨⟨hf, hn⟩, -⟩ := hT.1
  have hNU : NormalizingUnits 𝓛 (elementAlgebra c) := by
    have h := normalizingUnits_of_isField T.chain hf hn
    rwa [hTc] at h
  have hw1 : w ∈ 𝓛.endFiltration 1 := by
    by_cases hw : w = 0
    · rw [hw]
      exact zero_mem _
    obtain ⟨g, hgw, hgS⟩ := hNU w hwE hw
    have hsh := Shifts.of_stabilizer (𝓛 := 𝓛) ⟨g, hgS⟩
    set s := 𝓛.stabilizerValuation ⟨g, hgS⟩
    change Shifts 𝓛 s g at hsh
    have hs0 : 0 ≤ s := by
      by_contra hneg
      apply hsh.not_mem_succ
      rw [hgw]
      exact 𝓛.endFiltration_antitone (show s + 1 ≤ 0 by omega) hw0'
    have hs1 : 1 ≤ s := by
      by_contra hlt
      have hs : s = 0 := by omega
      apply (hsh.pow D.m).not_mem_succ
      rw [Units.val_pow_eq_pow_val, hgw, hs, mul_zero, zero_add]
      exact hwm
    rw [← hgw]
    exact 𝓛.endFiltration_antitone hs1 hsh.1
  change ((aeval z D.P : 𝓛.order) : Module.End F V) ∈ 𝓛.endFiltration 1
  have h := sub_mem hw1 hcong
  rwa [sub_sub_cancel] at h

/-- If the lifted residual polynomial kills the residual element modulo `𝔓`, the stratum is
equivalent to a simple stratum on the same chain and levels. -/
theorem exists_simple_of_aeval_mem (S : Stratum 𝒪[F] F V) (D : NonsplitData S)
    (hr : S.r = S.n - 1)
    (h : aeval (residualOrder S D.hB D.hϖ D.N) D.P ∈ S.chain.firstFiltrationIdeal) :
    ∃ T : Stratum 𝒪[F] F V,
      T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ S.Equivalent T ∧ T.IsSimple := by
  have hzP : aeval (↑(D.N.residual D.B (scalarEndUnit (uniformizerAsUnit D.hϖ))) :
      Module.End F V) (D.P.map (algebraMap 𝒪[F] F)) ∈ S.chain.endFiltration 1 := by
    change ((aeval (residualOrder S D.hB D.hϖ D.N) D.P : S.chain.order) : Module.End F V) ∈
      S.chain.endFiltration 1 at h
    rwa [aeval_subalgebra_coe, coe_residualOrder_eq, ← aeval_map_algebraMap F] at h
  obtain ⟨c, hc, ⟨hcf, hcn⟩, hck⟩ := exists_simple_cyclic_lift S.chain D.B D.hB D.hϖ D.N D.P
    D.hPmon D.hP₀ D.hPirr hzP
  have hcval : S.chain.valuation c = ((-S.n : ℤ) : WithTop ℤ) :=
    S.chain.valuation_eq_of_mem_of_notMem hc.1 (hc.not_mem_succ D.hB.not_mem_succ)
  let T : Stratum 𝒪[F] F V :=
    ⟨S.chain, S.n, S.r, c, S.r_lt_n, by rw [hcval]; exact_mod_cast le_rfl⟩
  have hcb : c - S.b ∈ S.chain.endFiltration (-S.r) := by
    rw [D.hBb, hr, show -(S.n - 1) = -S.n + 1 by ring]
    exact hc.2.2
  refine ⟨T, rfl, rfl, rfl, ?_, ⟨⟨⟨hcf, hcn⟩, ?_⟩, ?_⟩⟩
  · ext x
    change x - S.b ∈ S.chain.endFiltration (-S.r) ↔ x - c ∈ S.chain.endFiltration (-S.r)
    constructor
    · intro hx
      have h := sub_mem hx hcb
      rwa [sub_sub_sub_cancel_right] at h
    · intro hx
      have h := add_mem hx hcb
      rwa [sub_add_sub_cancel] at h
  · change S.chain.valuation c = _
    rw [hcval]
    rfl
  · change criticalExponent S.chain c < ((-S.r : ℤ) : WithBot ℤ)
    exact hck.trans_lt (WithBot.coe_lt_coe.mpr (by omega))

/-- **BK93 (2.4.13)** over the integers of a nonarchimedean local field. -/
theorem nonsplitSimpleCriterion_integer (S : Stratum 𝒪[F] F V) : S.NonsplitSimpleCriterion := by
  intro _ hS
  obtain ⟨D⟩ := exists_nonsplitData S hS
  have hr : S.r = S.n - 1 := hS.1.1
  constructor
  · rintro ⟨T, hTc, -, hTr, hST, hT⟩
    exact isSemisimpleRing_of_aeval_mem S D.hB D.hϖ D.N D.hBb D.hPirr
      (aeval_mem_of_simple S D hr T hTc hTr hST hT)
  · intro hss
    exact exists_simple_of_aeval_mem S D hr
      (aeval_mem_of_isSemisimpleRing S D.hB D.hϖ D.N D.hBb D.hPm)

end Langlands.BushnellKutzko.NonsplitSimple
