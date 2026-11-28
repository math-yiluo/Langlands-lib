import Langlands.BushnellKutzko.SimpleStratumConjugacyCyclic

/-! # Intertwined pure strata of depth `n − 1` are conjugate

Let `A₁, A₂` be units of `End_F(V)` which shift the chain by the same integer `d`, such that
every nonzero element of their generated algebras is a unit normalizing the chain. Suppose
that the cosets `A₂ + 𝔓^{d+1}` and `A₁ + 𝔓^{d+1}` are intertwined by some `g ∈ G`. Then a
unit `u` of `𝔄` conjugates `A₂` into `A₁ + 𝔓^{d+1}`. For the elements of pure strata
`[𝔄,n,n−1,β_i]` this is the case `t = n − 1` of the proof of BK93 (2.6.1), printed pp. 83–84.
-/

noncomputable section

open ValuativeRel IsLocalRing Polynomial

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The degree-zero generator `A^h π^{−k}` lies in `F[A]`. -/
theorem residual_mem_elementAlgebra {e : ℕ} {d : ℤ} (N : ShiftParameters e d) (B : Aˣ)
    (π₀ : Fˣ) : ((N.residual B (scalarEndUnit π₀) : Aˣ) : A) ∈ elementAlgebra (B : A) := by
  rw [ShiftParameters.residual, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val,
    NonsplitRefinement.coe_scalarEndUnit_zpow]
  exact mul_mem (pow_mem (Algebra.self_mem_adjoin_singleton F _) _)
    (Subalgebra.algebraMap_mem _ _)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Congruent units of degree `d` have congruent degree-zero generators. -/
theorem residual_symbolEq {d : ℤ} (N : ShiftParameters 𝓛.period d) {π X B : Aˣ}
    (hπ : Shifts 𝓛 𝓛.period π) (h : SymbolEq 𝓛 d (X : A) B) :
    SymbolEq 𝓛 0 ((N.residual X π : Aˣ) : A) ((N.residual B π : Aˣ) : A) := by
  have h₁ := (h.unit_pow N.h).mul (SymbolEq.refl (hπ.zpow (-N.k)).1)
  rw [N.residual_degree] at h₁
  simpa only [ShiftParameters.residual, zpow_natCast, Units.val_mul] using h₁

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation commutes with forming the degree-zero generator when `π` is central. -/
theorem residual_conj {e : ℕ} {d : ℤ} (N : ShiftParameters e d) (π₀ : Fˣ) (X g : Aˣ) :
    N.residual (g⁻¹ * X * g) (scalarEndUnit π₀) =
      g⁻¹ * N.residual X (scalarEndUnit π₀) * g := by
  have hc : Commute ((scalarEndUnit π₀ : Aˣ) ^ (-N.k)) g :=
    (scalarEndUnit_commutes π₀ g).zpow_left _
  have hp : (g⁻¹ * X * g) ^ N.h = g⁻¹ * X ^ N.h * g := by
    simpa only [inv_inv] using _root_.conj_pow (a := g⁻¹) (b := X) (i := N.h)
  simp only [ShiftParameters.residual, zpow_natCast, hp]
  rw [mul_assoc (g⁻¹ * X ^ N.h), ← hc.eq]
  simp only [mul_assoc]

/-- **The depth-`(d+1)` conjugacy of normalizing units.** Let `A₁, A₂` shift the chain by
`d`, such that every nonzero element of their generated algebras is a unit normalizing the
chain. If some `g` carries an element of `A₂ + 𝔓^{d+1}` into `A₁ + 𝔓^{d+1}`, then a unit `u`
of `𝔄` satisfies `u A₂ u⁻¹ ∈ A₁ + 𝔓^{d+1}`. -/
theorem exists_conj_symbol_of_intertwined {d : ℤ} {A₁ A₂ : Aˣ}
    (h₁ : Shifts 𝓛 d A₁) (h₂ : Shifts 𝓛 d A₂)
    (hN₁ : NormalizingUnits 𝓛 (elementAlgebra (A₁ : A)))
    (hN₂ : NormalizingUnits 𝓛 (elementAlgebra (A₂ : A)))
    {g : Aˣ} {x : A} (hx : SymbolEq 𝓛 d x A₂)
    (hgx : SymbolEq 𝓛 d (((g⁻¹ : Aˣ) : A) * x * g) A₁) :
    ∃ u : Aˣ, Shifts 𝓛 0 u ∧ SymbolEq 𝓛 d ((u : A) * A₂ * ((u⁻¹ : Aˣ) : A)) A₁ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let π₀ := LatticeChain.uniformizerAsUnit hϖ
  let π : Aˣ := scalarEndUnit π₀
  have hπ : Shifts 𝓛 𝓛.period π := uniformizerUnit_shifts hϖ 𝓛
  obtain ⟨N⟩ := exists_shiftParameters 𝓛.period_pos d
  have hC₁ : Commute A₁ π := (scalarEndUnit_commutes π₀ A₁).symm
  have hC₂ : Commute A₂ π := (scalarEndUnit_commutes π₀ A₂).symm
  obtain ⟨hz₁, ht₁⟩ := N.shifts_residual_shift h₁ hπ
  obtain ⟨hz₂, ht₂⟩ := N.shifts_residual_shift h₂ hπ
  -- the residual polynomial of the first degree-zero generator
  obtain ⟨Pol, hPm, hP₀, hPirr, hP₁⟩ := exists_residual_polynomial_of_normalizing 𝓛 hN₁ hz₁
    (residual_mem_elementAlgebra N A₁ π₀)
  -- it also kills the second one modulo `𝔓`
  obtain ⟨X, hX, hXs⟩ := exists_unit_of_symbolEq_self 𝓛 h₂ hx
  have hZ : SymbolEq 𝓛 0 ((N.residual X π : Aˣ) : A) ((N.residual A₂ π : Aˣ) : A) :=
    residual_symbolEq 𝓛 N hπ (hX ▸ hx)
  have hgZ : SymbolEq 𝓛 0 (((g⁻¹ : Aˣ) : A) * ((N.residual X π : Aˣ) : A) * g)
      ((N.residual A₁ π : Aˣ) : A) := by
    have h := residual_symbolEq 𝓛 N hπ (X := g⁻¹ * X * g) (B := A₁)
      (by simpa only [Units.val_mul, hX] using hgx)
    rwa [residual_conj N π₀ X g, Units.val_mul, Units.val_mul] at h
  have hP₂ := aeval_mem_one_of_conj 𝓛 hN₂ Pol (residual_mem_elementAlgebra N A₂ π₀) hz₂.1 hZ hgZ hP₁
  -- the two cyclic bases and the common cyclic algebra
  let z₁ : 𝓛.order := ⟨_, 𝓛.mem_order_iff_mem_endFiltration.mpr hz₁.1⟩
  let z₂ : 𝓛.order := ⟨_, 𝓛.mem_order_iff_mem_endFiltration.mpr hz₂.1⟩
  obtain ⟨B₁, hB₁⟩ := exists_cyclicBasis_count 𝓛 hϖ N.period_eq Pol hPm hPirr z₁ hP₁
    (N.shift A₁ π) ht₁
  obtain ⟨B₂, hB₂⟩ := exists_cyclicBasis_count 𝓛 hϖ N.period_eq Pol hPm hPirr z₂ hP₂
    (N.shift A₂ π) ht₂
  have hf : 0 < Pol.natDegree := by
    rw [← hPm.natDegree_map (residue 𝒪[F])]
    exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hPirr)
  have hcount (i : Fin N.g) : B₂.count i = B₁.count i :=
    Nat.eq_of_mul_eq_mul_left hf ((hB₂ i).trans (hB₁ i).symm)
  let Q := Pol.map (algebraMap 𝒪[F] F)
  have hQ : Q.Monic := hPm.map _
  have hQf : Q.natDegree = Pol.natDegree := hPm.natDegree_map _
  have hQc : IsUnit (Q.coeff 0) := by rw [coeff_map]; exact hP₀.map _
  obtain ⟨M⟩ := exists_cyclicAlgebra Q hQ hQc π₀ N.u N.h_pos hQf hf
  have hU₁ := actionU_symbol hϖ M B₁ hQ hQf N.h_pos hf (N.residual_commutes_shift hC₁) ht₁ hz₁ hP₁
  have hT₁ := actionT_symbol hϖ M B₁ N.h_pos hf N.period_eq ht₁ hz₁ hπ (N.shift_carry hC₁) hU₁
  have hU₂ := actionU_symbol hϖ M B₂ hQ hQf N.h_pos hf (N.residual_commutes_shift hC₂) ht₂ hz₂ hP₂
  have hT₂ := actionT_symbol hϖ M B₂ N.h_pos hf N.period_eq ht₂ hz₂ hπ (N.shift_carry hC₂) hU₂
  obtain ⟨u, hu, hconj⟩ := exists_unit_conj_action 𝓛 M hcount
  -- conjugation by `u` carries the second pair of operators to the first one
  have hcU : (u : A) * (B₂.actionU M : A) * ((u⁻¹ : Aˣ) : A) = B₁.actionU M := by
    change (u : A) * B₂.action M (M.U : M.A) * ((u⁻¹ : Aˣ) : A) = B₁.action M (M.U : M.A)
    rw [hconj, mul_assoc, Units.mul_inv, mul_one]
  have hcT : (u : A) * (B₂.actionT M : A) * ((u⁻¹ : Aˣ) : A) = B₁.actionT M := by
    change (u : A) * B₂.action M (M.T : M.A) * ((u⁻¹ : Aˣ) : A) = B₁.action M (M.T : M.A)
    rw [hconj, mul_assoc, Units.mul_inv, mul_one]
  have hsymU : SymbolEq 𝓛 0 (((u * N.residual A₂ π * u⁻¹ : Aˣ)) : A)
      ((N.residual A₁ π : Aˣ) : A) := by
    have h := ((SymbolEq.refl hu.1).mul hU₂.symm).mul (SymbolEq.refl hu.2)
    rw [hcU, add_zero, neg_zero, add_zero] at h
    simpa only [Units.val_mul] using h.trans hU₁
  have hsymT : SymbolEq 𝓛 N.g (((u * N.shift A₂ π * u⁻¹ : Aˣ)) : A)
      ((N.shift A₁ π : Aˣ) : A) := by
    have h := ((SymbolEq.refl hu.1).mul hT₂.symm).mul (SymbolEq.refl hu.2)
    rw [hcT, zero_add, neg_zero, add_zero] at h
    simpa only [Units.val_mul] using h.trans hT₁
  have hzs' : Shifts 𝓛 0 (u * N.residual A₂ π * u⁻¹) := by
    simpa only [add_zero, neg_zero] using (hu.mul hz₂).mul hu.inv
  have hts' : Shifts 𝓛 N.g (u * N.shift A₂ π * u⁻¹) := by
    simpa only [zero_add, add_zero, neg_zero] using (hu.mul ht₂).mul hu.inv
  have hlift := N.lifted_symbol hz₁ ht₁ hzs' hts' hsymU hsymT
  have hrec₁ := N.reconstruct hC₁
  have hrec₂ : (u * N.shift A₂ π * u⁻¹) ^ N.k * (u * N.residual A₂ π * u⁻¹) ^ N.v =
      u * A₂ * u⁻¹ := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_zpow, ← map_zpow, ← map_mul,
      N.reconstruct hC₂, MulAut.conj_apply]
  rw [hrec₁, hrec₂] at hlift
  exact ⟨u, hu, by simpa only [Units.val_mul] using hlift⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation by a unit of `𝔄` preserves every filtration step. -/
theorem conj_mem_of_shifts_zero {u : Aˣ} (hu : Shifts 𝓛 0 u) {x : A} {m : ℤ} (hx : x ∈ P m) :
    (u : A) * x * ((u⁻¹ : Aˣ) : A) ∈ P m := by
  have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hu.1 hx) hu.2
  simpa only [zero_add, neg_zero, add_zero] using h

/-- **The case `t = n − 1` of the proof of BK93 (2.6.1)**, printed pp. 83–84, for pure
strata on one chain. If the cosets `β₂ + 𝔓^{1−n}` and `β₁ + 𝔓^{1−n}` are intertwined, a unit
`u` of `𝔄` satisfies `u β₂ u⁻¹ ∈ β₁ + 𝔓^{1−n}`. -/
theorem exists_conj_of_isPure (S T : Stratum 𝒪[F] F V) (hchain : T.chain = S.chain)
    (hn : T.n = S.n) (hS : S.IsPure) (hT : T.IsPure) {g : Aˣ} {y : A}
    (hy : y - T.b ∈ S.chain.endFiltration (1 - S.n))
    (hgy : ((g⁻¹ : Aˣ) : A) * y * g - S.b ∈ S.chain.endFiltration (1 - S.n)) :
    ∃ u : Aˣ, Shifts S.chain 0 u ∧
      (u : A) * T.b * ((u⁻¹ : Aˣ) : A) - S.b ∈ S.chain.endFiltration (1 - S.n) := by
  obtain ⟨A₁, hA₁, h₁, hN₁⟩ := exists_shifts_of_isPure S hS
  obtain ⟨A₂, hA₂, h₂, hN₂⟩ := exists_shifts_of_isPure T hT
  rw [hchain, hn] at h₂
  rw [hchain] at hN₂
  have hsym {w b : A} {B : Aˣ} (hB : (B : A) = b) (hBs : Shifts S.chain (-S.n) B)
      (hw : w - b ∈ S.chain.endFiltration (1 - S.n)) : SymbolEq S.chain (-S.n) w B := by
    refine ⟨?_, hBs.1, ?_⟩
    · rw [show w = (w - b) + (B : A) by rw [hB]; abel]
      exact add_mem (S.chain.endFiltration_antitone (by omega) hw) hBs.1
    · rw [hB, show -S.n + 1 = 1 - S.n by ring]
      exact hw
  obtain ⟨u, hu, hsu⟩ := exists_conj_symbol_of_intertwined S.chain h₁ h₂
    (hA₁ ▸ hN₁) (hA₂ ▸ hN₂) (hsym hA₂ h₂ hy) (hsym hA₁ h₁ hgy)
  refine ⟨u, hu, ?_⟩
  rw [← hA₁, ← hA₂, show 1 - S.n = -S.n + 1 by ring]
  exact hsu.2.2

/-- The coset `c + 𝔓^{1−n}` is the coset of a unit shifting the chain by `−n` such that every
nonzero element of its generated algebra is a unit normalizing the chain (for instance the
element of a pure stratum), or it is the null coset `𝔓^{1−n}`. -/
def PureOrNull (n : ℤ) (c : A) : Prop :=
  (∃ B : Aˣ, Shifts 𝓛 (-n) B ∧ NormalizingUnits 𝓛 (elementAlgebra (B : A)) ∧
    c - B ∈ P (1 - n)) ∨ c ∈ P (1 - n)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The coset of a stratum equivalent at depth `n − 1` to a pure stratum on the same chain. -/
theorem pureOrNull_of_isPure (C : Stratum 𝒪[F] F V) (hC : C.chain = 𝓛) (hC' : C.IsPure)
    {c : A} (hc : c - C.b ∈ P (1 - C.n)) : PureOrNull 𝓛 C.n c := by
  subst hC
  obtain ⟨B, hB, hBs, hN⟩ := exists_shifts_of_isPure C hC'
  exact Or.inl ⟨B, hBs, hB ▸ hN, hB ▸ hc⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit shifting the chain by `d` which lies in `𝔓^m` and not in `𝔓^{m+1}` has `d = m`. -/
theorem shifts_eq_of_mem {d m : ℤ} {g : Aˣ} (hg : Shifts 𝓛 d g) (hm : (g : A) ∈ P m)
    (hm' : (g : A) ∉ P (m + 1)) : d = m := by
  have hle : 𝓛.lattice (0 + d) ≤ 𝓛.lattice (0 + m) := by
    rw [← hg.map_lattice 0]
    rintro _ ⟨v, hv, rfl⟩
    exact hm 0 v hv
  have h1 := 𝓛.strictAnti.le_iff_ge.mp hle
  by_contra hne
  exact hm' (𝓛.endFiltration_antitone (show m + 1 ≤ d by omega) hg.1)

/-- A nonzero scalar `c` shifts the chain by `e(𝓛) · ord(c)`. -/
theorem scalar_shifts {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : Fˣ) :
    Shifts 𝓛 (𝓛.period * ordOf hϖ (c : F)) (scalarEndUnit c) := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  have hci : ((c⁻¹ : Fˣ) : F) ≠ 0 := (c⁻¹).ne_zero
  constructor
  · intro i v hv
    change (c : F) • v ∈ 𝓛.lattice (i + 𝓛.period * ordOf hϖ (c : F))
    rw [𝓛.smul_mem_iff hϖ hc, add_sub_cancel_right]
    exact hv
  · intro i v hv
    change ((c⁻¹ : Fˣ) : F) • v ∈ 𝓛.lattice (i + -(𝓛.period * ordOf hϖ (c : F)))
    rw [𝓛.smul_mem_iff hϖ hci, Units.val_inv_eq_inv_val, ordOf_inv hϖ hc]
    rw [show i + -(↑𝓛.period * ordOf hϖ (c : F)) - ↑𝓛.period * -ordOf hϖ (c : F) = i by ring]
    exact hv

/-- Every nonzero element of the generated algebra of a scalar is a unit normalizing the
chain. -/
theorem normalizingUnits_algebraMap (δ : F) :
    NormalizingUnits 𝓛 (elementAlgebra (algebraMap F A δ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  intro X hX hX0
  have hbot : elementAlgebra (algebraMap F A δ) ≤ ⊥ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Subalgebra.algebraMap_mem ⊥ δ))
  obtain ⟨e, rfl⟩ := Algebra.mem_bot.mp (hbot hX)
  have he : e ≠ 0 := by
    rintro rfl
    exact hX0 (map_zero _)
  exact ⟨scalarEndUnit (Units.mk0 e he), rfl, (scalar_shifts 𝓛 hϖ _).mem_stabilizer⟩

/-- A coset congruent to a scalar of depth `−n` is pure or null. -/
theorem pureOrNull_of_scalar {n : ℤ} {c : A} (δ : F) (hδ : c - algebraMap F A δ ∈ P (1 - n))
    (hδn : algebraMap F A δ ∈ P (-n)) : PureOrNull 𝓛 n c := by
  by_cases h1 : algebraMap F A δ ∈ P (1 - n)
  · exact Or.inr (by simpa only [sub_add_cancel] using add_mem hδ h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact h1 (by rw [map_zero]; exact zero_mem _)
  let B : Aˣ := scalarEndUnit (Units.mk0 δ hδ0)
  have hBs := scalar_shifts 𝓛 hϖ (Units.mk0 δ hδ0)
  have hd := shifts_eq_of_mem 𝓛 hBs hδn (by rwa [show -n + 1 = 1 - n by ring])
  rw [hd] at hBs
  exact Or.inl ⟨B, hBs, normalizingUnits_algebraMap 𝓛 δ, hδ⟩

/-- **The final step in the proof of BK93 (2.6.1)**, printed pp. 85–86, for a single chain.
Two cosets `c_i + 𝔓^{1−n}`, each the coset of a pure stratum or the null coset, which are
intertwined, are conjugate by a unit of `𝔄`. The mixed case cannot occur, by the case of
equal orders and levels of BK93 (2.6.2), printed p. 86. -/
theorem exists_conj_of_pureOrNull {n : ℤ} {c₁ c₂ : A} (h₁ : PureOrNull 𝓛 n c₁)
    (h₂ : PureOrNull 𝓛 n c₂) {g : Aˣ} {y : A} (hy : y - c₂ ∈ P (1 - n))
    (hgy : ((g⁻¹ : Aˣ) : A) * y * g - c₁ ∈ P (1 - n)) :
    ∃ u : Aˣ, Shifts 𝓛 0 u ∧ (u : A) * c₂ * ((u⁻¹ : Aˣ) : A) - c₁ ∈ P (1 - n) := by
  have hsym {w b : A} {B : Aˣ} (hBs : Shifts 𝓛 (-n) B) (hwb : w - b ∈ P (1 - n))
      (hbB : b - B ∈ P (1 - n)) : SymbolEq 𝓛 (-n) w B := by
    have hw : w - B ∈ P (1 - n) := by
      simpa only [sub_add_sub_cancel] using add_mem hwb hbB
    refine ⟨?_, hBs.1, ?_⟩
    · rw [show w = (w - B) + (B : A) by abel]
      exact add_mem (𝓛.endFiltration_antitone (by omega) hw) hBs.1
    · rw [show -n + 1 = 1 - n by ring]
      exact hw
  rcases h₁ with ⟨B₁, hB₁, hN₁, hc₁⟩ | hc₁ <;> rcases h₂ with ⟨B₂, hB₂, hN₂, hc₂⟩ | hc₂
  · obtain ⟨u, hu, hsu⟩ := exists_conj_symbol_of_intertwined 𝓛 hB₁ hB₂ hN₁ hN₂
      (hsym hB₂ hy hc₂) (hsym hB₁ hgy hc₁)
    refine ⟨u, hu, ?_⟩
    have hconj := conj_mem_of_shifts_zero 𝓛 hu hc₂
    have hd := hsu.2.2
    rw [show -n + 1 = 1 - n by ring] at hd
    rw [show (u : A) * c₂ * ((u⁻¹ : Aˣ) : A) - c₁ =
      (u : A) * (c₂ - B₂) * ((u⁻¹ : Aˣ) : A) +
        ((u : A) * B₂ * ((u⁻¹ : Aˣ) : A) - B₁) + -(c₁ - B₁) by noncomm_ring]
    exact add_mem (add_mem hconj hd) (neg_mem hc₁)
  · exfalso
    have hy0 : y ∈ P (1 - n) := by
      simpa only [sub_add_cancel] using add_mem hy hc₂
    have hgy' : ((g⁻¹ : Aˣ) : A) * y * g - B₁ ∈ P (1 - n) := by
      simpa only [sub_add_sub_cancel] using add_mem hgy hc₁
    apply conj_not_mem_of_shifts 𝓛 hB₁ hgy' g⁻¹
    rw [inv_inv]
    have he : (g : A) * (((g⁻¹ : Aˣ) : A) * y * g) * ((g⁻¹ : Aˣ) : A) = y := by
      simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
    rw [he]
    exact hy0
  · exfalso
    have hy' : y - B₂ ∈ P (1 - n) := by
      simpa only [sub_add_sub_cancel] using add_mem hy hc₂
    apply conj_not_mem_of_shifts 𝓛 hB₂ hy' g
    simpa only [sub_add_cancel] using add_mem hgy hc₁
  · refine ⟨1, Shifts.one, ?_⟩
    simpa only [Units.val_one, one_mul, inv_one, mul_one] using sub_mem hc₂ hc₁

end Langlands.BushnellKutzko.SimpleConjugacy
