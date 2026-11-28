import Langlands.BushnellKutzko.RefinementDiagonal
import Langlands.BushnellKutzko.SubfieldLayerLifting
import Langlands.BushnellKutzko.SubfieldValuationShifts

/-! # An idempotent from a relative splitting basis -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.RelSplitIdempotent

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (𝓛 : LatticeChain 𝒪[F] F V) {m : ℕ} (w : Module.Basis (Fin m) E V)

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

open Classical in
/-- The basis lines `E w_k` on which the chain jumps between `L_0` and `L_1`. -/
def jumpFinset : Finset (Fin m) :=
  Finset.univ.filter fun k => ∃ c : E, c • w k ∈ 𝓛.lattice 0 ∧ c • w k ∉ 𝓛.lattice 1

omit [Algebra F E] [IsScalarTower F E V] in
theorem mem_jumpFinset {k : Fin m} :
    k ∈ jumpFinset 𝓛 w ↔ ∃ c : E, c • w k ∈ 𝓛.lattice 0 ∧ c • w k ∉ 𝓛.lattice 1 := by
  classical
  simp [jumpFinset]

/-- The `E`-linear projection onto the span of the jumping lines, along the other lines. -/
def projection : V →ₗ[E] V :=
  ∑ k ∈ jumpFinset 𝓛 w, (w.coord k).smulRight (w k)

/-- The projection as an `F`-linear endomorphism of `V`. -/
def blockIdempotent : Module.End F V :=
  (projection 𝓛 w).restrictScalars F

omit [Algebra F E] [IsScalarTower F E V] in
theorem projection_apply (v : V) :
    projection 𝓛 w v = ∑ k ∈ jumpFinset 𝓛 w, w.repr v k • w k := by
  simp [projection]

theorem blockIdempotent_apply (v : V) :
    blockIdempotent 𝓛 w v = ∑ k ∈ jumpFinset 𝓛 w, w.repr v k • w k :=
  projection_apply 𝓛 w v

omit [Algebra F E] [IsScalarTower F E V] in
theorem projection_basis (j : Fin m) :
    projection 𝓛 w (w j) = if j ∈ jumpFinset 𝓛 w then w j else 0 := by
  classical
  rw [projection_apply]
  simp only [Module.Basis.repr_self]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hj'
      exact absurd hj hj'
  · refine Finset.sum_eq_zero fun k hk => ?_
    have hkj : j ≠ k := by
      rintro rfl
      exact hj hk
    simp [hkj]

omit [Algebra F E] [IsScalarTower F E V] in
theorem projection_comp_projection : projection 𝓛 w ∘ₗ projection 𝓛 w = projection 𝓛 w := by
  refine w.ext fun j => ?_
  rw [LinearMap.comp_apply, projection_basis]
  split_ifs with hj
  · rw [projection_basis]
    simp [hj]
  · rw [map_zero]

theorem isIdempotentElem : IsIdempotentElem (blockIdempotent 𝓛 w) := by
  change (projection 𝓛 w).restrictScalars F * (projection 𝓛 w).restrictScalars F =
    (projection 𝓛 w).restrictScalars F
  ext v
  exact LinearMap.congr_fun (projection_comp_projection 𝓛 w) v

theorem blockIdempotent_smul (c : E) (v : V) :
    blockIdempotent 𝓛 w (c • v) = c • blockIdempotent 𝓛 w v :=
  (projection 𝓛 w).map_smul c v

theorem sub_blockIdempotent_apply (v : V) :
    v - blockIdempotent 𝓛 w v = ∑ k ∈ (jumpFinset 𝓛 w)ᶜ, w.repr v k • w k := by
  classical
  rw [blockIdempotent_apply]
  nth_rw 1 [← w.sum_repr v]
  rw [← Finset.sum_compl_add_sum (jumpFinset 𝓛 w), add_sub_cancel_right]

variable {𝓛 w}

omit [Algebra F E] [IsScalarTower F E V] in
/-- For a relative splitting basis, the terms of a lattice vector lie in the lattice. -/
theorem term_mem (hw : RelSplits (L := E) 𝓛 w) {i : ℤ} {v : V} (hv : v ∈ 𝓛.lattice i)
    (k : Fin m) : w.repr v k • w k ∈ 𝓛.lattice i :=
  hw i (fun j => w.repr v j) (by rw [w.sum_repr]; exact hv) k

theorem blockIdempotent_mem (hw : RelSplits (L := E) 𝓛 w) {i : ℤ} {v : V}
    (hv : v ∈ 𝓛.lattice i) : blockIdempotent 𝓛 w v ∈ 𝓛.lattice i := by
  rw [blockIdempotent_apply]
  exact Submodule.sum_mem _ fun k _ => term_mem hw hv k

theorem blockIdempotent_mem_order (hw : RelSplits (L := E) 𝓛 w) :
    blockIdempotent 𝓛 w ∈ 𝓛.order := by
  rw [LatticeChain.mem_order]
  exact fun i v hv => blockIdempotent_mem hw hv

section Shift

variable (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
  [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]
  {ϖ : 𝒪ₑ[F,E]} (hϖ : Irreducible ϖ)

/-- The shift of the chain under the extension uniformizer. -/
abbrev uniformizerShift : ℤ :=
  (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd

omit [IsFractionRing 𝒪ₑ[F,E] E] in
include hϖ in
/-- A nonzero element of `E` either has integral inverse or is a multiple of the uniformizer. -/
theorem inv_integral_or_dvd {t : E} (_ht : t ≠ 0) [IsFractionRing 𝒪ₑ[F,E] E] :
    (∃ s : 𝒪ₑ[F,E], (s : E) = t⁻¹) ∨ ∃ s : 𝒪ₑ[F,E], t = (ϖ : E) * s := by
  rcases ValuationRing.isInteger_or_isInteger 𝒪ₑ[F,E] (K := E) t⁻¹ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨s, hs⟩
  · rw [inv_inv] at hs
    by_cases hu : IsUnit s
    · left
      refine ⟨(hu.unit⁻¹ : (𝒪ₑ[F,E])ˣ), ?_⟩
      rw [← hs]
      have h1 : ((hu.unit⁻¹ : (𝒪ₑ[F,E])ˣ) : 𝒪ₑ[F,E]) * s = 1 := hu.val_inv_mul
      have h2 := congrArg (algebraMap 𝒪ₑ[F,E] E) h1
      rw [map_mul, map_one] at h2
      exact eq_inv_of_mul_eq_one_left h2
    · right
      have hmem : s ∈ IsLocalRing.maximalIdeal 𝒪ₑ[F,E] := hu
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
      obtain ⟨r, hr⟩ := hmem
      refine ⟨r, ?_⟩
      rw [← hs, hr]
      rfl

include hE hϖ in
/-- Within one window of length the uniformizer shift, a line of `V` jumps at most once. -/
theorem smul_mem_succ_of_jump {y : V} {i i' : ℤ} (hy : y ∈ 𝓛.lattice i)
    (hy' : y ∉ 𝓛.lattice (i + 1)) (h1 : i + 1 ≤ i') (h2 : i' + 1 ≤ i + uniformizerShift hE hϖ)
    (t : E) (ht : t • y ∈ 𝓛.lattice i') : t • y ∈ 𝓛.lattice (i' + 1) := by
  by_cases ht0 : t = 0
  · rw [ht0, zero_smul]
    exact zero_mem _
  rcases inv_integral_or_dvd hϖ ht0 with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    apply hy'
    have h := 𝓛.subfieldInteger_smul_mem E hE i' s ht
    rw [hs, smul_smul, inv_mul_cancel₀ ht0, one_smul] at h
    exact 𝓛.antitone h1 h
  · have hpy : (ϖ : E) • y ∈ 𝓛.lattice (i + uniformizerShift hE hϖ) :=
      (𝓛.mem_lattice_fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero) i).mpr hy
    have h := 𝓛.subfieldInteger_smul_mem E hE _ s hpy
    rw [smul_smul, mul_comm, ← hs] at h
    exact 𝓛.antitone h2 h

omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
include hE in
/-- Scaling by a power of the uniformizer moves the chain by multiples of its shift. -/
theorem zpow_smul_mem_iff (q : ℤ) (j : ℤ) (v : V) :
    (((subfieldIntegerUnit E hϖ.ne_zero) ^ q : Eˣ) : E) • v ∈
        𝓛.lattice (j + q * uniformizerShift hE hϖ) ↔ v ∈ 𝓛.lattice j := by
  have h := 𝓛.mem_lattice_fieldShift E hE ((subfieldIntegerUnit E hϖ.ne_zero) ^ q) j (v := v)
  rw [map_zpow, toAdd_zpow, smul_eq_mul] at h
  exact h

variable {hE}

include hϖ in
/-- On a jumping line, the chain does not jump at an index not divisible by the shift. -/
theorem jump_line_mem_succ (hpos : 0 < uniformizerShift hE hϖ) {k : Fin m}
    (hk : k ∈ jumpFinset 𝓛 w) {i : ℤ} (hi : ¬ uniformizerShift hE hϖ ∣ i) (c : E)
    (hc : c • w k ∈ 𝓛.lattice i) : c • w k ∈ 𝓛.lattice (i + 1) := by
  set p := uniformizerShift hE hϖ
  obtain ⟨c₀, h0, h1⟩ := (mem_jumpFinset 𝓛 w).mp hk
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h1
    exact h1 (zero_mem _)
  set q := i / p
  set u := ((subfieldIntegerUnit E hϖ.ne_zero) ^ q : Eˣ)
  have hy0 : (u : E) • (c₀ • w k) ∈ 𝓛.lattice (q * p) := by
    have := (zpow_smul_mem_iff hE hϖ q 0 (c₀ • w k)).mpr h0
    rwa [zero_add] at this
  have hy1 : (u : E) • (c₀ • w k) ∉ 𝓛.lattice (q * p + 1) := by
    intro h
    apply h1
    refine (zpow_smul_mem_iff hE hϖ q 1 (c₀ • w k)).mp ?_
    rw [show (1 : ℤ) + q * p = q * p + 1 by ring]
    exact h
  have hdiv : i = q * p + i % p := by
    have := Int.emod_add_ediv_mul i p
    linarith
  have hr0 : 0 ≤ i % p := Int.emod_nonneg i (ne_of_gt hpos)
  have hrp : i % p < p := Int.emod_lt_of_pos i hpos
  have hr1 : i % p ≠ 0 := fun h => hi (Int.dvd_of_emod_eq_zero h)
  have hr1' : 1 ≤ i % p := by
    rcases lt_or_eq_of_le hr0 with h | h
    · exact h
    · exact absurd h.symm hr1
  have hunit : ((u : E) * c₀) ≠ 0 := mul_ne_zero u.ne_zero hc₀
  have hck : c • w k = (c * ((u : E) * c₀)⁻¹) • ((u : E) • (c₀ • w k)) := by
    rw [smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel₀ hunit, mul_one]
  rw [hck] at hc ⊢
  exact smul_mem_succ_of_jump hE hϖ (i := q * p) (i' := i) hy0 hy1 (by linarith)
    (by linarith) _ hc

omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
include hϖ in
/-- On a line which does not jump between `L_0` and `L_1`, the chain does not jump at multiples
of the shift. -/
theorem nonjump_line_mem_succ {k : Fin m} (hk : k ∉ jumpFinset 𝓛 w) {i : ℤ}
    (hi : uniformizerShift hE hϖ ∣ i) (c : E) (hc : c • w k ∈ 𝓛.lattice i) :
    c • w k ∈ 𝓛.lattice (i + 1) := by
  set p := uniformizerShift hE hϖ
  obtain ⟨q, rfl⟩ := hi
  set u := ((subfieldIntegerUnit E hϖ.ne_zero) ^ (-q) : Eˣ)
  have h0 : (u : E) • (c • w k) ∈ 𝓛.lattice 0 := by
    refine (zpow_smul_mem_iff hE hϖ (-q) (p * q) _).mpr hc |> fun h => ?_
    rwa [show p * q + -q * p = 0 by ring] at h
  have h1 : (u : E) • (c • w k) ∈ 𝓛.lattice 1 := by
    by_contra hnot
    apply hk
    rw [mem_jumpFinset]
    exact ⟨(u : E) * c, by rwa [mul_smul], by rwa [mul_smul]⟩
  have h2 := (zpow_smul_mem_iff hE hϖ (-q) (p * q + 1) (c • w k)).mp
    (by rwa [show p * q + 1 + -q * p = 1 by ring])
  exact h2

include hϖ in
/-- At an index not divisible by the shift, the idempotent maps `L_i` into `L_{i+1}`. -/
theorem blockIdempotent_mem_succ (hw : RelSplits (L := E) 𝓛 w)
    (hpos : 0 < uniformizerShift hE hϖ) {i : ℤ} (hi : ¬ uniformizerShift hE hϖ ∣ i) {v : V}
    (hv : v ∈ 𝓛.lattice i) : blockIdempotent 𝓛 w v ∈ 𝓛.lattice (i + 1) := by
  rw [blockIdempotent_apply]
  exact Submodule.sum_mem _ fun k hk =>
    jump_line_mem_succ hϖ hpos hk hi _ (term_mem hw hv k)

omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
include hϖ in
/-- At a multiple of the shift, the complementary idempotent maps `L_i` into `L_{i+1}`. -/
theorem sub_blockIdempotent_mem_succ (hw : RelSplits (L := E) 𝓛 w) {i : ℤ}
    (hi : uniformizerShift hE hϖ ∣ i) {v : V} (hv : v ∈ 𝓛.lattice i) :
    v - blockIdempotent 𝓛 w v ∈ 𝓛.lattice (i + 1) := by
  rw [sub_blockIdempotent_apply]
  exact Submodule.sum_mem _ fun k hk =>
    nonjump_line_mem_succ hϖ (Finset.mem_compl.mp hk) hi _ (term_mem hw hv k)

include hϖ in
/-- The corners `ε x (1 - ε)` and `(1 - ε) x ε` of every `x ∈ 𝔄` lie in `𝔓 = End^1(𝓛)`. -/
theorem offDiagonal_mem (hw : RelSplits (L := E) 𝓛 w) (hpos : 0 < uniformizerShift hE hϖ)
    {x : Module.End F V} (hx : x ∈ 𝓛.order) :
    blockIdempotent 𝓛 w * x * (1 - blockIdempotent 𝓛 w) ∈ 𝓛.endFiltration 1 ∧
      (1 - blockIdempotent 𝓛 w) * x * blockIdempotent 𝓛 w ∈ 𝓛.endFiltration 1 := by
  set ε := blockIdempotent 𝓛 w
  have hxL : ∀ {j : ℤ} {v : V}, v ∈ 𝓛.lattice j → x v ∈ 𝓛.lattice j := fun hv =>
    (LatticeChain.mem_order 𝓛).mp hx _ _ hv
  have hεL : ∀ {j : ℤ} {v : V}, v ∈ 𝓛.lattice j → ε v ∈ 𝓛.lattice j := fun hv =>
    blockIdempotent_mem hw hv
  have hfL : ∀ {j : ℤ} {v : V}, v ∈ 𝓛.lattice j → (1 - ε) v ∈ 𝓛.lattice j := fun hv => by
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact sub_mem hv (hεL hv)
  constructor
  · intro i v hv
    change ε (x ((1 - ε) v)) ∈ 𝓛.lattice (i + 1)
    by_cases hdiv : uniformizerShift hE hϖ ∣ i
    · have h1 : (1 - ε) v ∈ 𝓛.lattice (i + 1) := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        exact sub_blockIdempotent_mem_succ hϖ hw hdiv hv
      exact hεL (hxL h1)
    · exact blockIdempotent_mem_succ hϖ hw hpos hdiv (hxL (hfL hv))
  · intro i v hv
    change (1 - ε) (x (ε v)) ∈ 𝓛.lattice (i + 1)
    by_cases hdiv : uniformizerShift hE hϖ ∣ i
    · rw [LinearMap.sub_apply, Module.End.one_apply]
      exact sub_blockIdempotent_mem_succ hϖ hw hdiv (hxL (hεL hv))
    · exact hfL (hxL (blockIdempotent_mem_succ hϖ hw hpos hdiv hv))

omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
include hE hϖ in
theorem blockIdempotent_ne_zero (hw : RelSplits (L := E) 𝓛 w) : blockIdempotent 𝓛 w ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv'⟩ := IsConcreteLE.exists_of_lt (𝓛.lattice_succ_lt 0)
  apply hv'
  have h := sub_blockIdempotent_mem_succ (hE := hE) hϖ hw (dvd_zero _) hv
  rwa [h0, LinearMap.zero_apply, sub_zero, zero_add] at h

include hϖ in
theorem blockIdempotent_ne_one (hw : RelSplits (L := E) 𝓛 w)
    (hp : 2 ≤ uniformizerShift hE hϖ) : blockIdempotent 𝓛 w ≠ 1 := by
  intro h1
  obtain ⟨v, hv, hv'⟩ := IsConcreteLE.exists_of_lt (𝓛.lattice_succ_lt 1)
  apply hv'
  have hndvd : ¬ uniformizerShift hE hϖ ∣ 1 := by
    intro hd
    have := Int.le_of_dvd one_pos hd
    omega
  have h := blockIdempotent_mem_succ hϖ hw (by omega) hndvd hv
  rwa [h1, Module.End.one_apply] at h

end Shift

end Langlands.BushnellKutzko.RelSplitIdempotent
