import Langlands.BushnellKutzko.MoyReduction

/-! # Moy's reduction with a compatible chain

Bushnell 1987, Theorem 1 (BK93 (2.3.1)) in the form of the Library's
`LatticeChain.exists_latticeChain_of_pow_mem`, with the additional information that every lattice
of the new chain is sandwiched between two consecutive lattices of the original chain. This is
the compatibility of the two hereditary orders asserted after (2.3.1) in BK93, printed p. 57
(citing Kutzko–Manderscheid, Prop. 3.5), in the sense of (1.1.9), printed p. 23. In Bushnell's
construction (printed pp. 194–195) every lattice of the new chain is of the form `ϖ^k I^l(L_q)`,
and each such lattice is sandwiched.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u

section Sandwich

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*}

namespace LatticeChain

variable {𝓛 : LatticeChain 𝒪[F] F (ι → F)}

/-- `LatticeChain.exists_latticeChain_shift`, recording that every lattice of the new chain is
sandwiched in the original chain. -/
theorem exists_latticeChain_shift_sandwiched
    (J : Submodule 𝒪[F] (ι → F) → Submodule 𝒪[F] (ι → F)) (hmono : Monotone J)
    (hsmul : ∀ (k : ℤ) (M : Submodule 𝒪[F] (ι → F)),
      J (uniformizerAsUnit hϖ ^ k • M) = uniformizerAsUnit hϖ ^ k • J M)
    (hsw : ∀ (p : ℤ) (M : Submodule 𝒪[F] (ι → F)), 𝓛.IsSandwiched p M →
      ∃ p', 𝓛.IsSandwiched p' (J M))
    {a : ℕ} (ha : 1 ≤ a) {q m : ℤ}
    (hper : J^[a] (𝓛.lattice q) = uniformizerAsUnit hϖ ^ m • 𝓛.lattice q) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F (ι → F)) (c : ℤ),
      (∀ t, 𝓜.lattice (t + c) = J (𝓜.lattice t)) ∧ (a : ℤ) * c = 𝓜.period * m ∧
        ∀ t, ∃ p, 𝓛.IsSandwiched p (𝓜.lattice t) := by
  classical
  set u := uniformizerAsUnit hϖ with hu
  set B := 𝓛.lattice q with hB
  have hsmulI : ∀ (l : ℕ) (k : ℤ) (M : Submodule 𝒪[F] (ι → F)),
      J^[l] (u ^ k • M) = u ^ k • J^[l] M :=
    iterate_zpow_smul_comm J u hsmul
  have hswI : ∀ l : ℕ, ∃ p, 𝓛.IsSandwiched p (J^[l] B) := by
    intro l
    induction l with
    | zero => exact ⟨q, isSandwiched_lattice q⟩
    | succ l ih =>
      obtain ⟨p, hp⟩ := ih
      rw [Function.iterate_succ_apply']
      exact hsw p _ hp
  have hred : ∀ (k : ℤ) (l : ℕ),
      u ^ k • J^[l] B = u ^ (k + m * ((l / a : ℕ) : ℤ)) • J^[l % a] B := by
    intro k l
    have h : J^[l] B = u ^ (m * ((l / a : ℕ) : ℤ)) • J^[l % a] B := by
      rw [← hsmulI, ← iterate_mul_eq_zpow_smul J u hsmul hper, ← Function.iterate_add_apply,
        Nat.mod_add_div]
    rw [h, smul_smul, ← zpow_add]
  let C : Set (Submodule 𝒪[F] (ι → F)) := {M | ∃ (k : ℤ) (l : ℕ), M = u ^ k • J^[l] B}
  have hmemC : ∀ (k : ℤ) (l : ℕ), u ^ k • J^[l] B ∈ C := fun k l => ⟨k, l, rfl⟩
  have hCsw : ∀ M ∈ C, ∃ p, 𝓛.IsSandwiched p M := by
    rintro M ⟨k, l, rfl⟩
    obtain ⟨p, hp⟩ := hswI l
    exact ⟨_, hp.zpow_smul hϖ k⟩
  -- Any two members of `C` are comparable.
  have hcmp : ∀ (k₁ k₂ : ℤ) (l d : ℕ), u ^ k₁ • J^[l] B ≤ u ^ k₂ • J^[l + d] B ∨
      u ^ k₂ • J^[l + d] B ≤ u ^ k₁ • J^[l] B := by
    intro k₁ k₂ l d
    rw [Function.iterate_add_apply, ← hsmulI, ← hsmulI]
    obtain ⟨p, hp⟩ := hswI d
    have hB' : u ^ k₁ • B = 𝓛.lattice (q + 𝓛.period * k₁) :=
      (lattice_add_period_mul hϖ 𝓛 q k₁).symm
    rw [hB']
    rcases (hp.zpow_smul hϖ k₂).le_or_le (q + 𝓛.period * k₁) with h | h
    · exact Or.inr ((hmono.iterate l) h)
    · exact Or.inl ((hmono.iterate l) h)
  have hchain : IsChain (· ≤ ·) C := by
    rintro M₁ ⟨k₁, l₁, rfl⟩ M₂ ⟨k₂, l₂, rfl⟩ -
    rcases le_total l₁ l₂ with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      exact hcmp k₁ k₂ l₁ d
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      exact (hcmp k₂ k₁ l₂ d).symm
  have hCsmul : ∀ M ∈ C, ∀ k : ℤ, u ^ k • M ∈ C := by
    rintro M ⟨k', l, rfl⟩ k
    rw [smul_smul, ← zpow_add]
    exact hmemC _ _
  have hClt : ∀ M ∈ C, u • M < M := fun M hM => by
    obtain ⟨p, hp⟩ := hCsw M hM
    exact hp.uniformizer_smul_lt hϖ
  choose pr hpr using hswI
  have he : (1 : ℤ) ≤ 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hfin : ∀ L ∈ C, ∀ L' ∈ C, {M | M ∈ C ∧ L' ≤ M ∧ M ≤ L}.Finite := by
    intro L hL L' hL'
    obtain ⟨P, hP⟩ := hCsw L hL
    obtain ⟨P', hP'⟩ := hCsw L' hL'
    refine ((Set.finite_Iio a).biUnion (fun r _ =>
      (Set.finite_Icc (-|P - pr r|) (|P' - pr r|)).image (fun k => u ^ k • J^[r] B))).subset ?_
    rintro M ⟨⟨k, l, rfl⟩, hM₁, hM₂⟩
    rw [hred] at hM₁ hM₂ ⊢
    have hsw' := (hpr (l % a)).zpow_smul hϖ (k + m * ((l / a : ℕ) : ℤ))
    have h1 := hP'.le_of_le hsw' hM₁
    have h2 := hsw'.le_of_le hP hM₂
    refine Set.mem_biUnion (Set.mem_Iio.2 (Nat.mod_lt _ (by omega))) ⟨_, ⟨?_, ?_⟩, rfl⟩
    · have h3 := neg_abs_le (P - pr (l % a))
      rcases le_or_gt 0 (k + m * ((l / a : ℕ) : ℤ)) with hk | hk
      · have := abs_nonneg (P - pr (l % a))
        linarith
      · have := mul_le_mul_of_nonpos_right he hk.le
        linarith
    · have h3 := le_abs_self (P' - pr (l % a))
      rcases le_or_gt (k + m * ((l / a : ℕ) : ℤ)) 0 with hk | hk
      · have := abs_nonneg (P' - pr (l % a))
        linarith
      · have := mul_le_mul_of_nonneg_right he hk.le
        linarith
  obtain ⟨𝓜, h𝓜⟩ := exists_latticeChain_range_eq hϖ C
    (fun M hM => (hCsw M hM).choose_spec.isLattice) hchain ⟨B, 0, 0, by simp⟩ hCsmul hClt hfin
  have hmemM : ∀ t, 𝓜.lattice t ∈ C := fun t => h𝓜 ▸ Set.mem_range_self t
  have hrangeM : ∀ M ∈ C, ∃ t, 𝓜.lattice t = M := fun M hM => by
    rw [← h𝓜] at hM
    exact hM
  -- `J` maps `C` to itself, bijectively and strictly monotonically, and `J^a = ϖ^m` on `C`.
  have hJC : ∀ M ∈ C, J M ∈ C := by
    rintro M ⟨k, l, rfl⟩
    rw [hsmul, ← Function.iterate_succ_apply' J l B]
    exact hmemC _ _
  have hJa : ∀ M ∈ C, J^[a] M = u ^ m • M := by
    rintro M ⟨k, l, rfl⟩
    have h1 : J^[a] (J^[l] B) = J^[l] (J^[a] B) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]
    rw [hsmulI, h1, hper, hsmulI, smul_smul, smul_smul, mul_comm]
  have hJsurj : ∀ M ∈ C, ∃ M' ∈ C, J M' = M := by
    rintro M ⟨k, l, rfl⟩
    refine ⟨u ^ (k - m) • J^[l + (a - 1)] B, hmemC _ _, ?_⟩
    have h2 : J (J^[l + (a - 1)] B) = J^[l] (J^[a] B) := by
      rw [← Function.iterate_succ_apply' J, ← Function.iterate_add_apply]
      congr 1
      omega
    rw [hsmul, h2, hper, hsmulI, smul_smul, ← zpow_add, sub_add_cancel]
  have hJlt : ∀ M ∈ C, ∀ M' ∈ C, M < M' → J M < J M' := by
    intro M hM M' hM' hlt
    refine lt_of_le_of_ne (hmono hlt.le) (fun heq => hlt.ne ?_)
    have h3 : J^[a] M = J^[a] M' := by
      obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [hb, Function.iterate_succ_apply, Function.iterate_succ_apply, heq]
    rw [hJa M hM, hJa M' hM'] at h3
    exact (smul_left_cancel_iff _).1 h3
  obtain ⟨c, hc⟩ := exists_shift_of_strictMono (β := (Submodule 𝒪[F] (ι → F))ᵒᵈ)
    (f := fun t => OrderDual.toDual (𝓜.lattice t))
    (fun t s h => OrderDual.toDual_lt_toDual.2 (𝓜.strictAnti h))
    (fun M => OrderDual.toDual (J (OrderDual.ofDual M)))
    (fun t => by
      obtain ⟨s, hs⟩ := hrangeM _ (hJC _ (hmemM t))
      exact ⟨s, by rw [hs]; rfl⟩)
    (fun t s h => OrderDual.toDual_lt_toDual.2
      (hJlt _ (hmemM s) _ (hmemM t) (𝓜.strictAnti h)))
    (fun s => by
      obtain ⟨M', hM', hJM'⟩ := hJsurj _ (hmemM s)
      obtain ⟨t, ht⟩ := hrangeM M' hM'
      refine ⟨t, ?_⟩
      show OrderDual.toDual (J (𝓜.lattice t)) = OrderDual.toDual (𝓜.lattice s)
      rw [ht, hJM'])
  have hc' : ∀ t, 𝓜.lattice (t + c) = J (𝓜.lattice t) :=
    fun t => OrderDual.toDual.injective (hc t)
  have hit : ∀ s : ℕ, ∀ t, 𝓜.lattice (t + s * c) = J^[s] (𝓜.lattice t) := by
    intro s
    induction s with
    | zero => intro t; simp
    | succ s ih =>
      intro t
      rw [Function.iterate_succ_apply', ← ih, ← hc']
      congr 1
      push_cast
      ring
  have h4 : 𝓜.lattice (0 + a * c) = 𝓜.lattice (0 + 𝓜.period * m) := by
    rw [hit, hJa _ (hmemM 0), lattice_add_period_mul hϖ 𝓜]
  have h5 := 𝓜.injective h4
  exact ⟨𝓜, c, hc', by linarith, fun t => hCsw _ (hmemM t)⟩

end LatticeChain

end Sandwich

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι]

namespace LatticeChain

/-- **Bushnell 1987, Theorem 1** (BK93 (2.3.1)), as `exists_latticeChain_of_pow_mem`, with every
lattice of the new chain sandwiched between consecutive lattices of the original chain. -/
theorem exists_latticeChain_of_pow_mem_sandwiched (𝓛 : LatticeChain 𝒪[F] F (ι → F)) {j : ℤ}
    {x y : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration j) {n : ℕ}
    (hn : y ^ n ∈ 𝓛.endFiltration (n * j + 1))
    (hxy : y - x ∈ 𝓛.endFiltration (j + 1)) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F (ι → F)) (j' : ℤ),
      (∀ z, z - x ∈ 𝓛.endFiltration (j + 1) → z ∈ 𝓜.endFiltration j') ∧
        j * 𝓜.period < j' * 𝓛.period ∧ ∀ t, ∃ p, 𝓛.IsSandwiched p (𝓜.lattice t) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨q, a, m, ha, hper⟩ := exists_iterate_cosetImage_eq_smul hϖ hx hxy hn
  obtain ⟨𝓜, c, hc, hac, hsw𝓜⟩ := exists_latticeChain_shift_sandwiched hϖ (𝓛.cosetImage j x) cosetImage_mono
    (fun k M => cosetImage_units_smul _ M) (fun p M h => h.exists_cosetImage hx) ha hper
  refine ⟨𝓜, c, fun z hz => ?_, ?_, hsw𝓜⟩
  · intro t v hv
    rw [hc]
    exact apply_mem_cosetImage hz hv
  · have hbound : ∀ s : ℕ, (𝓛.cosetImage j x)^[n * s] (𝓛.lattice q) ≤
        𝓛.lattice (q + s * (n * j + 1)) := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        rw [mul_add_one, add_comm (n * s) n, Function.iterate_add_apply]
        have := iterate_cosetImage_le_of_pow_mem hx hxy hn ih
        convert this using 2
        push_cast
        ring
    have h1 := hbound a
    rw [mul_comm n a, iterate_mul_eq_zpow_smul _ _ (fun k M => cosetImage_units_smul _ M) hper,
      ← lattice_add_period_mul hϖ] at h1
    have h2 := 𝓛.strictAnti.le_iff_ge.1 h1
    have he : (0 : ℤ) < 𝓜.period := by exact_mod_cast 𝓜.period_pos
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have h3 : (a : ℤ) * j < 𝓛.period * m := by
      by_contra h
      have h' : (𝓛.period : ℤ) * m ≤ a * j := not_lt.1 h
      have : (n : ℤ) * (𝓛.period * m) ≤ n * (a * j) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
      nlinarith
    have h4 : (a : ℤ) * (j * 𝓜.period) < a * (c * 𝓛.period) := by
      rw [show (a : ℤ) * (j * 𝓜.period) = 𝓜.period * (a * j) by ring,
        show (a : ℤ) * (c * 𝓛.period) = 𝓛.period * (a * c) by ring, hac]
      have := mul_lt_mul_of_pos_left h3 he
      linarith
    exact lt_of_mul_lt_mul_left h4 (by positivity)

/-- **Bushnell 1987, Theorem 1** (BK93 (2.3.1)) for a coset containing a nilpotent element, with
every lattice of the new chain sandwiched between consecutive lattices of the original chain. -/
theorem exists_latticeChain_of_isNilpotent_sandwiched (𝓛 : LatticeChain 𝒪[F] F (ι → F))
    {j : ℤ} {x y : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration j) (hy : IsNilpotent y)
    (hxy : y - x ∈ 𝓛.endFiltration (j + 1)) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F (ι → F)) (j' : ℤ),
      (∀ z, z - x ∈ 𝓛.endFiltration (j + 1) → z ∈ 𝓜.endFiltration j') ∧
        j * 𝓜.period < j' * 𝓛.period ∧ ∀ t, ∃ p, 𝓛.IsSandwiched p (𝓜.lattice t) := by
  obtain ⟨n, hn⟩ := hy
  exact 𝓛.exists_latticeChain_of_pow_mem_sandwiched hx (n := n)
    (by rw [hn]; exact zero_mem _) hxy

end LatticeChain

end Main

end Langlands.BushnellKutzko
