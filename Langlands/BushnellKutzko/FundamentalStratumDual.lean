import Langlands.BushnellKutzko.FiltrationCoordinates

/-! # Strata that are trivial on a smaller filtration step are not fundamental

Let `𝓛, 𝓛''` be `𝔬_F`-lattice chains in `F^ι` with periods `e, e''` and let `m, m''` be integers
with `m'' / e'' < m / e`. Let `b ∈ 𝔓^{-m}(𝓛)` and let `ψ` be an additive character of `F`
that is nontrivial on `𝔬_F`. If `ψ(tr(b x)) = 1` for every `x ∈ 𝔓^m(𝓛) ∩ 𝔓^{m''+1}(𝓛'')`,
then the coset `b + 𝔓^{1-m}(𝓛)` contains a nilpotent element
(`LatticeChain.exists_isNilpotent_add`).

The proof uses a basis `β` splitting both chains (`LatticeChain.exists_basis_splits_both`)
and the elementary endomorphisms `E_{kl}(t) : v ↦ t β^*_l(v) β_k`. An entry `b_{lk}` of `b`
whose term `E_{lk}(b_{lk})` is not in `𝔓^{1-m}(𝓛)` is tested against `E_{kl}(s / b_{lk})`; this
shows that `w(k) = e'' ν(β_k) - e ν''(β_k)` satisfies `w(l) < w(k)`. Hence the sum of these
terms strictly lowers `w` and is nilpotent, and the remaining terms lie in `𝔓^{1-m}(𝓛)`.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u

/-! ### Endomorphisms lowering a weight are nilpotent -/

section Nilpotent

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- An endomorphism that maps each basis vector `β_k` into the span of the `β_l` with
`w(l) < w(k)` is nilpotent. -/
theorem isNilpotent_of_lt_weight {κ : Type*} [Finite κ] (β : Module.Basis κ F V) (w : κ → ℤ)
    (z : Module.End F V) (hz : ∀ k, z (β k) ∈ Submodule.span F (β '' {l | w l < w k})) :
    IsNilpotent z := by
  have key : ∀ n : ℕ, ∀ k, (z ^ n) (β k) ∈ Submodule.span F (β '' {l | w l + n ≤ w k}) := by
    intro n
    induction n with
    | zero =>
      intro k
      exact Submodule.subset_span ⟨k, by simp, rfl⟩
    | succ n ih =>
      intro k
      rw [pow_succ', Module.End.mul_apply]
      have hle : Submodule.span F (β '' {l | w l + n ≤ w k}) ≤
          (Submodule.span F (β '' {l | w l + ((n + 1 : ℕ) : ℤ) ≤ w k})).comap z := by
        rw [Submodule.span_le]
        rintro _ ⟨l, hl, rfl⟩
        refine Submodule.span_mono (Set.image_mono ?_) (hz l)
        intro l' hl'
        simp only [Set.mem_ofPred_eq] at hl hl' ⊢
        push_cast
        omega
      exact hle (ih k)
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine ⟨1, ?_⟩
    rw [pow_one]
    exact β.ext fun k => isEmptyElim k
  obtain ⟨kmax, hmax⟩ := Finite.exists_max w
  obtain ⟨kmin, hmin⟩ := Finite.exists_min w
  refine ⟨(w kmax - w kmin).toNat + 1, β.ext fun k => ?_⟩
  have h := key ((w kmax - w kmin).toNat + 1) k
  have hempty : {l | w l + (((w kmax - w kmin).toNat + 1 : ℕ) : ℤ) ≤ w k} = ∅ := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have := hmax k
    have := hmin l
    have := Int.self_le_toNat (w kmax - w kmin)
    push_cast
    omega
  rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at h
  rw [h, LinearMap.zero_apply]

end Nilpotent

/-! ### The main lemma -/

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*} [Fintype ι]

namespace LatticeChain

include hϖ in
/-- Let `m'' e < m e''`, `b ∈ 𝔓^{-m}(𝓛)`, and `ψ` an additive character with `ψ(s) ≠ 1` for
some `s ∈ 𝔬_F`. If `ψ(tr(b x)) = 1` for all `x ∈ 𝔓^m(𝓛) ∩ 𝔓^{m''+1}(𝓛'')`, then
`b + y` is nilpotent for some `y ∈ 𝔓^{1-m}(𝓛)`. -/
theorem exists_isNilpotent_add (𝓛 𝓛'' : LatticeChain 𝒪[F] F (ι → F)) {m m'' : ℤ}
    (hlt : m'' * 𝓛.period < m * 𝓛''.period) {b : Module.End F (ι → F)}
    (hb : b ∈ 𝓛.endFiltration (-m)) (ψ : AddChar F ℂ) {s : F} (hs : s ∈ 𝒪[F])
    (hψs : ψ s ≠ 1)
    (htr : ∀ x ∈ 𝓛.endFiltration m, x ∈ 𝓛''.endFiltration (m'' + 1) →
      ψ (LinearMap.trace F (ι → F) (b * x)) = 1) :
    ∃ y ∈ 𝓛.endFiltration (1 - m), IsNilpotent (b + y) := by
  classical
  obtain ⟨r, β, hβ, hβ''⟩ := 𝓛.exists_basis_splits_both hϖ 𝓛''
  have he : (0 : ℤ) < 𝓛.period := Int.natCast_pos.mpr 𝓛.period_pos
  have he'' : (0 : ℤ) < 𝓛''.period := Int.natCast_pos.mpr 𝓛''.period_pos
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hψs (AddChar.map_zero_eq_one ψ)
  have hords : 0 ≤ ordOf hϖ s := ordOf_nonneg hϖ hs0 hs
  let w : Fin r → ℤ := fun k =>
    (𝓛''.period : ℤ) * 𝓛.index hϖ (β k) - (𝓛.period : ℤ) * 𝓛''.index hϖ (β k)
  let bad : Fin r → Fin r → Prop := fun l k =>
    elementaryEnd β l k (entry β b l k) ∉ 𝓛.endFiltration (1 - m)
  -- the key inequality for a bad entry
  have hbad : ∀ l k, bad l k → w l < w k := by
    intro l k hlk
    have hblk : entry β b l k ≠ 0 := by
      intro h0
      apply hlk
      rw [h0, elementaryEnd_zero]
      exact zero_mem _
    have h1 := 𝓛.le_of_mem_endFiltration hϖ hβ hb l k hblk
    have h2 : ¬ (1 - m + 𝓛.index hϖ (β k) ≤
        (𝓛.period : ℤ) * ordOf hϖ (entry β b l k) + 𝓛.index hϖ (β l)) := by
      rw [← 𝓛.elementaryEnd_mem_iff hϖ hβ l k hblk]
      exact hlk
    have hc' : (𝓛.period : ℤ) * ordOf hϖ (entry β b l k) =
        𝓛.index hϖ (β k) - 𝓛.index hϖ (β l) - m := by omega
    have ht0 : s * (entry β b l k)⁻¹ ≠ 0 := mul_ne_zero hs0 (inv_ne_zero hblk)
    have hordt : ordOf hϖ (s * (entry β b l k)⁻¹) = ordOf hϖ s - ordOf hϖ (entry β b l k) := by
      rw [ordOf_mul hϖ hs0 (inv_ne_zero hblk), ordOf_inv hϖ hblk]
      ring
    have hx : elementaryEnd β k l (s * (entry β b l k)⁻¹) ∈ 𝓛.endFiltration m := by
      rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l ht0, hordt, mul_sub]
      have : 0 ≤ (𝓛.period : ℤ) * ordOf hϖ s := mul_nonneg he.le hords
      omega
    have htrace : LinearMap.trace F (ι → F) (b * elementaryEnd β k l (s * (entry β b l k)⁻¹)) =
        s := by
      rw [trace_mul_elementaryEnd, mul_assoc, inv_mul_cancel₀ hblk, mul_one]
    have hx'' : elementaryEnd β k l (s * (entry β b l k)⁻¹) ∉ 𝓛''.endFiltration (m'' + 1) := by
      intro hx''
      apply hψs
      rw [← htrace]
      exact htr _ hx hx''
    rw [𝓛''.elementaryEnd_mem_iff hϖ hβ'' k l ht0, hordt, mul_sub] at hx''
    have h3 : (𝓛''.period : ℤ) * ordOf hϖ (entry β b l k) ≥
        𝓛''.index hϖ (β k) - 𝓛''.index hϖ (β l) - m'' := by
      have : 0 ≤ (𝓛''.period : ℤ) * ordOf hϖ s := mul_nonneg he''.le hords
      omega
    have h4 : (𝓛''.period : ℤ) * ((𝓛.period : ℤ) * ordOf hϖ (entry β b l k)) =
        (𝓛''.period : ℤ) * (𝓛.index hϖ (β k) - 𝓛.index hϖ (β l) - m) := by
      rw [hc']
    have h5 : (𝓛.period : ℤ) * ((𝓛''.period : ℤ) * ordOf hϖ (entry β b l k)) ≥
        (𝓛.period : ℤ) * (𝓛''.index hϖ (β k) - 𝓛''.index hϖ (β l) - m'') :=
      mul_le_mul_of_nonneg_left h3 he.le
    show (𝓛''.period : ℤ) * 𝓛.index hϖ (β l) - (𝓛.period : ℤ) * 𝓛''.index hϖ (β l) <
      (𝓛''.period : ℤ) * 𝓛.index hϖ (β k) - (𝓛.period : ℤ) * 𝓛''.index hϖ (β k)
    nlinarith
  -- the decomposition `b = z + g`
  let z : Module.End F (ι → F) :=
    ∑ l, ∑ k, if bad l k then elementaryEnd β l k (entry β b l k) else 0
  let g : Module.End F (ι → F) :=
    ∑ l, ∑ k, if bad l k then 0 else elementaryEnd β l k (entry β b l k)
  have hbzg : b = z + g := by
    conv_lhs => rw [← sum_elementaryEnd_entry β b]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  refine ⟨-g, neg_mem (sum_mem fun l _ => sum_mem fun k _ => ?_), ?_⟩
  · split_ifs with h
    · exact zero_mem _
    · exact not_not.1 h
  · rw [hbzg, add_neg_cancel_right]
    apply isNilpotent_of_lt_weight β w
    intro j
    simp only [z, LinearMap.sum_apply]
    refine sum_mem fun l _ => sum_mem fun k _ => ?_
    split_ifs with hlk
    · rw [elementaryEnd_apply_basis]
      split_ifs with hkj
      · subst hkj
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hbad l k hlk, rfl⟩)
      · exact zero_mem _
    · rw [LinearMap.zero_apply]
      exact zero_mem _

end LatticeChain

end Main

end Langlands.BushnellKutzko
