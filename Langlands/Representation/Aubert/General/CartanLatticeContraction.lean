import Langlands.Representation.Aubert.General.JacquetCartanAssembly

/-!
# Wall contraction from a lattice model of the Cartan elements

`IsCartanLatticeModel` abstracts the shape of the Cartan elements of the standard
Levi subgroups `M_I` of a reductive group over a nonarchimedean local field: each
Cartan element of `M_I` is `ϖ^x f` with `x` in a cocharacter lattice `X`, `f` in a
fixed finite set `F₀`, and the pairings `⟨β, x⟩` with the simple roots `β ∈ I`
bounded below; cocharacters orthogonal to `I` give central elements of `M_I`;
standard cocharacters of `I` exist; and the cocharacters in the open chamber of
`J` contract each element of `N_J` into every neighbourhood of `1`.

`IsCartanLatticeModel.hasWallContraction` derives the wall contraction dichotomy
`HasWallContraction` for every `I` (proof of Renard VI.2.1 `a) ⇒ b)`). A gap
argument chooses thresholds `T 0 < T 1 < ⋯ < T |I|` and an index `k` such that no
pairing `⟨β, x⟩`, `β ∈ I`, lies in `[T k, T (k+1))`; the wall is
`J = {β ∈ I | ⟨β, x⟩ < T k}`. If `J = I` the element is a member of a finite set
times a central element; otherwise its `J`-pairings are bounded, so up to finitely
many lattice translates it is orthogonal to `J`, and after a central shift along a
standard cocharacter of `I` it lies deep in the open chamber of `J`.
-/

noncomputable section

open Filter Topology

namespace Langlands.Aubert.General

universe uG uΔ uX

variable {G : Type uG} [Group G] {Δ : Type uΔ} {X : Type uX} [AddCommGroup X]

/-- **Lattice models of Cartan elements.** The Cartan elements of `M_I` are
`e x * f` with `x` in the lattice `X`, `f` in the finite set `F₀`, and
`⟨β, x⟩ ≥ -B` for `β ∈ I`; `e x` and `F₀` lie in every `M_I`, and `e x` is central
in `M_I` when `x` is orthogonal to `I`; every `I` has a standard cocharacter `ζ`
(orthogonal to `I`, positive on the other simple roots); and for each `u ∈ N_J`
and neighbourhood `O` of `1`, `e y * u * (e y)⁻¹ ∈ O` for all `y` orthogonal to `J`
with large pairings with the simple roots outside `J` (Renard V.5.2 (iii)). -/
structure IsCartanLatticeModel [TopologicalSpace G]
    (levi unipotent : Finset Δ → Subgroup G) (cartanSet : Finset Δ → Set G)
    (e : Multiplicative X →* G) (pair : Δ → X →+ ℤ) (F₀ : Set G) : Prop where
  finite_F₀ : F₀.Finite
  exists_rep : ∀ I, ∃ B : ℤ, ∀ t ∈ cartanSet I, ∃ x : X, ∃ f ∈ F₀,
    t = e (.ofAdd x) * f ∧ ∀ β ∈ I, -B ≤ pair β x
  e_mem_levi : ∀ I (x : X), e (.ofAdd x) ∈ levi I
  F₀_subset_levi : ∀ I, F₀ ⊆ levi I
  levi_le_normalizer : ∀ I, levi I ≤ Subgroup.normalizer (unipotent I : Set G)
  commute_of_pair_eq_zero : ∀ I (x : X), (∀ β ∈ I, pair β x = 0) →
    ∀ m ∈ levi I, m * e (.ofAdd x) = e (.ofAdd x) * m
  exists_standard : ∀ I : Finset Δ, ∃ ζ : X, (∀ β ∈ I, pair β ζ = 0) ∧ ∀ β ∉ I, 0 < pair β ζ
  contracts : ∀ J, ∀ u ∈ unipotent J, ∀ O ∈ 𝓝 (1 : G), ∃ L : ℤ, ∀ y : X,
    (∀ β ∈ J, pair β y = 0) → (∀ β ∉ J, L ≤ pair β y) →
      e (.ofAdd y) * u * (e (.ofAdd y))⁻¹ ∈ O

/-- Lattice elements with bounded pairings on a finite set `J` are orthogonal to
`J` up to finitely many translates. -/
theorem exists_finite_pairing_reps (pair : Δ → X →+ ℤ) (J : Finset Δ) (lo hi : ℤ) :
    ∃ R : Set X, R.Finite ∧ ∀ x : X, (∀ β ∈ J, lo ≤ pair β x ∧ pair β x ≤ hi) →
      ∃ r ∈ R, ∀ β ∈ J, pair β (x - r) = 0 := by
  let φ : X → (J → ℤ) := fun x β => pair β x
  let s : Set X := {x | ∀ β ∈ J, lo ≤ pair β x ∧ pair β x ≤ hi}
  have hbox : (φ '' s).Finite := by
    refine (Set.Finite.pi (t := fun _ : J => Set.Icc lo hi)
      fun _ => Set.finite_Icc lo hi).subset ?_
    rintro _ ⟨x, hx, rfl⟩ β -
    exact hx β β.2
  refine ⟨Function.invFunOn φ s '' (φ '' s), hbox.image _, fun x hx => ?_⟩
  refine ⟨Function.invFunOn φ s (φ x), ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩, fun β hβ => ?_⟩
  have h := congrFun (Function.invFunOn_eq (f := φ) (s := s) ⟨x, hx, rfl⟩) ⟨β, hβ⟩
  rw [map_sub, sub_eq_zero]
  exact h.symm

namespace IsCartanLatticeModel

variable [TopologicalSpace G] {levi unipotent : Finset Δ → Subgroup G}
  {cartanSet : Finset Δ → Set G} {e : Multiplicative X →* G} {pair : Δ → X →+ ℤ}
  {F₀ : Set G}

/-- Cocharacters orthogonal to `I` may be added without changing conjugation of
elements of `M_I`. -/
theorem conj_add_of_pair_eq_zero
    (hM : IsCartanLatticeModel levi unipotent cartanSet e pair F₀) {I : Finset Δ}
    {z : X} (hz : ∀ β ∈ I, pair β z = 0) {u : G} (hu : u ∈ levi I) (y : X) :
    e (.ofAdd (y + z)) * u * (e (.ofAdd (y + z)))⁻¹ =
      e (.ofAdd y) * u * (e (.ofAdd y))⁻¹ := by
  have hc := hM.commute_of_pair_eq_zero I z hz u hu
  rw [ofAdd_add, map_mul]
  calc e (.ofAdd y) * e (.ofAdd z) * u * (e (.ofAdd y) * e (.ofAdd z))⁻¹
      = e (.ofAdd y) * (u * e (.ofAdd z)) * (e (.ofAdd z))⁻¹ * (e (.ofAdd y))⁻¹ := by
        rw [hc]; group
    _ = e (.ofAdd y) * u * (e (.ofAdd y))⁻¹ := by group

/-- **The step of the gap argument.** For every bound `T` on the pairings with a
wall `J ⊊ I`, every large enough `T'` bounding the pairings with `I \ J` from
below forces the contraction of the given elements of the wall. -/
theorem eventually_wall_contraction [IsTopologicalGroup G] [Fintype Δ]
    (hM : IsCartanLatticeModel levi unipotent cartanSet e pair F₀) (I : Finset Δ)
    {O : Set G} (hO : O ∈ 𝓝 (1 : G)) (S : {J : Finset Δ // J ⊂ I} → Finset G)
    (hS : ∀ J, (S J : Set G) ⊆ unipotent J.1 ⊓ levi I) (B T : ℤ) :
    ∀ᶠ T' in atTop, ∀ J : {J : Finset Δ // J ⊂ I}, ∀ x : X,
      (∀ β ∈ J.1, -B ≤ pair β x ∧ pair β x ≤ T) → (∀ β ∈ I, β ∉ J.1 → T' ≤ pair β x) →
      ∀ f ∈ F₀, ∀ u ∈ S J, e (.ofAdd x) * f * u * (e (.ofAdd x) * f)⁻¹ ∈ O := by
  classical
  refine Filter.eventually_all.mpr fun J => ?_
  obtain ⟨R, hR, hrep⟩ := exists_finite_pairing_reps pair J.1 (-B) T
  -- the neighbourhood of `1` absorbing conjugation by the translates `e r`
  let O' : Set G := ⋂ r ∈ R, (fun g => e (.ofAdd r) * g * (e (.ofAdd r))⁻¹) ⁻¹' O
  have hO' : O' ∈ 𝓝 (1 : G) := by
    refine (Filter.biInter_mem hR).mpr fun r _ => ?_
    refine ContinuousAt.preimage_mem_nhds ?_ (by simpa using hO)
    exact ((continuous_const.mul continuous_id).mul continuous_const).continuousAt
  -- the finitely many conjugates `f * u * f⁻¹` of wall elements
  let U : Set G := (fun p : G × G => p.1 * p.2 * p.1⁻¹) '' (F₀ ×ˢ (S J : Set G))
  have hU : U.Finite := (hM.finite_F₀.prod (S J).finite_toSet).image _
  have hUJ : ∀ u ∈ U, u ∈ unipotent J.1 ⊓ levi I := by
    rintro _ ⟨⟨f, u⟩, ⟨hf, hu⟩, rfl⟩
    have hu' := hS J hu
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (hM.levi_le_normalizer J.1 (hM.F₀_subset_levi J.1 hf)) u).mp hu'.1
    · have hfI := hM.F₀_subset_levi I hf
      exact (levi I).mul_mem ((levi I).mul_mem hfI hu'.2) ((levi I).inv_mem hfI)
  have hL : ∀ᶠ L in atTop, ∀ u ∈ U, ∀ y : X, (∀ β ∈ J.1, pair β y = 0) →
      (∀ β ∉ J.1, L ≤ pair β y) → e (.ofAdd y) * u * (e (.ofAdd y))⁻¹ ∈ O' := by
    refine (Filter.eventually_all_finite hU).mpr fun u hu => ?_
    obtain ⟨L₀, hL₀⟩ := hM.contracts J.1 u (hUJ u hu).1 O' hO'
    exact eventually_atTop.mpr ⟨L₀, fun L hL y hy hy' =>
      hL₀ y hy fun β hβ => hL.trans (hy' β hβ)⟩
  obtain ⟨L, hL⟩ := hL.exists
  have hbound : ∀ᶠ T' in atTop, ∀ r ∈ R, ∀ β : Δ, L + pair β r ≤ T' :=
    (Filter.eventually_all_finite hR).mpr fun r _ =>
      Filter.eventually_all.mpr fun β => eventually_ge_atTop _
  filter_upwards [hbound] with T' hT' x hxJ hxI f hf u hu
  obtain ⟨r, hr, hxr⟩ := hrep x hxJ
  obtain ⟨ζ, hζI, hζpos⟩ := hM.exists_standard I
  set y := x - r with hy
  let m : ℕ := ∑ β, (L - pair β y).toNat
  have hmζ : ∀ β ∈ I, pair β (m • ζ) = 0 := fun β hβ => by
    rw [map_nsmul, hζI β hβ, smul_zero]
  have hy' : ∀ β ∈ J.1, pair β (y + m • ζ) = 0 := fun β hβ => by
    rw [map_add, hxr β hβ, hmζ β (J.2.subset hβ), add_zero]
  have hy'' : ∀ β ∉ J.1, L ≤ pair β (y + m • ζ) := by
    intro β hβ
    by_cases hβI : β ∈ I
    · rw [map_add, hmζ β hβI, add_zero, hy, map_sub]
      linarith [hxI β hβI hβ, hT' r hr β]
    · have hle : (L - pair β y).toNat ≤ m :=
        Finset.single_le_sum (f := fun β => (L - pair β y).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ β)
      have h1 : L - pair β y ≤ (m : ℤ) :=
        (Int.self_le_toNat _).trans (by exact_mod_cast hle)
      have h2 : (m : ℤ) ≤ (m : ℤ) * pair β ζ :=
        le_mul_of_one_le_right (Int.natCast_nonneg m) (hζpos β hβI)
      rw [map_add, map_nsmul, nsmul_eq_mul]
      linarith
  have hu' : f * u * f⁻¹ ∈ U := ⟨(f, u), ⟨hf, hu⟩, rfl⟩
  have hmem := hL (f * u * f⁻¹) hu' (y + m • ζ) hy' hy''
  rw [hM.conj_add_of_pair_eq_zero hmζ (hUJ _ hu').2] at hmem
  have hO_r := Set.mem_iInter₂.mp hmem r hr
  have hx : e (.ofAdd x) = e (.ofAdd r) * e (.ofAdd y) := by
    rw [← map_mul, ← ofAdd_add, hy, add_sub_cancel]
  simp only [Set.mem_preimage] at hO_r
  rw [hx]
  convert hO_r using 1
  group

/-- **Wall contraction from a lattice model** (proof of Renard VI.2.1
`a) ⇒ b)`). -/
theorem hasWallContraction [IsTopologicalGroup G] [Fintype Δ]
    (hM : IsCartanLatticeModel levi unipotent cartanSet e pair F₀) (I : Finset Δ) :
    HasWallContraction levi unipotent cartanSet I := by
  classical
  intro O hO S hS
  obtain ⟨B, hB⟩ := hM.exists_rep I
  have hstep : ∀ T : ℤ, ∃ T', T < T' ∧ ∀ J : {J : Finset Δ // J ⊂ I}, ∀ x : X,
      (∀ β ∈ J.1, -B ≤ pair β x ∧ pair β x ≤ T) → (∀ β ∈ I, β ∉ J.1 → T' ≤ pair β x) →
      ∀ f ∈ F₀, ∀ u ∈ S J, e (.ofAdd x) * f * u * (e (.ofAdd x) * f)⁻¹ ∈ O :=
    fun T => ((eventually_gt_atTop T).and
      (hM.eventually_wall_contraction I hO S hS B T)).exists
  choose next hnext_gt hnext using hstep
  -- the thresholds `T 0 < T 1 < ⋯`
  let T : ℕ → ℤ := fun k => next^[k] (-B)
  have hTsucc : ∀ k, T (k + 1) = next (T k) := fun k =>
    Function.iterate_succ_apply' next k (-B)
  have hTmono : Monotone T := monotone_nat_of_le_succ fun k => by
    rw [hTsucc k]
    exact (hnext_gt (T k)).le
  obtain ⟨R, hR, hrep⟩ := exists_finite_pairing_reps pair I (-B) (T I.card)
  refine ⟨(fun p : X × G => e (.ofAdd p.1) * p.2) '' (R ×ˢ F₀),
    ((hR.prod hM.finite_F₀).image _).isCompact, fun t ht => ?_⟩
  obtain ⟨x, f, hf, rfl, hxB⟩ := hB t ht
  -- the gap argument
  let Jk : ℕ → Finset Δ := fun k => I.filter fun β => pair β x < T k
  have hJmono : ∀ k, Jk k ⊆ Jk (k + 1) := fun k β hβ => by
    simp only [Jk, Finset.mem_filter] at hβ ⊢
    exact ⟨hβ.1, hβ.2.trans_le (hTmono (Nat.le_succ k))⟩
  obtain ⟨k, hk, hsub⟩ : ∃ k ≤ I.card, Jk (k + 1) ⊆ Jk k := by
    by_contra hcon
    push Not at hcon
    have hcard : ∀ k ≤ I.card + 1, k ≤ (Jk k).card := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hlt : (Jk k).card < (Jk (k + 1)).card :=
          Finset.card_lt_card ⟨hJmono k, hcon k (by omega)⟩
        have := ih (by omega)
        omega
    have h1 := hcard (I.card + 1) le_rfl
    have h2 : (Jk (I.card + 1)).card ≤ I.card := Finset.card_filter_le _ _
    omega
  by_cases hJI : Jk k = I
  · -- all pairings with `I` are bounded: a finite set times a central element
    left
    have hbd : ∀ β ∈ I, -B ≤ pair β x ∧ pair β x ≤ T I.card := fun β hβ => by
      have hβk : β ∈ Jk k := hJI.symm ▸ hβ
      simp only [Jk, Finset.mem_filter] at hβk
      exact ⟨hxB β hβ, (hβk.2.trans_le (hTmono hk)).le⟩
    obtain ⟨r, hr, hxr⟩ := hrep x hbd
    have hc := hM.commute_of_pair_eq_zero I (x - r) hxr f (hM.F₀_subset_levi I hf)
    refine ⟨e (.ofAdd r) * f, ⟨(r, f), ⟨hr, hf⟩, rfl⟩, e (.ofAdd (x - r)),
      hM.e_mem_levi I _, fun m hm => hM.commute_of_pair_eq_zero I _ hxr m hm, ?_⟩
    calc e (.ofAdd x) * f = e (.ofAdd r) * e (.ofAdd (x - r)) * f := by
          rw [← map_mul, ← ofAdd_add, add_sub_cancel]
      _ = e (.ofAdd r) * f * e (.ofAdd (x - r)) := by
          rw [mul_assoc, ← hc, mul_assoc]
  · -- the wall `J = {β ∈ I | ⟨β, x⟩ < T k}`
    right
    have hJssub : Jk k ⊂ I :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hJI⟩
    refine ⟨⟨Jk k, hJssub⟩, fun u hu => ?_⟩
    refine hnext (T k) ⟨Jk k, hJssub⟩ x (fun β hβ => ?_) (fun β hβI hβJ => ?_) f hf u hu
    · simp only [Jk, Finset.mem_filter] at hβ
      exact ⟨hxB β hβ.1, hβ.2.le⟩
    · have hβ' : β ∉ Jk (k + 1) := fun h => hβJ (hsub h)
      simp only [Jk, Finset.mem_filter, not_and, not_lt] at hβ'
      rw [← hTsucc k]
      exact hβ' hβI

end IsCartanLatticeModel

end Langlands.Aubert.General
