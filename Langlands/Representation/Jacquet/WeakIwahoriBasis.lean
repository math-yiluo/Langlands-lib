import Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract

/-! # Iwahori bases contracted strictly by one element and weakly by another

In a locally compact nonarchimedean group with unique `O * M * U` factorization
and an open product near the identity, let `g` and `a` be central elements of
`M`. If the powers of `g` contract `U` uniformly on compact sets (and those of
`g⁻¹` contract `O`), while conjugation by the nonnegative powers of `a` (resp.
`a⁻¹`) is equicontinuous at the identity on `U` (resp. `O`), then every identity
neighborhood contains a compact open subgroup with an Iwahori contraction for
`g` whose radical pieces are also stable under `a` and `a⁻¹`. -/

namespace Langlands.Jacquet

open Topology Filter

universe uΓ

variable {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]

/-- The conjugation conditions of an Iwahori contraction without exhaustion and
uniform contraction: `g` lies in `M` and conjugation by `g` maps `K ∩ N` into
itself, while conjugation by `g⁻¹` maps `K ∩ M` and `K ∩ Nbar` into themselves. -/
structure IsWeakIwahoriContraction (K : OpenSubgroup Γ) (N M Nbar : Subgroup Γ) (g : Γ) :
    Prop where
  /-- The weakly contracting element lies in `M`. -/
  mem_levi : g ∈ M
  /-- Conjugation by `g` maps `K ∩ N` into itself. -/
  upper : ∀ u ∈ K.toSubgroup ⊓ N, g * u * g⁻¹ ∈ K.toSubgroup ⊓ N
  /-- Conjugation by `g⁻¹` maps `K ∩ M` into itself. -/
  levi : ∀ m ∈ K.toSubgroup ⊓ M, g⁻¹ * m * g ∈ K.toSubgroup ⊓ M
  /-- Conjugation by `g⁻¹` maps `K ∩ Nbar` into itself. -/
  lower : ∀ l ∈ K.toSubgroup ⊓ Nbar, g⁻¹ * l * g ∈ K.toSubgroup ⊓ Nbar

/-- An Iwahori contraction is in particular a weak one. -/
theorem IsIwahoriContraction.isWeakIwahoriContraction {K : OpenSubgroup Γ}
    {N M Nbar : Subgroup Γ} {g : Γ} (h : IsIwahoriContraction K N M Nbar g) :
    IsWeakIwahoriContraction K N M Nbar g :=
  ⟨h.mem_levi, h.upper, h.levi, h.lower⟩

namespace IsWeakIwahoriContraction

variable {K : OpenSubgroup Γ} {N M Nbar : Subgroup Γ}

theorem one (h1 : (1 : Γ) ∈ M) : IsWeakIwahoriContraction K N M Nbar 1 :=
  ⟨h1, fun u hu => by simpa using hu, fun m hm => by simpa using hm,
    fun l hl => by simpa using hl⟩

/-- Weak contractions are closed under products. -/
theorem mul {g h : Γ} (hg : IsWeakIwahoriContraction K N M Nbar g)
    (hh : IsWeakIwahoriContraction K N M Nbar h) :
    IsWeakIwahoriContraction K N M Nbar (g * h) := by
  refine ⟨M.mul_mem hg.mem_levi hh.mem_levi, fun u hu => ?_, fun m hm => ?_,
    fun l hl => ?_⟩
  · have e : g * h * u * (g * h)⁻¹ = g * (h * u * h⁻¹) * g⁻¹ := by group
    rw [e]
    exact hg.upper _ (hh.upper u hu)
  · have e : (g * h)⁻¹ * m * (g * h) = h⁻¹ * (g⁻¹ * m * g) * h := by group
    rw [e]
    exact hh.levi _ (hg.levi m hm)
  · have e : (g * h)⁻¹ * l * (g * h) = h⁻¹ * (g⁻¹ * l * g) * h := by group
    rw [e]
    exact hh.lower _ (hg.lower l hl)

/-- Weak contractions are closed under natural powers. -/
theorem pow {g : Γ} (hg : IsWeakIwahoriContraction K N M Nbar g) (n : ℕ) :
    IsWeakIwahoriContraction K N M Nbar (g ^ n) := by
  induction n with
  | zero => simpa using one (K := K) (N := N) (Nbar := Nbar) M.one_mem
  | succ n ih => simpa [pow_succ] using ih.mul hg

end IsWeakIwahoriContraction

/-- Inside a compact open subgroup `V`, the elements of a closed subgroup `H`
whose conjugates by all products `a ^ i * h ^ j` stay in `V` form a compact
subgroup stable under conjugation by `h` and by `a`, normalized by `V ∩ M`, and
relatively open in `H`, provided the powers of `h` contract `H` uniformly on
compact sets and conjugation by the powers of `a` is equicontinuous at `1` on `H`. -/
theorem exists_stable_piece_of_weak [NonarchimedeanGroup Γ]
    (V : OpenSubgroup Γ) (hVc : IsCompact (V : Set Γ)) (H M : Subgroup Γ)
    (hH : IsClosed (H : Set Γ)) {h a : Γ} (hh : h ∈ M) (ha : a ∈ M)
    (hcomm : ∀ m ∈ M, m * h = h * m) (hcomma : ∀ m ∈ M, m * a = a * m)
    (hMH : M ≤ Subgroup.normalizer (H : Set Γ))
    (hcontr : ∀ C : Set Γ, IsCompact C → C ⊆ H → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, h ^ n * c * (h ^ n)⁻¹ ∈ W)
    (hweak : ∀ W ∈ 𝓝 (1 : Γ), ∃ W' ∈ 𝓝 (1 : Γ), ∀ i : ℕ, ∀ y ∈ H, y ∈ W' →
      a ^ i * y * (a ^ i)⁻¹ ∈ W) :
    ∃ P : Subgroup Γ, P ≤ H ∧ (P : Set Γ) ⊆ V ∧ IsCompact (P : Set Γ) ∧
      (∀ x ∈ P, h * x * h⁻¹ ∈ P) ∧ (∀ x ∈ P, a * x * a⁻¹ ∈ P) ∧
      (∀ b ∈ V.toSubgroup ⊓ M, ∀ x ∈ P, b * x * b⁻¹ ∈ P) ∧
      ∃ Y ∈ 𝓝 (1 : Γ), ∀ x ∈ H, x ∈ Y → x ∈ P := by
  have hah : Commute a h := hcomm a ha
  let P : Subgroup Γ :=
    H ⊓ ⨅ (i : ℕ) (j : ℕ), V.toSubgroup.comap (MulAut.conj (a ^ i * h ^ j)).toMonoidHom
  have hmem : ∀ x, x ∈ P ↔ x ∈ H ∧ ∀ i j : ℕ,
      (a ^ i * h ^ j) * x * (a ^ i * h ^ j)⁻¹ ∈ V := by
    intro x
    simp only [P, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, OpenSubgroup.mem_toSubgroup]
  have hPH : P ≤ H := fun x hx => ((hmem x).1 hx).1
  have hPV : (P : Set Γ) ⊆ V := fun x hx => by simpa using ((hmem x).1 hx).2 0 0
  have hset : (P : Set Γ) = (H : Set Γ) ∩
      ⋂ (i : ℕ) (j : ℕ), (fun x => (a ^ i * h ^ j) * x * (a ^ i * h ^ j)⁻¹) ⁻¹' (V : Set Γ) := by
    ext x
    rw [SetLike.mem_coe, hmem]
    simp
  have hPclosed : IsClosed (P : Set Γ) := by
    rw [hset]
    exact hH.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      V.isClosed.preimage (by fun_prop))
  refine ⟨P, hPH, hPV, hVc.of_isClosed_subset hPclosed hPV, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH hh) x).mp hxH, fun i j => ?_⟩
    have e : (a ^ i * h ^ j) * (h * x * h⁻¹) * (a ^ i * h ^ j)⁻¹ =
        (a ^ i * h ^ (j + 1)) * x * (a ^ i * h ^ (j + 1))⁻¹ := by
      rw [pow_succ]
      group
    rw [e]
    exact hxV i (j + 1)
  · intro x hx
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH ha) x).mp hxH, fun i j => ?_⟩
    have hcj : Commute (h ^ j) a := (hah.pow_right j).symm
    have e : (a ^ i * h ^ j) * (a * x * a⁻¹) * (a ^ i * h ^ j)⁻¹ =
        (a ^ (i + 1) * h ^ j) * x * (a ^ (i + 1) * h ^ j)⁻¹ := by
      calc (a ^ i * h ^ j) * (a * x * a⁻¹) * (a ^ i * h ^ j)⁻¹
          = a ^ i * (h ^ j * a) * x * (a⁻¹ * (h ^ j)⁻¹) * (a ^ i)⁻¹ := by group
        _ = a ^ i * (a * h ^ j) * x * ((h ^ j)⁻¹ * a⁻¹) * (a ^ i)⁻¹ := by
          rw [hcj.eq, ← mul_inv_rev, ← mul_inv_rev, hcj.eq]
        _ = (a ^ (i + 1) * h ^ j) * x * (a ^ (i + 1) * h ^ j)⁻¹ := by
          rw [pow_succ]
          group
    rw [e]
    exact hxV (i + 1) j
  · intro b hb x hx
    obtain ⟨hbV, hbM⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH hbM) x).mp hxH, fun i j => ?_⟩
    have hbij : Commute (a ^ i * h ^ j) b :=
      (Commute.mul_left (Commute.pow_left (hcomma b hbM).symm i)
        (Commute.pow_left (hcomm b hbM).symm j))
    rw [conj_conj_of_commute hbij]
    exact V.mul_mem (V.mul_mem hbV (hxV i j)) (V.inv_mem hbV)
  · obtain ⟨W', hW', hW'V⟩ := hweak (V : Set Γ) V.mem_nhds_one
    obtain ⟨V₁, hV₁⟩ := NonarchimedeanGroup.is_nonarchimedean _
      (Filter.inter_mem hW' V.mem_nhds_one)
    have hV₁c : IsCompact (V₁ : Set Γ) :=
      hVc.of_isClosed_subset V₁.isClosed (hV₁.trans Set.inter_subset_right)
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hcontr ((V₁ : Set Γ) ∩ H) (hV₁c.inter_right hH) Set.inter_subset_right V₁
        V₁.mem_nhds_one)
    refine ⟨{x | ∀ k ∈ Finset.range (N + 1), h ^ k * x * (h ^ k)⁻¹ ∈ V₁}, ?_, ?_⟩
    · refine (Filter.eventually_all_finset _).mpr fun k _ => ?_
      have hc : Continuous fun x : Γ => h ^ k * x * (h ^ k)⁻¹ := by fun_prop
      exact hc.continuousAt.eventually_mem (by simpa using V₁.mem_nhds_one)
    · intro x hxH hxY
      have hxV₁ : x ∈ V₁ := by simpa using hxY 0 (Finset.mem_range.mpr (by omega))
      have hj : ∀ j : ℕ, h ^ j * x * (h ^ j)⁻¹ ∈ V₁ := by
        intro j
        rcases le_or_gt j N with hjN | hjN
        · exact hxY j (Finset.mem_range.mpr (by omega))
        · exact hN j hjN.le x ⟨hxV₁, hxH⟩
      refine (hmem x).2 ⟨hxH, fun i j => ?_⟩
      have hyH : h ^ j * x * (h ^ j)⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp (hMH (pow_mem hh j)) x).mp hxH
      have e : (a ^ i * h ^ j) * x * (a ^ i * h ^ j)⁻¹ =
          a ^ i * (h ^ j * x * (h ^ j)⁻¹) * (a ^ i)⁻¹ := by group
      rw [e]
      exact hW'V i _ hyH (hV₁ (hj j)).1

/-- **Iwahori basis with a weak second contraction.** Unique `O * M * U`
factorization, an open product of identity neighborhoods, uniform contraction of
`U` by the powers of a central element `g ∈ M` (and of `O` by those of `g⁻¹`),
and equicontinuity at `1` of conjugation by the powers of a second central
element `a ∈ M` on `U` (and of `a⁻¹` on `O`) give compact open subgroups inside
every identity neighborhood with an Iwahori contraction for `g` and a weak
Iwahori contraction for `a`. -/
theorem exists_weakIwahoriBasis_of_contraction
    [NonarchimedeanGroup Γ] [LocallyCompactSpace Γ]
    {U M O : Subgroup Γ} {g a : Γ}
    (hO : IsClosed (O : Set Γ)) (hU : IsClosed (U : Set Γ))
    (hg : g ∈ M) (ha : a ∈ M) (hcomm : ∀ m ∈ M, m * g = g * m)
    (hcomma : ∀ m ∈ M, m * a = a * m)
    (hMO : M ≤ Subgroup.normalizer (O : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (hunique : ∀ o ∈ O, ∀ m ∈ M, ∀ u ∈ U, ∀ o' ∈ O, ∀ m' ∈ M, ∀ u' ∈ U,
      o * m * u = o' * m' * u' → o = o' ∧ m = m' ∧ u = u')
    (hcell : ∀ A ∈ 𝓝 (1 : Γ), ∀ B ∈ 𝓝 (1 : Γ), ∀ C ∈ 𝓝 (1 : Γ),
      {x : Γ | ∃ a ∈ A ∩ (O : Set Γ), ∃ b ∈ B ∩ (M : Set Γ), ∃ c ∈ C ∩ (U : Set Γ),
        x = a * b * c} ∈ 𝓝 (1 : Γ))
    (hcontrU : ∀ C : Set Γ, IsCompact C → C ⊆ U → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, g ^ n * c * (g ^ n)⁻¹ ∈ W)
    (hcontrO : ∀ C : Set Γ, IsCompact C → C ⊆ O → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, (g ^ n)⁻¹ * c * g ^ n ∈ W)
    (hweakU : ∀ W ∈ 𝓝 (1 : Γ), ∃ W' ∈ 𝓝 (1 : Γ), ∀ i : ℕ, ∀ y ∈ U, y ∈ W' →
      a ^ i * y * (a ^ i)⁻¹ ∈ W)
    (hweakO : ∀ W ∈ 𝓝 (1 : Γ), ∃ W' ∈ 𝓝 (1 : Γ), ∀ i : ℕ, ∀ y ∈ O, y ∈ W' →
      (a ^ i)⁻¹ * y * a ^ i ∈ W) :
    ∀ W : Set Γ, IsOpen W → (1 : Γ) ∈ W →
      ∃ K : OpenSubgroup Γ, IsCompact (K : Set Γ) ∧ (K : Set Γ) ⊆ W ∧
        IsIwahoriContraction K U M O g ∧ IsWeakIwahoriContraction K U M O a := by
  intro W hW h1W
  obtain ⟨V, hVc, hVW⟩ := exists_isCompact_openSubgroup_subset (hW.mem_nhds h1W)
  have hgpow : ∀ n : ℕ, g ^ n ∈ M := fun n => pow_mem hg n
  have hOconj : ∀ m ∈ M, ∀ x ∈ O, m * x * m⁻¹ ∈ O :=
    fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (hMO hm) x).mp hx
  have hUconj : ∀ m ∈ M, ∀ x ∈ U, m * x * m⁻¹ ∈ U :=
    fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (hMU hm) x).mp hx
  -- The `O`-piece, stable under conjugation by `g⁻¹`.
  obtain ⟨A0, hA0O, hA0V, hA0c, hA0g, hA0a, hA0B, YA, hYA, hYA0⟩ :=
    exists_stable_piece_of_weak V hVc O M hO (inv_mem hg) (inv_mem ha)
      (fun m hm => (Commute.inv_right (hcomm m hm)).eq)
      (fun m hm => (Commute.inv_right (hcomma m hm)).eq) hMO
      (fun C hC hCO W hW => by simpa only [inv_pow, inv_inv] using hcontrO C hC hCO W hW)
      (fun W hW => by
        obtain ⟨W', hW', h'⟩ := hweakO W hW
        exact ⟨W', hW', fun i y hy hyW => by
          simpa only [inv_pow, inv_inv] using h' i y hy hyW⟩)
  -- The `U`-piece, stable under conjugation by `g`.
  obtain ⟨C0, hC0U, hC0V, hC0c, hC0g, hC0a, hC0B, YC, hYC, hYC0⟩ :=
    exists_stable_piece_of_weak V hVc U M hU hg ha hcomm hcomma hMU hcontrU hweakU
  have hA0pow : ∀ n : ℕ, ∀ x ∈ A0, (g ^ n)⁻¹ * x * g ^ n ∈ A0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have e : (g ^ (n + 1))⁻¹ * x * g ^ (n + 1) =
          g⁻¹ * ((g ^ n)⁻¹ * x * g ^ n) * g⁻¹⁻¹ := by group
      rw [e]
      exact hA0g _ (ih x hx)
  let B0 : Subgroup Γ := V.toSubgroup ⊓ M
  -- An identity neighborhood made of the three pieces.
  let Z : Set Γ := {x | ∃ a ∈ A0, ∃ b ∈ B0, ∃ c ∈ C0, x = a * b * c}
  have hZ : Z ∈ 𝓝 (1 : Γ) := by
    refine Filter.mem_of_superset (hcell YA hYA (V : Set Γ) V.mem_nhds_one YC hYC) ?_
    rintro x ⟨a, ⟨haY, haO⟩, b, ⟨hbV, hbM⟩, c, ⟨hcY, hcU⟩, rfl⟩
    exact ⟨a, hYA0 a haO haY, b, Subgroup.mem_inf.mpr ⟨hbV, hbM⟩, c, hYC0 c hcU hcY, rfl⟩
  obtain ⟨Q, hQZ⟩ := NonarchimedeanGroup.is_nonarchimedean Z hZ
  have hQn : (Q : Set Γ) ∈ 𝓝 (1 : Γ) := Q.mem_nhds_one
  -- Choice of the shrinking exponent `n`.
  have hY1 : {y : Γ | ∀ s ∈ (A0 : Set Γ), s * y * s⁻¹ ∈ Q} ∈ 𝓝 (1 : Γ) :=
    eventually_forall_conj_mem hA0c hQn
  have hY2 : {y : Γ | y⁻¹ ∈ Q ∧ ∀ s ∈ (C0 : Set Γ), s * y * s⁻¹ ∈ Q} ∈ 𝓝 (1 : Γ) :=
    (Filter.eventually_of_mem hQn fun y hy => Q.inv_mem hy).and
      (eventually_forall_conj_mem hC0c hQn)
  obtain ⟨n, hn1, hn2⟩ := ((hcontrU C0 hC0c hC0U _ hY1).and
    (hcontrO A0 hA0c hA0O _ hY2)).exists
  -- The shrunken `O`-piece.
  let A : Subgroup Γ := A0.comap (MulAut.conj (g ^ n)).toMonoidHom
  have hAmem : ∀ x, x ∈ A ↔ g ^ n * x * (g ^ n)⁻¹ ∈ A0 := by
    intro x
    simp only [A, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hAA0 : ∀ x ∈ A, x ∈ A0 := by
    intro x hx
    have e : x = (g ^ n)⁻¹ * (g ^ n * x * (g ^ n)⁻¹) * g ^ n := by group
    rw [e]
    exact hA0pow n _ ((hAmem x).1 hx)
  have hAO : ∀ x ∈ A, x ∈ O := fun x hx => hA0O (hAA0 x hx)
  have hAg : ∀ x ∈ A, g⁻¹ * x * g ∈ A := by
    intro x hx
    refine (hAmem _).2 ?_
    have e : g ^ n * (g⁻¹ * x * g) * (g ^ n)⁻¹ = g⁻¹ * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹⁻¹ := by
      group
    rw [e]
    exact hA0g _ ((hAmem x).1 hx)
  have hAa : ∀ x ∈ A, a⁻¹ * x * a ∈ A := by
    intro x hx
    refine (hAmem _).2 ?_
    have hagn : Commute (g ^ n) a := Commute.pow_left (hcomma g hg) n
    have e : g ^ n * (a⁻¹ * x * a) * (g ^ n)⁻¹ = a⁻¹ * (g ^ n * x * (g ^ n)⁻¹) * a⁻¹⁻¹ := by
      rw [inv_inv]
      calc g ^ n * (a⁻¹ * x * a) * (g ^ n)⁻¹
          = (g ^ n * a⁻¹) * x * (a * (g ^ n)⁻¹) := by group
        _ = (a⁻¹ * g ^ n) * x * ((g ^ n)⁻¹ * a) := by
          rw [(hagn.inv_right).eq, (hagn.inv_left).eq]
        _ = a⁻¹ * (g ^ n * x * (g ^ n)⁻¹) * a := by group
    rw [e]
    exact hA0a _ ((hAmem x).1 hx)
  have hAB : ∀ b ∈ B0, ∀ x ∈ A, b * x * b⁻¹ ∈ A := by
    intro b hb x hx
    refine (hAmem _).2 ?_
    have hbn : Commute (g ^ n) b :=
      (Commute.pow_right (hcomm b (Subgroup.mem_inf.mp hb).2) n).symm
    rw [conj_conj_of_commute hbn]
    exact hA0B b hb _ ((hAmem x).1 hx)
  obtain ⟨YA', hYA', hYA'A⟩ : ∃ Y ∈ 𝓝 (1 : Γ), ∀ x ∈ O, x ∈ Y → x ∈ A := by
    have hc : Continuous fun x : Γ => g ^ n * x * (g ^ n)⁻¹ := by fun_prop
    refine ⟨(fun x : Γ => g ^ n * x * (g ^ n)⁻¹) ⁻¹' YA,
      hc.continuousAt.preimage_mem_nhds (by simpa using hYA), fun x hxO hxY => ?_⟩
    exact (hAmem x).2 (hYA0 _ (hOconj _ (hgpow n) x hxO) hxY)
  -- The key commutation `C0 * A ⊆ A * B0 * C0`.
  have hswap : ∀ c ∈ C0, ∀ a ∈ A, ∃ a' ∈ A, ∃ b' ∈ B0, ∃ c' ∈ C0, c * a = a' * b' * c' := by
    intro c hc a ha
    have hã : g ^ n * a * (g ^ n)⁻¹ ∈ A0 := (hAmem a).1 ha
    obtain ⟨hinv, hconj⟩ := hn2 _ hã
    have ea : (g ^ n)⁻¹ * (g ^ n * a * (g ^ n)⁻¹) * g ^ n = a := by group
    rw [ea] at hinv hconj
    have hx : a⁻¹ * (c * a * c⁻¹) ∈ Q := Q.mul_mem hinv (hconj c hc)
    obtain ⟨o1, ho1, m1, hm1, u1, hu1, h1⟩ := hQZ hx
    have hy := hn1 c hc _ (A0.inv_mem hã)
    obtain ⟨o2, ho2, m2, hm2, u2, hu2, h2⟩ := hQZ hy
    have e2 : (g ^ n * a * (g ^ n)⁻¹)⁻¹ * (g ^ n * c * (g ^ n)⁻¹) *
        (g ^ n * a * (g ^ n)⁻¹)⁻¹⁻¹ = g ^ n * (a⁻¹ * (c * a * c⁻¹)) * c * (g ^ n)⁻¹ := by
      group
    rw [e2, h1] at h2
    have e3 : g ^ n * (o1 * m1 * u1) * c * (g ^ n)⁻¹ =
        (g ^ n * o1 * (g ^ n)⁻¹) * (g ^ n * m1 * (g ^ n)⁻¹) * (g ^ n * (u1 * c) * (g ^ n)⁻¹) := by
      group
    rw [e3] at h2
    have hu1c : u1 * c ∈ C0 := C0.mul_mem hu1 hc
    obtain ⟨ho, -, -⟩ := hunique _ (hOconj _ (hgpow n) _ (hA0O ho1))
      _ (M.mul_mem (M.mul_mem (hgpow n) (Subgroup.mem_inf.mp hm1).2) (M.inv_mem (hgpow n)))
      _ (hUconj _ (hgpow n) _ (hC0U hu1c))
      _ (hA0O ho2) _ (Subgroup.mem_inf.mp hm2).2 _ (hC0U hu2) h2
    have ho1A : o1 ∈ A := (hAmem o1).2 (ho ▸ ho2)
    refine ⟨a * o1, A.mul_mem ha ho1A, m1, hm1, u1 * c, hu1c, ?_⟩
    calc c * a = a * (a⁻¹ * (c * a * c⁻¹)) * c := by group
      _ = a * (o1 * m1 * u1) * c := by rw [h1]
      _ = a * o1 * m1 * (u1 * c) := by group
  -- The compact open subgroup `A * B0 * C0`.
  let K : Subgroup Γ :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B0, ∃ c ∈ C0, x = a * b * c}
      one_mem' := ⟨1, A.one_mem, 1, B0.one_mem, 1, C0.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, c, hc, rfl⟩ ⟨a', ha', b', hb', c', hc', rfl⟩
        obtain ⟨a'', ha'', b'', hb'', c'', hc'', e⟩ := hswap c hc a' ha'
        refine ⟨a * (b * a'' * b⁻¹), A.mul_mem ha (hAB b hb a'' ha''),
          b * b'' * b', B0.mul_mem (B0.mul_mem hb hb'') hb',
          b'⁻¹ * c'' * b' * c', C0.mul_mem ?_ hc', ?_⟩
        · simpa only [inv_inv] using hC0B b'⁻¹ (B0.inv_mem hb') c'' hc''
        · calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
            _ = a * b * (a'' * b'' * c'') * b' * c' := by rw [e]
            _ = a * (b * a'' * b⁻¹) * (b * b'' * b') * (b'⁻¹ * c'' * b' * c') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, c, hc, rfl⟩
        have ha1 : b⁻¹ * a⁻¹ * b ∈ A := by
          simpa only [inv_inv] using hAB b⁻¹ (B0.inv_mem hb) a⁻¹ (A.inv_mem ha)
        obtain ⟨a'', ha'', b'', hb'', c'', hc'', e⟩ := hswap c⁻¹ (C0.inv_mem hc) _ ha1
        refine ⟨a'', ha'', b'' * b⁻¹, B0.mul_mem hb'' (B0.inv_mem hb),
          b * c'' * b⁻¹, hC0B b hb c'' hc'', ?_⟩
        calc (a * b * c)⁻¹ = c⁻¹ * (b⁻¹ * a⁻¹ * b) * b⁻¹ := by group
          _ = a'' * b'' * c'' * b⁻¹ := by rw [e]
          _ = a'' * (b'' * b⁻¹) * (b * c'' * b⁻¹) := by group }
  have hKmem : ∀ x, x ∈ K ↔ ∃ a ∈ A, ∃ b ∈ B0, ∃ c ∈ C0, x = a * b * c := fun _ => Iff.rfl
  have hKn : (K : Set Γ) ∈ 𝓝 (1 : Γ) := by
    refine Filter.mem_of_superset (hcell YA' hYA' (V : Set Γ) V.mem_nhds_one YC hYC) ?_
    rintro x ⟨a, ⟨haY, haO⟩, b, ⟨hbV, hbM⟩, c, ⟨hcY, hcU⟩, rfl⟩
    exact ⟨a, hYA'A a haO haY, b, Subgroup.mem_inf.mpr ⟨hbV, hbM⟩, c, hYC0 c hcU hcY, rfl⟩
  let KO : OpenSubgroup Γ := ⟨K, K.isOpen_of_mem_nhds hKn⟩
  have hKOmem : ∀ x, x ∈ KO ↔ x ∈ K := fun _ => Iff.rfl
  have hKV : (KO : Set Γ) ⊆ V := by
    intro x hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem x).1 ((hKOmem x).1 hx)
    exact V.mul_mem (V.mul_mem (hA0V (hAA0 a ha)) (Subgroup.mem_inf.mp hb).1) (hC0V hc)
  have hAK : ∀ x ∈ A, x ∈ K := fun x hx =>
    (hKmem x).2 ⟨x, hx, 1, B0.one_mem, 1, C0.one_mem, by simp⟩
  have hBK : ∀ x ∈ B0, x ∈ K := fun x hx =>
    (hKmem x).2 ⟨1, A.one_mem, x, hx, 1, C0.one_mem, by simp⟩
  have hCK : ∀ x ∈ C0, x ∈ K := fun x hx =>
    (hKmem x).2 ⟨1, A.one_mem, 1, B0.one_mem, x, hx, by simp⟩
  have hKU : ∀ x ∈ K, x ∈ U → x ∈ C0 := by
    intro x hx hxU
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem x).1 hx
    obtain ⟨-, -, e⟩ := hunique a (hAO a ha) b (Subgroup.mem_inf.mp hb).2 c (hC0U hc)
      1 O.one_mem 1 M.one_mem _ hxU (by simp)
    rw [← e]
    exact hc
  have hKO : ∀ x ∈ K, x ∈ O → x ∈ A := by
    intro x hx hxO
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem x).1 hx
    obtain ⟨e, -, -⟩ := hunique a (hAO a ha) b (Subgroup.mem_inf.mp hb).2 c (hC0U hc)
      _ hxO 1 M.one_mem 1 U.one_mem (by simp)
    rw [← e]
    exact ha
  have hleviL : ∀ m ∈ M, g⁻¹ * m * g = m := fun m hm => by
    rw [mul_assoc, hcomm m hm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hleviR : ∀ m ∈ M, g * m * g⁻¹ = m := fun m hm => by
    rw [← hcomm m hm, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨KO, hVc.of_isClosed_subset KO.isClosed hKV, hKV.trans hVW, ?_, ?_⟩
  · exact
      { mem_levi := hg
        factor := fun k hk => by
          obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (hKmem k).1 ((hKOmem k).1 hk)
          exact ⟨a, Subgroup.mem_inf.mpr ⟨hAK a ha, hAO a ha⟩,
            b, Subgroup.mem_inf.mpr ⟨hBK b hb, (Subgroup.mem_inf.mp hb).2⟩,
            c, Subgroup.mem_inf.mpr ⟨hCK c hc, hC0U hc⟩, rfl⟩
        upper := fun u hu => by
          obtain ⟨hK, hU'⟩ := Subgroup.mem_inf.mp hu
          have h' := hC0g u (hKU u hK hU')
          exact Subgroup.mem_inf.mpr ⟨hCK _ h', hC0U h'⟩
        levi := fun m hm => by
          rw [hleviL m (Subgroup.mem_inf.mp hm).2]
          exact hm
        lower := fun l hl => by
          obtain ⟨hK, hO'⟩ := Subgroup.mem_inf.mp hl
          have h' := hAg l (hKO l hK hO')
          exact Subgroup.mem_inf.mpr ⟨hAK _ h', hAO _ h'⟩
        exhaust := fun x hx => by
          obtain ⟨r, hr⟩ := (hcontrU {x} isCompact_singleton
            (Set.singleton_subset_iff.mpr hx) YC hYC).exists
          exact ⟨r, hCK _ (hYC0 _ (hUconj _ (hgpow r) x hx) (hr x rfl))⟩
        contract := fun L => by
          obtain ⟨s, hs⟩ := (hcontrO A0 hA0c hA0O L L.mem_nhds_one).exists
          exact ⟨s, fun l hl => hs l (hAA0 l (hKO l (Subgroup.mem_inf.mp hl).1
            (Subgroup.mem_inf.mp hl).2))⟩ }
  · exact
      { mem_levi := ha
        upper := fun u hu => by
          obtain ⟨hK, hU'⟩ := Subgroup.mem_inf.mp hu
          have h' := hC0a u (hKU u hK hU')
          exact Subgroup.mem_inf.mpr ⟨hCK _ h', hC0U h'⟩
        levi := fun m hm => by
          have e : a⁻¹ * m * a = m := by
            rw [mul_assoc, hcomma m (Subgroup.mem_inf.mp hm).2, ← mul_assoc, inv_mul_cancel,
              one_mul]
          rw [e]
          exact hm
        lower := fun l hl => by
          obtain ⟨hK, hO'⟩ := Subgroup.mem_inf.mp hl
          have h' := hAa l (hKO l hK hO')
          exact Subgroup.mem_inf.mpr ⟨hAK _ h', hAO _ h'⟩ }

end Langlands.Jacquet
