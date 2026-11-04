import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Opposite Iwahori bases from one contracting central element

In a locally compact nonarchimedean group, three subgroups `O`, `M`, `U` with
unique factorization `O * M * U`, an open product near the identity, and a
central element `g` of `M` whose powers contract `U` (and whose inverse powers
contract `O`) uniformly on compact sets give compact open subgroups inside
every identity neighborhood, with Iwahori contractions in both orders for the
same fixed `g`. -/

namespace Langlands.Jacquet

open Topology Filter

universe uΓ

variable {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]

omit [TopologicalSpace Γ] in
/-- Commuting elements give commuting conjugations. -/
theorem conj_conj_of_commute {a b : Γ} (hab : Commute a b) (x : Γ) :
    a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ :=
  calc a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
    _ = (b * a) * x * (b * a)⁻¹ := by rw [hab.eq]
    _ = b * (a * x * a⁻¹) * b⁻¹ := by group

/-- In a locally compact nonarchimedean group, every identity neighborhood
contains a compact open subgroup. -/
theorem exists_isCompact_openSubgroup_subset [NonarchimedeanGroup Γ] [LocallyCompactSpace Γ]
    {W : Set Γ} (hW : W ∈ 𝓝 (1 : Γ)) :
    ∃ V : OpenSubgroup Γ, IsCompact (V : Set Γ) ∧ (V : Set Γ) ⊆ W := by
  obtain ⟨s, hs, hsW, hsc⟩ := local_compact_nhds hW
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean s hs
  exact ⟨V, hsc.of_isClosed_subset V.isClosed hV, hV.trans hsW⟩

/-- Conjugation by the elements of a compact set is uniformly continuous at the
identity. -/
theorem eventually_forall_conj_mem [IsTopologicalGroup Γ] {S : Set Γ} (hS : IsCompact S)
    {Q : Set Γ} (hQ : Q ∈ 𝓝 (1 : Γ)) :
    ∀ᶠ y in 𝓝 (1 : Γ), ∀ s ∈ S, s * y * s⁻¹ ∈ Q := by
  refine hS.eventually_forall_of_forall_eventually fun s _ => ?_
  have hc : Continuous fun z : Γ × Γ => z.2 * z.1 * z.2⁻¹ := by fun_prop
  have h1 : (fun z : Γ × Γ => z.2 * z.1 * z.2⁻¹) (1, s) = 1 := by simp
  exact hc.continuousAt.eventually_mem (by simpa using hQ)

/-- Inside a compact open subgroup `V`, the elements of a closed subgroup `H`
whose conjugates by all nonnegative powers of `h` stay in `V` form a compact
subgroup that is stable under conjugation by `h`, normalized by `V ∩ M`, and
relatively open in `H`, provided the powers of `h` contract `H`. -/
theorem exists_stable_piece [IsTopologicalGroup Γ] (V : OpenSubgroup Γ)
    (hVc : IsCompact (V : Set Γ)) (H M : Subgroup Γ) (hH : IsClosed (H : Set Γ))
    {h : Γ} (hh : h ∈ M) (hcomm : ∀ m ∈ M, m * h = h * m)
    (hMH : M ≤ Subgroup.normalizer (H : Set Γ))
    (hcontr : ∀ C : Set Γ, IsCompact C → C ⊆ H → ∀ W ∈ 𝓝 (1 : Γ),
      ∀ᶠ n in atTop, ∀ c ∈ C, h ^ n * c * (h ^ n)⁻¹ ∈ W) :
    ∃ P : Subgroup Γ, P ≤ H ∧ (P : Set Γ) ⊆ V ∧ IsCompact (P : Set Γ) ∧
      (∀ x ∈ P, h * x * h⁻¹ ∈ P) ∧
      (∀ b ∈ V.toSubgroup ⊓ M, ∀ x ∈ P, b * x * b⁻¹ ∈ P) ∧
      ∃ Y ∈ 𝓝 (1 : Γ), ∀ x ∈ H, x ∈ Y → x ∈ P := by
  let P : Subgroup Γ :=
    H ⊓ ⨅ k : ℕ, V.toSubgroup.comap (MulAut.conj (h ^ k)).toMonoidHom
  have hmem : ∀ x, x ∈ P ↔ x ∈ H ∧ ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ ∈ V := by
    intro x
    simp only [P, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, OpenSubgroup.mem_toSubgroup]
  have hPH : P ≤ H := fun x hx => ((hmem x).1 hx).1
  have hPV : (P : Set Γ) ⊆ V := fun x hx => by simpa using ((hmem x).1 hx).2 0
  have hset : (P : Set Γ) =
      (H : Set Γ) ∩ ⋂ k : ℕ, (fun x => h ^ k * x * (h ^ k)⁻¹) ⁻¹' (V : Set Γ) := by
    ext x
    rw [SetLike.mem_coe, hmem]
    simp
  have hPclosed : IsClosed (P : Set Γ) := by
    rw [hset]
    exact hH.inter (isClosed_iInter fun k => V.isClosed.preimage (by fun_prop))
  refine ⟨P, hPH, hPV, hVc.of_isClosed_subset hPclosed hPV, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH hh) x).mp hxH, fun k => ?_⟩
    have e : h ^ k * (h * x * h⁻¹) * (h ^ k)⁻¹ = h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ := by
      group
    rw [e]
    exact hxV (k + 1)
  · intro b hb x hx
    obtain ⟨hbV, hbM⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨hxH, hxV⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hMH hbM) x).mp hxH, fun k => ?_⟩
    have hbk : Commute (h ^ k) b := (Commute.pow_right (hcomm b hbM) k).symm
    rw [conj_conj_of_commute hbk]
    exact V.mul_mem (V.mul_mem hbV (hxV k)) (V.inv_mem hbV)
  · obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hcontr ((V : Set Γ) ∩ H) (hVc.inter_right hH) Set.inter_subset_right V V.mem_nhds_one)
    refine ⟨{x | ∀ k ∈ Finset.range (N + 1), h ^ k * x * (h ^ k)⁻¹ ∈ V}, ?_, ?_⟩
    · refine (Filter.eventually_all_finset _).mpr fun k _ => ?_
      have hc : Continuous fun x : Γ => h ^ k * x * (h ^ k)⁻¹ := by fun_prop
      exact hc.continuousAt.eventually_mem (by simpa using V.mem_nhds_one)
    · intro x hxH hxY
      refine (hmem x).2 ⟨hxH, fun k => ?_⟩
      rcases le_or_gt k N with hk | hk
      · exact hxY k (Finset.mem_range.mpr (by omega))
      · have hxV : x ∈ V := by
          simpa using hxY 0 (Finset.mem_range.mpr (by omega))
        exact hN k hk.le x ⟨hxV, hxH⟩

/-- **Abstract opposite Iwahori basis.** Unique `O * M * U` factorization, an
open product of identity neighborhoods, and uniform contraction of `U` by the
powers of a central element `g ∈ M` and of `O` by the powers of `g⁻¹` give a
fixed-element compact open basis with Iwahori contractions in both orders. -/
theorem hasOppositeIwahoriContractionBasis_of_contraction
    [NonarchimedeanGroup Γ] [LocallyCompactSpace Γ]
    {U M O : Subgroup Γ} {g : Γ}
    (hO : IsClosed (O : Set Γ)) (hU : IsClosed (U : Set Γ))
    (hg : g ∈ M) (hcomm : ∀ m ∈ M, m * g = g * m)
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
      ∀ᶠ n in atTop, ∀ c ∈ C, (g ^ n)⁻¹ * c * g ^ n ∈ W) :
    HasOppositeIwahoriContractionBasis U M O g := by
  intro W hW h1W
  obtain ⟨V, hVc, hVW⟩ := exists_isCompact_openSubgroup_subset (hW.mem_nhds h1W)
  have hgpow : ∀ n : ℕ, g ^ n ∈ M := fun n => pow_mem hg n
  have hOconj : ∀ m ∈ M, ∀ x ∈ O, m * x * m⁻¹ ∈ O :=
    fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (hMO hm) x).mp hx
  have hUconj : ∀ m ∈ M, ∀ x ∈ U, m * x * m⁻¹ ∈ U :=
    fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (hMU hm) x).mp hx
  -- The `O`-piece, stable under conjugation by `g⁻¹`.
  obtain ⟨A0, hA0O, hA0V, hA0c, hA0g, hA0B, YA, hYA, hYA0⟩ :=
    exists_stable_piece V hVc O M hO (inv_mem hg)
      (fun m hm => (Commute.inv_right (hcomm m hm)).eq) hMO
      (fun C hC hCO W hW => by simpa only [inv_pow, inv_inv] using hcontrO C hC hCO W hW)
  -- The `U`-piece, stable under conjugation by `g`.
  obtain ⟨C0, hC0U, hC0V, hC0c, hC0g, hC0B, YC, hYC, hYC0⟩ :=
    exists_stable_piece V hVc U M hU hg hcomm hMU hcontrU
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
      { mem_levi := inv_mem hg
        factor := fun k hk => by
          obtain ⟨a, ha, b, hb, c, hc, e⟩ := (hKmem k⁻¹).1 ((hKOmem k⁻¹).1 (KO.inv_mem hk))
          refine ⟨c⁻¹, Subgroup.mem_inf.mpr ⟨hCK _ (C0.inv_mem hc), U.inv_mem (hC0U hc)⟩,
            b⁻¹, Subgroup.mem_inf.mpr ⟨hBK _ (B0.inv_mem hb),
              M.inv_mem (Subgroup.mem_inf.mp hb).2⟩,
            a⁻¹, Subgroup.mem_inf.mpr ⟨hAK _ (A.inv_mem ha), O.inv_mem (hAO a ha)⟩, ?_⟩
          calc k = (k⁻¹)⁻¹ := (inv_inv k).symm
            _ = (a * b * c)⁻¹ := by rw [e]
            _ = c⁻¹ * b⁻¹ * a⁻¹ := by group
        upper := fun u hu => by
          obtain ⟨hK, hO'⟩ := Subgroup.mem_inf.mp hu
          have h' := hAg u (hKO u hK hO')
          rw [inv_inv]
          exact Subgroup.mem_inf.mpr ⟨hAK _ h', hAO _ h'⟩
        levi := fun m hm => by
          rw [inv_inv, hleviR m (Subgroup.mem_inf.mp hm).2]
          exact hm
        lower := fun l hl => by
          obtain ⟨hK, hU'⟩ := Subgroup.mem_inf.mp hl
          have h' := hC0g l (hKU l hK hU')
          rw [inv_inv]
          exact Subgroup.mem_inf.mpr ⟨hCK _ h', hC0U h'⟩
        exhaust := fun x hx => by
          obtain ⟨r, hr⟩ := (hcontrO {x} isCompact_singleton
            (Set.singleton_subset_iff.mpr hx) YA' hYA').exists
          refine ⟨r, ?_⟩
          rw [inv_pow, inv_inv]
          have hxO : (g ^ r)⁻¹ * x * g ^ r ∈ O := by
            simpa only [inv_inv] using hOconj _ (M.inv_mem (hgpow r)) x hx
          exact hAK _ (hYA'A _ hxO (hr x rfl))
        contract := fun L => by
          obtain ⟨s, hs⟩ := (hcontrU C0 hC0c hC0U L L.mem_nhds_one).exists
          refine ⟨s, fun l hl => ?_⟩
          rw [inv_pow, inv_inv]
          exact hs l (hKU l (Subgroup.mem_inf.mp hl).1 (Subgroup.mem_inf.mp hl).2) }

end Langlands.Jacquet
