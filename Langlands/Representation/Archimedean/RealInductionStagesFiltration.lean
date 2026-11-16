import Langlands.Representation.Archimedean.RealInductionStagesDerivative
import Langlands.Representation.Archimedean.RealInducedPairFiltrationReduction

/-!
# Induction in stages of adjacent filtrations

This file proves `RealAdjacentFiltrationInStagesStatement`. A filtration as in
`RealAdjacentFiltration` of the standard module of `[x, y]` on `GL_r(ℝ)`, given by maps
`q j`, induces one of the standard module of `pre ++ x :: y :: post` on `GL_n(ℝ)` with the same
lists `ws j`. The maps on `GL_n(ℝ)` are `Q j = Ind T j` (`RealInductionStagesInduce`), where
`T j` is the average of `q j` over `O(r)` (`RealInductionStagesAverage`).

With `F m = ⨆_{i < m} range (q i)`, the subspaces `F m` are `O(r)`-stable, `T j - q j` maps
into `F j`, and `T j` commutes with right derivatives modulo `F j`. The key step shows by
induction on `m` that every `G` all of whose slices `σ_κ G` (`κ ∈ O(n)`) lie in `F m` lies in
`⨆_{i < m} range (Q i)` (`mem_iSup_range_ind`). The derivative defect of `Q j` has all slices in
`F j` (`sliceK_ind_lie_sub_mem`), so `Q j` is an intertwiner modulo `⨆_{i < j} range (Q i)`.
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

/-! ## Intertwiners modulo a subspace in terms of `kRep` and `lie` -/

section Intertwiner

variable {n : ℕ} {ds es : List RealBlock}

theorem coe_kRep (k : unitaryCompact ℝ n) (f : KFin n ds) :
    ((kRep n ds k f : KFin n ds) : Langlands.GeneralLinear n ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
        (f : Langlands.GeneralLinear n ℝ → ℂ) :=
  funext fun g => kRep_apply_coe n ds k f g

/-- `IsRealIntertwinerModulo` in terms of `kRep` and `lie`. -/
theorem isRealIntertwinerModulo_iff {M : Submodule ℂ (KFin n es)}
    {q : KFin n ds →ₗ[ℂ] KFin n es} :
    IsRealIntertwinerModulo n ds es M q ↔
      (∀ k f, q (kRep n ds k f) - kRep n es k (q f) ∈ M) ∧
        ∀ X f, q (lie n ds X f) - lie n es X (q f) ∈ M := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k f => ?_, fun X f => ?_⟩
    · obtain ⟨hf, hg, hm⟩ := h1 k f
      have e1 : (⟨_, hf⟩ : KFin n ds) = kRep n ds k f := Subtype.ext (coe_kRep k f).symm
      have e2 : (⟨_, hg⟩ : KFin n es) = kRep n es k (q f) :=
        Subtype.ext (coe_kRep k (q f)).symm
      rwa [e1, e2] at hm
    · obtain ⟨hf, hg, hm⟩ := h2 X f
      have e1 : (⟨_, hf⟩ : KFin n ds) = lie n ds X f :=
        Subtype.ext (lie_apply_coe n ds X f).symm
      have e2 : (⟨_, hg⟩ : KFin n es) = lie n es X (q f) :=
        Subtype.ext (lie_apply_coe n es X (q f)).symm
      rwa [e1, e2] at hm
  · rintro ⟨h1, h2⟩
    refine ⟨fun k f => ?_, fun X f => ?_⟩
    · have hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            KFin n ds := by
        rw [← coe_kRep]
        exact (kRep n ds k f).2
      have hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (q f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            KFin n es := by
        rw [← coe_kRep]
        exact (kRep n es k (q f)).2
      refine ⟨hf, hg, ?_⟩
      have e1 : (⟨_, hf⟩ : KFin n ds) = kRep n ds k f := Subtype.ext (coe_kRep k f).symm
      have e2 : (⟨_, hg⟩ : KFin n es) = kRep n es k (q f) :=
        Subtype.ext (coe_kRep k (q f)).symm
      rw [e1, e2]
      exact h1 k f
    · have hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          KFin n ds := by
        rw [← lie_apply_coe]
        exact (lie n ds X f).2
      have hg : rightDerivative (matrixModel ℝ n) X (q f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          KFin n es := by
        rw [← lie_apply_coe]
        exact (lie n es X (q f)).2
      refine ⟨hf, hg, ?_⟩
      have e1 : (⟨_, hf⟩ : KFin n ds) = lie n ds X f :=
        Subtype.ext (lie_apply_coe n ds X f).symm
      have e2 : (⟨_, hg⟩ : KFin n es) = lie n es X (q f) :=
        Subtype.ext (lie_apply_coe n es X (q f)).symm
      rw [e1, e2]
      exact h2 X f

/-- Changing the source list along an equality of lists. -/
theorem isRealIntertwinerModulo_comp_ofEq {L₁ L₂ : List RealBlock} (e : L₁ = L₂)
    {M : Submodule ℂ (KFin n es)} {q : KFin n L₂ →ₗ[ℂ] KFin n es}
    (hq : IsRealIntertwinerModulo n L₂ es M q) :
    IsRealIntertwinerModulo n L₁ es M
      (q ∘ₗ (LinearEquiv.ofEq _ _ (congrArg (KFin n) e)).toLinearMap) := by
  subst e
  have : q ∘ₗ (LinearEquiv.ofEq _ _ (congrArg (KFin n) (rfl : L₁ = L₁))).toLinearMap = q :=
    LinearMap.ext fun _ => rfl
  rw [this]
  exact hq

end Intertwiner

/-! ## Linear sections modulo a subspace -/

/-- If every `v ∈ N'` is congruent modulo `N` to some `T u`, there is a linear `s` with
`T (s v) - v ∈ N` for all `v ∈ N'`. -/
theorem exists_section {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (T : W →ₗ[ℂ] V) (N N' : Submodule ℂ V) (hN : ∀ v ∈ N', ∃ u, T u - v ∈ N) :
    ∃ s : V →ₗ[ℂ] W, ∀ v ∈ N', T (s v) - v ∈ N := by
  let φ : W →ₗ[ℂ] V ⧸ N := N.mkQ ∘ₗ T
  obtain ⟨g, hg⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict φ)
  have hmem : ∀ v : N', N.mkQ (v : V) ∈ LinearMap.range φ := fun v => by
    obtain ⟨u, hu⟩ := hN v v.2
    exact ⟨u, (Submodule.Quotient.eq N).mpr hu⟩
  let s' : N' →ₗ[ℂ] W := g ∘ₗ (N.mkQ ∘ₗ N'.subtype).codRestrict (LinearMap.range φ) hmem
  obtain ⟨s, hs⟩ := LinearMap.exists_extend s'
  refine ⟨s, fun v hv => ?_⟩
  have h1 : s v = g ⟨N.mkQ v, hmem ⟨v, hv⟩⟩ := LinearMap.congr_fun hs ⟨v, hv⟩
  have h2 : φ (g ⟨N.mkQ v, hmem ⟨v, hv⟩⟩) = N.mkQ v := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg ⟨N.mkQ v, hmem ⟨v, hv⟩⟩)
    simpa using this
  rw [← h1] at h2
  exact (Submodule.Quotient.eq N).mp h2

/-! ## The filtration on `GL_r(ℝ)` -/

section Filtration

variable {r : ℕ} {ds : List RealBlock} {k : ℕ} {ws : Fin k → List RealBlock}

/-- `F m = ⨆_{i < m} range (q i)`. -/
def filt (q : ∀ j : Fin k, KFin r (ws j) →ₗ[ℂ] KFin r ds) (m : ℕ) : Submodule ℂ (KFin r ds) :=
  ⨆ (i : Fin k) (_ : (i : ℕ) < m), LinearMap.range (q i)

variable (q : ∀ j : Fin k, KFin r (ws j) →ₗ[ℂ] KFin r ds)

theorem range_le_filt {i : Fin k} {m : ℕ} (hi : (i : ℕ) < m) :
    LinearMap.range (q i) ≤ filt q m :=
  le_iSup₂_of_le (f := fun (i : Fin k) (_ : (i : ℕ) < m) => LinearMap.range (q i)) i hi le_rfl

theorem filt_mono {m m' : ℕ} (hm : m ≤ m') : filt q m ≤ filt q m' :=
  iSup₂_le fun _ hi => range_le_filt q (lt_of_lt_of_le hi hm)

theorem filt_zero : filt q 0 = ⊥ :=
  iSup₂_eq_bot.mpr fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem filt_succ_le (m : ℕ) (hm : m < k) :
    filt q (m + 1) ≤ filt q m ⊔ LinearMap.range (q ⟨m, hm⟩) := by
  refine iSup₂_le fun i hi => ?_
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
  · exact le_sup_of_le_left (range_le_filt q hi')
  · have : i = ⟨m, hm⟩ := Fin.ext hi'
    subst this
    exact le_sup_right

theorem filt_eq_top (htop : ⨆ j, LinearMap.range (q j) = ⊤) : filt q k = ⊤ := by
  rw [eq_top_iff, ← htop]
  exact iSup_le fun i => range_le_filt q i.isLt

variable {q}

/-- The filtration is `O(r)`-stable. -/
theorem kRep_mem_filt
    (hq : ∀ (j : Fin k) κ f, q j (kRep r (ws j) κ f) - kRep r ds κ (q j f) ∈ filt q j)
    (m : ℕ) (κ : unitaryCompact ℝ r) : ∀ v ∈ filt q m, kRep r ds κ v ∈ filt q m := by
  suffices hle : filt q m ≤ (filt q m).comap (kRep r ds κ) from fun v hv => hle hv
  refine iSup₂_le fun i hi => ?_
  rintro _ ⟨f, rfl⟩
  rw [Submodule.mem_comap]
  have e : kRep r ds κ (q i f) =
      q i (kRep r (ws i) κ f) - (q i (kRep r (ws i) κ f) - kRep r ds κ (q i f)) := by abel
  rw [e]
  exact Submodule.sub_mem _ (range_le_filt q hi ⟨_, rfl⟩) (filt_mono q hi.le (hq i κ f))

end Filtration

/-! ## Induction in stages -/

section Stages

variable {n a r : ℕ} {pre ds post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
  (hn : realRank (pre ++ ds ++ post) = n)

include hr hn in
theorem realRank_of_realRank_eq {es : List RealBlock} (hes : realRank es = r) :
    realRank (pre ++ es ++ post) = n := by
  simp only [realRank_append'] at hn ⊢
  omega

/-- A function all of whose slices vanish is zero. -/
theorem eq_zero_of_sliceK (G : KFin n (pre ++ ds ++ post))
    (hG : ∀ κ, sliceK h ha hr κ G = 0) : G = 0 := by
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries G.2.1.1
    (0 : KFin n (pre ++ ds ++ post)).2.1.1 fun κ hκ => ?_
  have := congrArg (fun v : KFin r ds => (v : Langlands.GeneralLinear r ℝ → ℂ) 1) (hG ⟨κ, hκ⟩)
  simp only [sliceK_apply_one] at this
  rw [this]
  rfl

/-- **One step.** If `T` is exactly `O(r)`-equivariant and every element of `N'` is congruent
modulo `N` to an element of the range of `T`, then every `G` whose slices lie in `N'` differs
from an element of the range of `Ind T` by some `G'` whose slices lie in `N`. -/
theorem exists_sub_mem_range_ind {es : List RealBlock} (hes : realRank es = r)
    (T : KFin r es →ₗ[ℂ] KFin r ds) (hT : ∀ κ f, T (kRep r es κ f) = kRep r ds κ (T f))
    (N N' : Submodule ℂ (KFin r ds)) (hNst : ∀ κ, ∀ v ∈ N, kRep r ds κ v ∈ N)
    (hN'st : ∀ κ, ∀ v ∈ N', kRep r ds κ v ∈ N') (hN : ∀ v ∈ N', ∃ u, T u - v ∈ N)
    (G : KFin n (pre ++ ds ++ post)) (hG : ∀ κ, sliceK h ha hr κ G ∈ N') :
    ∃ G' : KFin n (pre ++ ds ++ post), (∀ κ, sliceK h ha hr κ G' ∈ N) ∧
      G - G' ∈ LinearMap.range (ind h ha hr hes hn T hT) := by
  have hnes := realRank_of_realRank_eq hr hn hes
  obtain ⟨s0, hs0⟩ := exists_section T N N' hN
  have hs : ∀ κ f, avg s0 (kRep r ds κ f) = kRep r es κ (avg s0 f) := avg_kRep s0
  have hsT : ∀ v ∈ N', T (avg s0 v) - v ∈ N := by
    intro v hv
    rw [map_avg s0 T hT]
    refine avg_sub_mem _ N v v fun κ => ?_
    have h1 := hNst κ⁻¹ _ (hs0 _ (hN'st κ v hv))
    rwa [map_sub, kRep_inv_kRep] at h1
  set S := ind h ha hes hr hnes (avg s0) hs with hS
  refine ⟨G - ind h ha hr hes hn T hT (S G), fun κ => ?_, ?_⟩
  · rw [map_sub, sliceK_ind h ha hr hes hn hT, hS, sliceK_ind h ha hes hr hnes hs]
    have := Submodule.neg_mem _ (hsT _ (hG κ))
    rwa [neg_sub] at this
  · rw [sub_sub_cancel]
    exact ⟨_, rfl⟩

variable {k : ℕ} {ws : Fin k → List RealBlock} (hws : ∀ j, realRank (ws j) = r)

include h ha hr hn hws in
/-- **Induction in stages of filtrations.** -/
theorem exists_stages_filtration (q : ∀ j : Fin k, KFin r (ws j) →ₗ[ℂ] KFin r ds)
    (hq : ∀ j, IsRealIntertwinerModulo r (ws j) ds
      (⨆ (i : Fin k) (_ : i < j), LinearMap.range (q i)) (q j))
    (htop : ⨆ j, LinearMap.range (q j) = ⊤) :
    ∃ Q : ∀ j : Fin k, KFin n (pre ++ ws j ++ post) →ₗ[ℂ] KFin n (pre ++ ds ++ post),
      (∀ j, IsRealIntertwinerModulo n (pre ++ ws j ++ post) (pre ++ ds ++ post)
        (⨆ (i : Fin k) (_ : i < j), LinearMap.range (Q i)) (Q j)) ∧
      ⨆ j, LinearMap.range (Q j) = ⊤ := by
  have hq' : ∀ j : Fin k, (∀ κ f, q j (kRep r (ws j) κ f) - kRep r ds κ (q j f) ∈ filt q j) ∧
      ∀ X f, q j (lie r (ws j) X f) - lie r ds X (q j f) ∈ filt q j :=
    fun j => isRealIntertwinerModulo_iff.mp (hq j)
  have hstab : ∀ m κ, ∀ v ∈ filt q m, kRep r ds κ v ∈ filt q m :=
    kRep_mem_filt fun j => (hq' j).1
  -- the averaged maps
  obtain ⟨T, hTk, hTq, hTl⟩ : ∃ T : ∀ j : Fin k, KFin r (ws j) →ₗ[ℂ] KFin r ds,
      (∀ j κ f, T j (kRep r (ws j) κ f) = kRep r ds κ (T j f)) ∧
      (∀ (j : Fin k) f, T j f - q j f ∈ filt q j) ∧
      ∀ (j : Fin k) Z f, T j (lie r (ws j) Z f) - lie r ds Z (T j f) ∈ filt q j := by
    refine ⟨fun j => avg (q j), fun j => avg_kRep (q j), fun j f =>
      avg_sub_self_mem (q j) _ (hstab j) (hq' j).1 f, fun j Z f => ?_⟩
    have h1 := lie_avg_sub_mem (q j) (filt q j) (hstab j) (fun Y f => by
      have := Submodule.neg_mem _ ((hq' j).2 Y f)
      rwa [neg_sub] at this) Z f
    have := Submodule.neg_mem _ h1
    rwa [neg_sub] at this
  -- the key induction
  have key : ∀ m, m ≤ k → ∀ G : KFin n (pre ++ ds ++ post),
      (∀ κ, sliceK h ha hr κ G ∈ filt q m) →
        G ∈ ⨆ (i : Fin k) (_ : (i : ℕ) < m),
          LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i)) := by
    intro m
    induction m with
    | zero =>
      intro _ G hG
      have hG0 : G = 0 := eq_zero_of_sliceK h ha hr G fun κ => by
        have := hG κ
        rwa [filt_zero, Submodule.mem_bot] at this
      rw [hG0]
      exact Submodule.zero_mem _
    | succ m ih =>
      intro hmk G hG
      have hm : m < k := by omega
      set j : Fin k := ⟨m, hm⟩ with hj
      have hN : ∀ v ∈ filt q (m + 1), ∃ u, T j u - v ∈ filt q m := by
        intro v hv
        obtain ⟨y, hy, z, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.mp (filt_succ_le q m hm hv)
        refine ⟨u, ?_⟩
        have e : T j u - (y + q j u) = (T j u - q j u) - y := by abel
        rw [e]
        exact Submodule.sub_mem _ (hTq j u) hy
      obtain ⟨G', hG', hGG'⟩ := exists_sub_mem_range_ind h ha hr hn (hws j) (T j) (hTk j)
        (filt q m) (filt q (m + 1)) (hstab m) (hstab (m + 1)) hN G hG
      have hG'm := ih (by omega) G' hG'
      have e : G = G' + (G - G') := by abel
      rw [e]
      refine Submodule.add_mem _ ?_ ?_
      · have hle : (⨆ (i : Fin k) (_ : (i : ℕ) < m),
            LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i))) ≤
            ⨆ (i : Fin k) (_ : (i : ℕ) < m + 1),
              LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i)) :=
          iSup₂_le fun i hi => le_iSup₂_of_le (f := fun (i : Fin k) (_ : (i : ℕ) < m + 1) =>
            LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i))) i (by omega) le_rfl
        exact hle hG'm
      · have hle : LinearMap.range (ind h ha hr (hws j) hn (T j) (hTk j)) ≤
            ⨆ (i : Fin k) (_ : (i : ℕ) < m + 1),
              LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i)) :=
          le_iSup₂_of_le (f := fun (i : Fin k) (_ : (i : ℕ) < m + 1) =>
            LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i))) j (by simp [hj]) le_rfl
        exact hle hGG'
  refine ⟨fun j => ind h ha hr (hws j) hn (T j) (hTk j), fun j => ?_, ?_⟩
  · refine isRealIntertwinerModulo_iff.mpr ⟨fun κ f => ?_, fun X f => ?_⟩
    · rw [ind_kRep, sub_self]
      exact Submodule.zero_mem _
    · exact key j j.isLt.le _ fun κ =>
        sliceK_ind_lie_sub_mem h ha hr (hws j) hn (hTk j) (filt q j) (hTl j) X f κ
  · rw [eq_top_iff]
    intro G _
    have hG := key k le_rfl G fun κ => by rw [filt_eq_top q htop]; exact Submodule.mem_top
    have hle : (⨆ (i : Fin k) (_ : (i : ℕ) < k),
        LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i))) ≤
        ⨆ j, LinearMap.range (ind h ha hr (hws j) hn (T j) (hTk j)) :=
      iSup₂_le fun i _ => le_iSup (fun i =>
        LinearMap.range (ind h ha hr (hws i) hn (T i) (hTk i))) i
    exact hle hG

end Stages

/-! ## The statement -/

/-- **Induction in stages of adjacent filtrations.** -/
theorem realAdjacentFiltrationInStages : RealAdjacentFiltrationInStagesStatement := by
  intro n pre post x y hn hf
  obtain ⟨k, ws, q, hws, hq, htop⟩ := hf
  have hwsr : ∀ j, realRank (ws j) = realRank [x, y] := by
    intro j
    rcases hws j with hj | ⟨hj, -⟩
    · rw [hj]
      simp only [realRank, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
    · rw [← length_realExponentSupport, hj.length_eq, length_realExponentSupport]
  have hL : pre ++ x :: y :: post = pre ++ [x, y] ++ post := by simp
  have hn' : realRank (pre ++ [x, y] ++ post) = n := hL ▸ hn
  have h : realRank pre + realRank [x, y] ≤ n := by
    rw [← hn', realRank_append', realRank_append']
    omega
  have e : ∀ j, ws j = [] ++ ws j ++ [] := fun j => (List.append_nil (ws j)).symm
  let q' : ∀ j, KFin (realRank [x, y]) (ws j) →ₗ[ℂ] KFin (realRank [x, y]) [x, y] := fun j =>
    q j ∘ₗ (LinearEquiv.ofEq _ _ (congrArg (KFin (realRank [x, y])) (e j))).toLinearMap
  have hrange : ∀ j, LinearMap.range (q' j) = LinearMap.range (q j) := fun j =>
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)
  have hq' : ∀ j, IsRealIntertwinerModulo (realRank [x, y]) (ws j) [x, y]
      (⨆ (i : Fin k) (_ : i < j), LinearMap.range (q' i)) (q' j) := by
    intro j
    simp only [hrange]
    exact isRealIntertwinerModulo_comp_ofEq (e j) (hq j)
  have htop' : ⨆ j, LinearMap.range (q' j) = ⊤ := by
    simp only [hrange]
    exact htop
  obtain ⟨Q, hQ, hQtop⟩ := exists_stages_filtration h rfl rfl hn' hwsr q' hq' htop'
  unfold RealAdjacentFiltration
  rw [hL]
  exact ⟨k, ws, Q, hws, hQ, hQtop⟩

end InductionStages

end Langlands.Archimedean
