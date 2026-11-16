import Langlands.Representation.Archimedean.LowerVermaFiltration

/-!
# The Hom bound for lower Verma modules of `𝔤𝔩_n(ℂ)`

`lowerVermaHomBound : VermaGL.LowerVermaHomBoundStatement`. See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaPBW

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping

/-! ## The representation on `Hom(W, M⁻(λ))` -/

section HomSpace

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)

/-- The representation `(Y · G)(w) = Y · G(w) - G(σ(Y) w)` of `𝔤𝔩_n(ℂ)` on
`Hom(W, M⁻(λ))`: the Library's `BGChase.homLie` for `σ` and the action on `M⁻(λ)`. -/
abbrev rhoH : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆
    Module.End ℂ (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) :=
  BGChase.homLie σ (VermaGL.action n lam)

theorem rhoH_apply (Y : Matrix (Fin n) (Fin n) ℂ) (G : Wt →ₗ[ℂ] VermaGL.LowerVerma n lam)
    (w : Wt) :
    rhoH n lam σ Y G w = UniversalEnvelopingAlgebra.ι ℂ Y • G w - G (σ Y w) := rfl

end HomSpace

/-! ## A weight basis of `W` and the filtration of `Hom(W, M⁻(λ))` -/

section Filtration

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)
  {D : ℕ} (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ)

variable (hb : ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k)

theorem eq_sum_smulRight (G : Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) :
    G = ∑ j, (b.coord j).smulRight (G (b j)) :=
  BGChase.eq_sum_coord_smulRight b G

theorem rhoH_smulRight (c : Idx n) (j : Fin D) (x : VermaGL.LowerVerma n lam) :
    rhoH n lam σ (unitE n c) ((b.coord j).smulRight x) =
      (b.coord j).smulRight (UniversalEnvelopingAlgebra.ι ℂ (unitE n c) • x) -
        ∑ i, b.coord j (σ (unitE n c) (b i)) • (b.coord i).smulRight x := by
  ext w
  have hf := b.sum_dual_apply_smul_coord (b.coord j ∘ₗ σ (unitE n c))
  have hw' : b.coord j (σ (unitE n c) w) =
      ∑ i, b.coord j (σ (unitE n c) (b i)) * b.coord i w := by
    have h := LinearMap.congr_fun hf w
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      smul_eq_mul] at h
    exact h.symm
  rw [rhoH_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply,
    smul_comm, LinearMap.sum_apply]
  congr 1
  rw [hw', Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_smul]

/-- The map `w ↦ b_k^*(w) · gen`. -/
def Gk (k : Fin D) : Wt →ₗ[ℂ] VermaGL.LowerVerma n lam := (b.coord k).smulRight (VermaGL.gen n lam)

include hb in
theorem isWt_Gk (k : Fin D) : IsWt n (rhoH n lam σ) (Gk n lam b k) (lam - wtC n m k) := by
  intro p
  ext w
  rw [Gk, rhoH_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply, smul_comm,
    show UniversalEnvelopingAlgebra.ι ℂ (unitE n (p, p)) • VermaGL.gen n lam =
      lam p • VermaGL.gen n lam from unitU_smul_gen n lam p,
    coord_unitE_diag n σ b m hb, LinearMap.smul_apply, LinearMap.smulRight_apply, Pi.sub_apply,
    smul_smul, smul_smul, ← sub_smul, wtC]
  congr 1
  ring

theorem rhoH_Gk_lower (k : Fin D) {p q : Fin n} (hqp : q < p) :
    rhoH n lam σ (unitE n (p, q)) (Gk n lam b k) =
      -∑ i, b.coord k (σ (unitE n (p, q)) (b i)) • Gk n lam b i := by
  rw [Gk, rhoH_smulRight]
  have h0 : UniversalEnvelopingAlgebra.ι ℂ (unitE n (p, q)) • VermaGL.gen n lam = 0 := by
    have h := unitE_lo_smul_gen n lam 0 ⟨(p, q), not_lt.mpr hqp.le⟩
    rw [vVal_of_lt n lam 0 hqp, zero_smul] at h
    exact h
  rw [h0]
  simp [Gk]

/-- The generators `E_{c₁} ⋯ E_{c_r} · G_j`, `j ∈ T`. -/
abbrev gensT (T : Finset (Fin D)) : Set (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) :=
  gensG n (rhoH n lam σ) (Gk n lam b) T

/-- The filtration step `F_T`. -/
abbrev FT (T : Finset (Fin D)) : Submodule ℂ (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) :=
  FG n (rhoH n lam σ) (Gk n lam b) T

theorem isInv_FT (T : Finset (Fin D)) : IsInv n (rhoH n lam σ) (FT n lam σ b T) :=
  isInv_FG n _ _ T

include hb in
theorem isWt_gensT {T : Finset (Fin D)} {v : Wt →ₗ[ℂ] VermaGL.LowerVerma n lam}
    (hv : v ∈ gensT n lam σ b T) : ∃ μ, IsWt n (rhoH n lam σ) v μ :=
  isWt_gensG n _ _ (fun j => lam - wtC n m j) (isWt_Gk n lam σ b m hb) hv

theorem FT_mono {T T' : Finset (Fin D)} (h : T ⊆ T') : FT n lam σ b T ≤ FT n lam σ b T' :=
  FG_mono n _ _ h

theorem Gk_mem_FT {T : Finset (Fin D)} {j : Fin D} (hj : j ∈ T) :
    Gk n lam b j ∈ FT n lam σ b T :=
  G_mem_FG n _ _ hj

theorem smulRight_W_mem_FT (l : List (Idx n)) (j : Fin D) :
    (b.coord j).smulRight (W n l • VermaGL.gen n lam) ∈ FT n lam σ b Finset.univ := by
  induction l generalizing j with
  | nil =>
    rw [W_nil, one_smul]
    exact Gk_mem_FT n lam σ b (Finset.mem_univ j)
  | cons c l ih =>
    rw [W_cons, mul_smul]
    have h := rhoH_smulRight n lam σ b c j (W n l • VermaGL.gen n lam)
    rw [eq_sub_iff_add_eq] at h
    rw [← h]
    refine Submodule.add_mem _ ?_ ?_
    · exact isInv_FT n lam σ b _ c _ (ih j)
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ih i)

theorem smulRight_mem_FT (j : Fin D) (x : VermaGL.LowerVerma n lam) :
    (b.coord j).smulRight x ∈ FT n lam σ b Finset.univ := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_smul_gen]
  have hu' : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [basisU_apply]
    exact smulRight_W_mem_FT n lam σ b _ j
  | zero =>
    have h0 : (b.coord j).smulRight ((0 : VermaGL.glU n) • VermaGL.gen n lam) = 0 := by
      ext w
      simp
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have h : (b.coord j).smulRight ((x + y) • VermaGL.gen n lam) =
        (b.coord j).smulRight (x • VermaGL.gen n lam) +
          (b.coord j).smulRight (y • VermaGL.gen n lam) := by
      ext w
      simp [add_smul, smul_add]
    rw [h]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h : (b.coord j).smulRight ((a • x) • VermaGL.gen n lam) =
        a • (b.coord j).smulRight (x • VermaGL.gen n lam) := by
      ext w
      rw [LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_assoc,
        smul_comm (b.coord j w) a]
    rw [h]
    exact Submodule.smul_mem _ a hx

theorem FT_univ : FT n lam σ b Finset.univ = ⊤ := by
  refine eq_top_iff.mpr fun G _ => ?_
  rw [eq_sum_smulRight n lam b G]
  exact Submodule.sum_mem _ fun j _ => smulRight_mem_FT n lam σ b j _

end Filtration

/-! ## The step of the filtration -/

section Step

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)
  {D : ℕ} (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ)
  (hb : ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k)

/-- The singular vectors of weight `λ` in `Hom(W, M⁻(λ))`. -/
def Ssing : Submodule ℂ (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) where
  carrier := {G | (∀ p q : Fin n, q < p → rhoH n lam σ (unitE n (p, q)) G = 0) ∧
    IsWt n (rhoH n lam σ) G lam}
  add_mem' := by
    rintro G G' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun p q hqp => by rw [map_add, h1 p q hqp, h1' p q hqp, add_zero], fun p => ?_⟩
    rw [map_add, h2 p, h2' p, smul_add]
  zero_mem' := ⟨fun p q _ => map_zero _, fun p => by rw [map_zero, smul_zero]⟩
  smul_mem' := by
    rintro a G ⟨h1, h2⟩
    refine ⟨fun p q hqp => by rw [map_smul, h1 p q hqp, smul_zero], fun p => ?_⟩
    rw [map_smul, h2 p, smul_comm]

variable {T : Finset (Fin D)} {k : Fin D} (hk : k ∈ T)
  (hT : ∀ j, htZ n m k < htZ n m j → j ∈ T)

include hb hk hT in
theorem rhoH_Gk_lower_mem {p q : Fin n} (hqp : q < p) :
    rhoH n lam σ (unitE n (p, q)) (Gk n lam b k) ∈ FT n lam σ b (T.erase k) := by
  rw [rhoH_Gk_lower n lam σ b k hqp]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => ?_)
  by_cases h : b.coord k (σ (unitE n (p, q)) (b i)) = 0
  · rw [h, zero_smul]
    exact Submodule.zero_mem _
  · have hw := wtC_eq_of_lower_coeff n σ b m hb (p, q) h
    have hlt := htZ_lt_of_wtC_eq n m hqp hw
    have hiT : i ∈ T.erase k := Finset.mem_erase.mpr ⟨fun hik => by subst hik; omega, hT i hlt⟩
    exact Submodule.smul_mem _ _ (Gk_mem_FT n lam σ b hiT)

include hb hk hT in
theorem env_lower_mem (l : List (Idx n)) (hl : ∀ c ∈ l, ¬ c.1 < c.2) :
    envelopingAction (rhoH n lam σ) (W n l) (Gk n lam b k) ∈
      FT n lam σ b (T.erase k) ⊔ ℂ ∙ Gk n lam b k :=
  envG_lower_mem n _ _ (fun j => lam - wtC n m j) (isWt_Gk n lam σ b m hb)
    (fun _ _ hqp => rhoH_Gk_lower_mem n lam σ b m hb hk hT hqp) l hl

/-- The span of the upper words applied to `G_k`. -/
abbrev Pk (k : Fin D) : Submodule ℂ (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) :=
  PG n (rhoH n lam σ) (Gk n lam b) k

include hb hk hT in
theorem env_mem_sup (u : VermaGL.glU n) :
    envelopingAction (rhoH n lam σ) u (Gk n lam b k) ∈
      FT n lam σ b (T.erase k) ⊔ Pk n lam σ b k :=
  envG_mem_sup n _ _ (fun j => lam - wtC n m j) (isWt_Gk n lam σ b m hb)
    (fun _ _ hqp => rhoH_Gk_lower_mem n lam σ b m hb hk hT hqp) u

include hb hk hT in
theorem FT_le_sup : FT n lam σ b T ≤ FT n lam σ b (T.erase k) ⊔ Pk n lam σ b k :=
  FG_le_sup n _ _ (fun j => lam - wtC n m j) (isWt_Gk n lam σ b m hb)
    (fun _ _ hqp => rhoH_Gk_lower_mem n lam σ b m hb hk hT hqp)

include hb hk hT in
/-- **The step.** A singular vector of weight `λ` in `F_T` lies in `F_{T∖k} + ℂ G_k`, and even
in `F_{T∖k}` unless `G_k` has weight `λ`. -/
theorem step (hZ : VermaGL.IsZExtremal n lam) {x : Wt →ₗ[ℂ] VermaGL.LowerVerma n lam}
    (hxS : x ∈ Ssing n lam σ) (hxT : x ∈ FT n lam σ b T) :
    x ∈ FT n lam σ b (T.erase k) ⊔ ℂ ∙ Gk n lam b k ∧
      (wtC n m k ≠ 0 → x ∈ FT n lam σ b (T.erase k)) := by
  set F' := FT n lam σ b (T.erase k) with hF'
  set s₂ : Set (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) := {v | ∃ l : List (Idx n),
    (∀ c ∈ l, c.1 < c.2) ∧ v = envelopingAction (rhoH n lam σ) (W n l) (Gk n lam b k)}
  have hx1 : x ∈ Submodule.span ℂ (gensT n lam σ b (T.erase k) ∪ s₂) := by
    rw [Submodule.span_union]
    exact FT_le_sup n lam σ b m hb hk hT hxT
  have hx2 := mem_span_wt n (rhoH n lam σ) (fun v hv => by
      rcases hv with hv | ⟨l, -, rfl⟩
      · exact isWt_gensT n lam σ b m hb hv
      · exact ⟨_, isWt_env_W n _ (isWt_Gk n lam σ b m hb k) l⟩) hx1 hxS.2
  set Q : Set (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) := {v | ∃ l : List (Idx n),
    (∀ c ∈ l, c.1 < c.2) ∧ shiftOf n l = wtC n m k ∧
      v = envelopingAction (rhoH n lam σ) (W n l) (Gk n lam b k)}
  have hx3 : x ∈ F' ⊔ Submodule.span ℂ Q := by
    refine (Submodule.span_le.mpr ?_) hx2
    rintro v ⟨hv | ⟨l, hl, rfl⟩, hvw⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span hv)
    · by_cases h0 : envelopingAction (rhoH n lam σ) (W n l) (Gk n lam b k) = 0
      · rw [h0]
        exact Submodule.zero_mem _
      · have hu := isWt_unique n _ (isWt_env_W n _ (isWt_Gk n lam σ b m hb k) l) hvw h0
        have hsh : shiftOf n l = wtC n m k := by
          calc shiftOf n l = ((lam - wtC n m k) + shiftOf n l) - (lam - wtC n m k) := by abel
            _ = lam - (lam - wtC n m k) := by rw [hu]
            _ = wtC n m k := by abel
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨l, hl, hsh, rfl⟩)
  have part2 : wtC n m k ≠ 0 → x ∈ F' := by
    intro hk0
    by_cases hQ : ∃ l : List (Idx n), (∀ c ∈ l, c.1 < c.2) ∧ shiftOf n l = wtC n m k
    · obtain ⟨l₀, hl₀, hsh₀⟩ := hQ
      have hcone : lam - (lam - wtC n m k) ∈ VermaGL.posRootCone n := by
        rw [sub_sub_cancel, ← hsh₀]
        exact shiftOf_mem_posRootCone n hl₀
      have hne : lam - wtC n m k ≠ lam := fun h => hk0 (by
        have := congrArg (fun f => lam - f) h
        simpa using this)
      obtain ⟨z, hz, c, hzl, hzμ⟩ := hZ (lam - wtC n m k) hcone hne
      obtain ⟨c', hc'⟩ := center_smul_gen n (lam - wtC n m k) hz
      have hcc : c - c' ≠ 0 := fun h => hzμ (by rw [hc', sub_eq_zero.mp h])
      have hxz : envelopingAction (rhoH n lam σ) z x = c • x := by
        have h := env_center_sub_mem n (rhoH n lam σ) (isInv_bot n _) lam x
          (fun p q hqp => by rw [hxS.1 p q hqp]; exact Submodule.zero_mem _)
          (fun p => by rw [hxS.2 p, sub_self]; exact Submodule.zero_mem _) hzl
        rw [Submodule.mem_bot, sub_eq_zero] at h
        exact h
      have hGz : envelopingAction (rhoH n lam σ) z (Gk n lam b k) - c' • Gk n lam b k ∈ F' :=
        env_center_sub_mem n (rhoH n lam σ) (isInv_FT n lam σ b _) (lam - wtC n m k) _
          (fun p q hqp => rhoH_Gk_lower_mem n lam σ b m hb hk hT hqp)
          (fun p => by rw [isWt_Gk n lam σ b m hb k p, sub_self]; exact Submodule.zero_mem _) hc'
      have hcomm : ∀ u : VermaGL.glU n, envelopingAction (rhoH n lam σ) z
          (envelopingAction (rhoH n lam σ) u (Gk n lam b k)) =
            envelopingAction (rhoH n lam σ) u (envelopingAction (rhoH n lam σ) z (Gk n lam b k)) := by
        intro u
        rw [← Module.End.mul_apply, ← map_mul, ← Subalgebra.mem_center_iff.mp hz u, map_mul,
          Module.End.mul_apply]
      have hy : ∀ y ∈ Submodule.span ℂ Q, envelopingAction (rhoH n lam σ) z y - c' • y ∈ F' := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨l, -, -, rfl⟩ := hv
          rw [hcomm, ← map_smul, ← map_sub]
          exact env_W_mem n _ (isInv_FT n lam σ b _) l hGz
        | zero => rw [map_zero, smul_zero, sub_zero]; exact Submodule.zero_mem _
        | add y y' _ _ hy hy' =>
          rw [map_add, smul_add, add_sub_add_comm]
          exact Submodule.add_mem _ hy hy'
        | smul a y _ hy =>
          have h := Submodule.smul_mem _ a hy
          rw [smul_sub, smul_comm a c' y, ← map_smul] at h
          exact h
      obtain ⟨f, hf, y, hyQ, rfl⟩ := Submodule.mem_sup.mp hx3
      have hmem0 : envelopingAction (rhoH n lam σ) z (f + y) - c' • (f + y) ∈ F' := by
        rw [map_add, smul_add, add_sub_add_comm]
        exact Submodule.add_mem _ (Submodule.sub_mem _ (env_mem n _ (isInv_FT n lam σ b _) z hf)
          (Submodule.smul_mem _ _ hf)) (hy y hyQ)
      have hmem : (c - c') • (f + y) ∈ F' := by
        rw [hxz, show c • (f + y) - c' • (f + y) = (c - c') • (f + y) from
          (sub_smul c c' (f + y)).symm] at hmem0
        exact hmem0
      exact (Submodule.smul_mem_iff _ hcc).mp hmem
    · have hQe : Submodule.span ℂ Q = ⊥ := by
        rw [Submodule.span_eq_bot]
        rintro v ⟨l, hl, hsh, rfl⟩
        exact absurd ⟨l, hl, hsh⟩ hQ
      rw [hQe, sup_bot_eq] at hx3
      exact hx3
  refine ⟨?_, part2⟩
  by_cases hk0 : wtC n m k = 0
  · have hQ : Submodule.span ℂ Q ≤ ℂ ∙ Gk n lam b k := by
      refine Submodule.span_le.mpr ?_
      rintro v ⟨l, hl, hsh, rfl⟩
      rw [hk0] at hsh
      rw [eq_nil_of_shiftOf_eq_zero n hl hsh, W_nil, map_one, Module.End.one_apply]
      exact Submodule.mem_span_singleton_self _
    exact (sup_le_sup_left hQ _) hx3
  · exact Submodule.mem_sup_left (part2 hk0)

end Step

/-! ## Counting -/

section Count

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)
  {D : ℕ} (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ)
  (hb : ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k)

include hb in
/-- The singular vectors of weight `λ` in `F_T` form a finite-dimensional space of dimension at
most the number of `k ∈ T` with `b k` of weight `0`, for every upward closed `T`. -/
theorem count (hZ : VermaGL.IsZExtremal n lam) : ∀ T : Finset (Fin D),
    (∀ i ∈ T, ∀ j, htZ n m i < htZ n m j → j ∈ T) →
      FiniteDimensional ℂ (Ssing n lam σ ⊓ FT n lam σ b T : Submodule ℂ _) ∧
        Module.finrank ℂ (Ssing n lam σ ⊓ FT n lam σ b T : Submodule ℂ _) ≤
          (T.filter fun k => wtC n m k = 0).card := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hup
  rcases T.eq_empty_or_nonempty with rfl | hne
  · have h0 : FT n lam σ b ∅ = ⊥ := FG_empty n _ _
    rw [h0, inf_bot_eq]
    exact ⟨inferInstance, by simp⟩
  · obtain ⟨k, hk, hmin⟩ := T.exists_min_image (htZ n m) hne
    have hT : ∀ j, htZ n m k < htZ n m j → j ∈ T := hup k hk
    have hupT' : ∀ i ∈ T.erase k, ∀ j, htZ n m i < htZ n m j → j ∈ T.erase k := by
      intro i hi j hij
      have hiT := Finset.mem_of_mem_erase hi
      refine Finset.mem_erase.mpr ⟨fun hjk => ?_, hup i hiT j hij⟩
      subst hjk
      have := hmin i hiT
      omega
    obtain ⟨ihfd, ihle⟩ := ih (T.erase k) (Finset.erase_ssubset hk) hupT'
    by_cases hall : ∀ x ∈ Ssing n lam σ ⊓ FT n lam σ b T, x ∈ FT n lam σ b (T.erase k)
    · have heq : Ssing n lam σ ⊓ FT n lam σ b T = Ssing n lam σ ⊓ FT n lam σ b (T.erase k) :=
        le_antisymm (fun x hx => ⟨hx.1, hall x hx⟩)
          (inf_le_inf_left _ (FT_mono n lam σ b (Finset.erase_subset k T)))
      rw [heq]
      exact ⟨ihfd, ihle.trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.erase_subset k T)))⟩
    · push Not at hall
      obtain ⟨x₀, hx₀, hx₀'⟩ := hall
      have hst₀ := step n lam σ b m hb hk hT hZ hx₀.1 hx₀.2
      have hk0 : wtC n m k = 0 := by
        by_contra h
        exact hx₀' (hst₀.2 h)
      have hle : Ssing n lam σ ⊓ FT n lam σ b T ≤
          (Ssing n lam σ ⊓ FT n lam σ b (T.erase k)) ⊔ ℂ ∙ x₀ := by
        intro x hx
        obtain ⟨f, hf, g, hg, hfg⟩ :=
          Submodule.mem_sup.mp (step n lam σ b m hb hk hT hZ hx.1 hx.2).1
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
        obtain ⟨f₀, hf₀, g₀, hg₀, hfg₀⟩ := Submodule.mem_sup.mp hst₀.1
        obtain ⟨a₀, rfl⟩ := Submodule.mem_span_singleton.mp hg₀
        have ha₀ : a₀ ≠ 0 := by
          rintro rfl
          apply hx₀'
          rw [← hfg₀, zero_smul, add_zero]
          exact hf₀
        have hdiff : x - (a / a₀) • x₀ = f - (a / a₀) • f₀ := by
          rw [← hfg, ← hfg₀, smul_add, smul_smul, div_mul_cancel₀ a ha₀]
          abel
        refine Submodule.mem_sup.mpr ⟨x - (a / a₀) • x₀, ⟨Submodule.sub_mem _ hx.1
          (Submodule.smul_mem _ _ hx₀.1), ?_⟩, (a / a₀) • x₀,
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩
        rw [hdiff]
        exact Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hf₀)
      have hx₀ne : x₀ ≠ 0 := fun h => hx₀' (h ▸ Submodule.zero_mem _)
      have := ihfd
      refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
      calc Module.finrank ℂ (Ssing n lam σ ⊓ FT n lam σ b T : Submodule ℂ _)
          ≤ Module.finrank ℂ
              ((Ssing n lam σ ⊓ FT n lam σ b (T.erase k)) ⊔ ℂ ∙ x₀ : Submodule ℂ _) :=
            Submodule.finrank_mono hle
        _ ≤ Module.finrank ℂ (Ssing n lam σ ⊓ FT n lam σ b (T.erase k) : Submodule ℂ _) +
            Module.finrank ℂ (ℂ ∙ x₀) := Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ ((T.erase k).filter fun k => wtC n m k = 0).card + 1 := by
            rw [finrank_span_singleton hx₀ne]
            omega
        _ = (T.filter fun k => wtC n m k = 0).card := by
            rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hk, hk0⟩)]
            have : 0 < (T.filter fun k => wtC n m k = 0).card :=
              Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hk0⟩⟩
            omega

include hb in
theorem card_zero_le_finrank [FiniteDimensional ℂ Wt] :
    (Finset.univ.filter fun k => wtC n m k = 0).card ≤
      Module.finrank ℂ (VermaGL.zeroWeightSpace σ) := by
  classical
  let f : {k : Fin D // wtC n m k = 0} → VermaGL.zeroWeightSpace σ := fun k => ⟨b k.1, by
    simp only [VermaGL.zeroWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro p
    have h := hb k.1 p
    have h0 : (m k.1 p : ℂ) = 0 := congrFun k.2 p
    rw [h0, zero_smul] at h
    exact h⟩
  have hli : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp (VermaGL.zeroWeightSpace σ).subtype
    exact b.linearIndependent.comp _ Subtype.val_injective
  have h := hli.fintype_card_le_finrank
  rwa [Fintype.card_subtype] at h

end Count

/-! ## Equivariant maps `W → End M⁻(λ)` -/

section Equivariant

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)

/-- The equivariant maps `g : W → End M⁻(λ)`, `g(σ(Y) w) = [Y, g(w)]`. -/
def equivSub : Submodule ℂ (Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)) where
  carrier := {g | ∀ Y w, g (σ Y w) =
    VermaGL.action n lam Y * g w - g w * VermaGL.action n lam Y}
  add_mem' := by
    intro g g' hg hg' Y w
    simp only [LinearMap.add_apply, hg Y w, hg' Y w, mul_add, add_mul]
    abel
  zero_mem' := by
    intro Y w
    simp
  smul_mem' := by
    intro a g hg Y w
    simp only [LinearMap.smul_apply, hg Y w, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Evaluation at the generator: `g ↦ (w ↦ g(w) gen)`. -/
def evalGen : (Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)) →ₗ[ℂ]
    (Wt →ₗ[ℂ] VermaGL.LowerVerma n lam) :=
  LinearMap.llcomp ℂ Wt (Module.End ℂ (VermaGL.LowerVerma n lam)) (VermaGL.LowerVerma n lam)
    (LinearMap.applyₗ (VermaGL.gen n lam))

theorem evalGen_apply (g : Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)) (w : Wt) :
    evalGen n lam g w = g w (VermaGL.gen n lam) := rfl

theorem rhoH_evalGen {g : Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)}
    (hg : g ∈ equivSub n lam σ) (Y : Matrix (Fin n) (Fin n) ℂ) (w : Wt) :
    rhoH n lam σ Y (evalGen n lam g) w =
      g w (UniversalEnvelopingAlgebra.ι ℂ Y • VermaGL.gen n lam) := by
  rw [rhoH_apply, evalGen_apply, evalGen_apply, hg Y w, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply]
  change _ - (UniversalEnvelopingAlgebra.ι ℂ Y • g w (VermaGL.gen n lam) -
    g w (UniversalEnvelopingAlgebra.ι ℂ Y • VermaGL.gen n lam)) = _
  abel

theorem evalGen_mem_Ssing {g : Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)}
    (hg : g ∈ equivSub n lam σ) : evalGen n lam g ∈ Ssing n lam σ := by
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · refine LinearMap.ext fun w => ?_
    have h0 : UniversalEnvelopingAlgebra.ι ℂ (unitE n (p, q)) • VermaGL.gen n lam = 0 := by
      have h := unitE_lo_smul_gen n lam 0 ⟨(p, q), not_lt.mpr hqp.le⟩
      rw [vVal_of_lt n lam 0 hqp, zero_smul] at h
      exact h
    rw [rhoH_evalGen n lam σ hg, h0, map_zero, LinearMap.zero_apply]
  · refine LinearMap.ext fun w => ?_
    rw [rhoH_evalGen n lam σ hg, LinearMap.smul_apply, evalGen_apply,
      show UniversalEnvelopingAlgebra.ι ℂ (unitE n (p, p)) • VermaGL.gen n lam =
        lam p • VermaGL.gen n lam from unitU_smul_gen n lam p, map_smul]

theorem eq_zero_of_evalGen {g : Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)}
    (hg : g ∈ equivSub n lam σ) (hg0 : evalGen n lam g = 0) : g = 0 := by
  have h0 : ∀ w, g w (VermaGL.gen n lam) = 0 := fun w => by
    rw [← evalGen_apply, hg0, LinearMap.zero_apply]
  have hW : ∀ (l : List (Idx n)) (w : Wt), g w (W n l • VermaGL.gen n lam) = 0 := by
    intro l
    induction l with
    | nil => intro w; rw [W_nil, one_smul]; exact h0 w
    | cons c l ih =>
      intro w
      rw [W_cons, mul_smul]
      have h := congrArg (fun T : Module.End ℂ (VermaGL.LowerVerma n lam) =>
        T (W n l • VermaGL.gen n lam)) (hg (unitE n c) w)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      rw [ih (σ (unitE n c) w), ih w, map_zero, zero_sub, eq_comm, neg_eq_zero] at h
      exact h
  refine LinearMap.ext fun w => LinearMap.ext fun x => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_smul_gen, LinearMap.zero_apply, LinearMap.zero_apply]
  have hu : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [basisU_apply]
    exact hW _ w
  | zero => rw [zero_smul, map_zero]
  | add x y _ _ hx hy => rw [add_smul, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_assoc, map_smul, hx, smul_zero]

end Equivariant

/-! ## The Hom bound -/

universe uW

theorem linearIndependent_evalGen (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt]
    [Module ℂ Wt] (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt) {d : ℕ}
    (g : Fin d → (Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)))
    (hgE : ∀ i, g i ∈ equivSub n lam σ) (hli : LinearIndependent ℂ g) :
    LinearIndependent ℂ (⇑(evalGen n lam) ∘ g) := by
  have hmem : ∀ z : Fin d →₀ ℂ, Finsupp.linearCombination ℂ g z ∈ equivSub n lam σ := by
    intro z
    have hz : Finsupp.linearCombination ℂ g z ∈ Submodule.span ℂ (Set.range g) := by
      rw [← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ z
    refine (Submodule.span_le.mpr ?_) hz
    rintro _ ⟨i, rfl⟩
    exact hgE i
  have hinj : ∀ z : Fin d →₀ ℂ,
      Finsupp.linearCombination ℂ (⇑(evalGen n lam) ∘ g) z = 0 → z = 0 := by
    intro z hz
    rw [← Finsupp.apply_linearCombination] at hz
    have h0 := eq_zero_of_evalGen n lam σ (hmem z) hz
    exact hli (h0.trans (map_zero _).symm)
  exact (injective_iff_map_eq_zero _).mpr hinj

theorem finrank_le_of_equivariant (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt]
    [Module ℂ Wt] (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)
    (hfd : FiniteDimensional ℂ (Ssing n lam σ)) {d : ℕ}
    (g : Fin d → (Wt →ₗ[ℂ] Module.End ℂ (VermaGL.LowerVerma n lam)))
    (hgE : ∀ i, g i ∈ equivSub n lam σ) (hli : LinearIndependent ℂ g) :
    d ≤ Module.finrank ℂ (Ssing n lam σ) := by
  have hli' := linearIndependent_evalGen n lam σ g hgE hli
  let v : Fin d → Ssing n lam σ := fun i =>
    ⟨evalGen n lam (g i), evalGen_mem_Ssing n lam σ (hgE i)⟩
  have hcomp : ⇑(Ssing n lam σ).subtype ∘ v = ⇑(evalGen n lam) ∘ g := funext fun i => rfl
  rw [← hcomp] at hli'
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp (Ssing n lam σ).subtype hli'
  have h1 := hv.fintype_card_le_finrank
  rwa [Fintype.card_fin] at h1

/-- **The Hom bound for lower Verma modules.** -/
theorem lowerVermaHomBound : VermaGL.LowerVermaHomBoundStatement.{uW} := by
  intro n lam hZ Wt _ _ _ σ hσ d g hg hli
  obtain ⟨D, b, m, hb⟩ := exists_weight_basis n σ hσ
  have hc := count n lam σ b m hb hZ Finset.univ (fun _ _ j _ => Finset.mem_univ j)
  rw [FT_univ, inf_top_eq] at hc
  obtain ⟨hfd, hcard⟩ := hc
  have h1 := finrank_le_of_equivariant n lam σ hfd g (fun i Y w => hg i Y w) hli
  exact h1.trans (hcard.trans (card_zero_le_finrank n σ b m hb))

end Langlands.Archimedean.VermaPBW
