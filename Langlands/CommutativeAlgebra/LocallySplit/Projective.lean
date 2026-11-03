import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Matrix.ToLin
import Langlands.CommutativeAlgebra.LocallySplit.Domination

/-! # Projectivity from dominated factorizations

A countably generated module with dominated factorizations is projective. Consequently, a
countably generated flat module that becomes locally split after a faithfully flat base change
is projective.

Main results:
* `projective_of_hasDominatedFactorizations`;
* `projective_of_locallySplit`;
* `projective_of_locallySplit_baseChange`. -/

universe u v

open TensorProduct

namespace Langlands.CommutativeAlgebra

section TransposeTrick

variable {R : Type u} [CommRing R]

/-- The transpose trick: if every tuple `ν` killed by all rows of `s` is killed by all rows of
`t`, then `t` factors through `s`. -/
theorem exists_eq_comp_of_forall_sum_smul_eq_zero {ι κ μ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (s : (ι → R) →ₗ[R] (κ → R)) (t : (ι → R) →ₗ[R] (μ → R))
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N] (ν : ι → N),
      (∀ j, ∑ i, s (Pi.single i 1) j • ν i = 0) → ∀ k, ∑ i, t (Pi.single i 1) k • ν i = 0) :
    ∃ U : (κ → R) →ₗ[R] (μ → R), t = U ∘ₗ s := by
  let W : Submodule R (ι → R) := Submodule.span R (Set.range fun j i => s (Pi.single i 1) j)
  have hsum : ∀ a : ι → R, ∑ i, a i • (Pi.single i 1 : ι → R) = a := by
    intro a
    ext i'
    simp [Finset.sum_apply, Pi.single_apply]
  have hq : ∀ a : ι → R, ∑ i, a i • W.mkQ (Pi.single i 1) = W.mkQ a := by
    intro a
    conv_rhs => rw [← hsum a]
    simp only [map_sum, map_smul]
  have hW := h ((ι → R) ⧸ W) (fun i => W.mkQ (Pi.single i 1)) (by
    intro j
    rw [hq]
    exact (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.subset_span ⟨j, rfl⟩))
  have hmem : ∀ k, (fun i => t (Pi.single i 1) k) ∈ W := by
    intro k
    have := hW k
    rw [hq] at this
    exact (Submodule.Quotient.mk_eq_zero W).mp this
  choose d hd using fun k => (Submodule.mem_span_range_iff_exists_fun R).mp (hmem k)
  refine ⟨Matrix.mulVecLin (Matrix.of d), ?_⟩
  refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
  ext k
  have := congrFun (hd k) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  rw [← this]
  simp [Matrix.mulVec, dotProduct]

end TransposeTrick

/-- A sequence of finite tuples `x l` in `M`, each written as `x l i = ∑ k, T l i k • x (l+1) k`
in terms of the next one with coefficients `T l` dominating `x l`, such that every element of `M`
lies in the span of `x l` for all large `l`. -/
structure DominatedChain (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] where
  /-- The length of the `l`-th tuple. -/
  n : ℕ → ℕ
  /-- The `l`-th tuple. -/
  x : ∀ l, Fin (n l) → M
  /-- The coefficients expressing the `l`-th tuple in terms of the next one. -/
  T : ∀ l, Fin (n l) → Fin (n (l + 1)) → R
  hx : ∀ l i, x l i = ∑ k, T l i k • x (l + 1) k
  hdom : ∀ l, Dominates.{u} (x l) (T l)
  hexh : ∀ (m : M) (l₀ : ℕ), ∃ l, l₀ ≤ l ∧ m ∈ Submodule.span R (Set.range (x l))

namespace DominatedChain

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (C : DominatedChain R M)

/-- The map `R^(n l) → M` given by the `l`-th tuple. -/
def H (l : ℕ) : (Fin (C.n l) → R) →ₗ[R] M := Fintype.linearCombination R (C.x l)

/-- The transition map `R^(n l) → R^(n (l+1))` given by the coefficients `T l`. -/
def t (l : ℕ) : (Fin (C.n l) → R) →ₗ[R] (Fin (C.n (l + 1)) → R) :=
  Fintype.linearCombination R (C.T l)

theorem H_apply (l : ℕ) (c : Fin (C.n l) → R) : C.H l c = ∑ i, c i • C.x l i := rfl

theorem t_apply (l : ℕ) (c : Fin (C.n l) → R) : C.t l c = ∑ i, c i • C.T l i := rfl

theorem H_single (l : ℕ) (i : Fin (C.n l)) : C.H l (Pi.single i 1) = C.x l i := by
  simp [H]

theorem t_single (l : ℕ) (i : Fin (C.n l)) : C.t l (Pi.single i 1) = C.T l i := by
  simp [t]

theorem H_succ_t (l : ℕ) (c : Fin (C.n l) → R) : C.H (l + 1) (C.t l c) = C.H l c := by
  rw [t_apply, map_sum, C.H_apply l c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, C.H_apply (l + 1) (C.T l i), ← C.hx l i]

/-- The kernel of `H l` is contained in the kernel of `t l` (domination tested against `R`). -/
theorem t_eq_zero_of_H_eq_zero {l : ℕ} {c : Fin (C.n l) → R} (hc : C.H l c = 0) :
    C.t l c = 0 := by
  have h0 : ∑ i, C.x l i ⊗ₜ[R] c i = 0 := by
    have : ∑ i, C.x l i ⊗ₜ[R] c i = C.H l c ⊗ₜ[R] (1 : R) := by
      rw [H_apply, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    rw [this, hc, TensorProduct.zero_tmul]
  have := C.hdom l R c h0
  ext k
  simpa [t_apply, Finset.sum_apply, mul_comm] using this k

/-- Stabilisation: `t l` factors through the two-step transition `t (l+1) ∘ t l`. -/
theorem exists_t_eq_comp (l : ℕ) :
    ∃ U : (Fin (C.n (l + 1 + 1)) → R) →ₗ[R] (Fin (C.n (l + 1)) → R),
      C.t l = U ∘ₗ (C.t (l + 1) ∘ₗ C.t l) := by
  classical
  apply exists_eq_comp_of_forall_sum_smul_eq_zero
  intro N _ _ ν hν k
  simp only [LinearMap.comp_apply] at hν
  have hx : ∀ i, C.x l i =
      ∑ j, (C.t (l + 1) (C.t l (Pi.single i 1))) j • C.x (l + 1 + 1) j := by
    intro i
    rw [← H_apply, H_succ_t, H_succ_t, H_single]
  have h0 : ∑ i, C.x l i ⊗ₜ[R] ν i = 0 := by
    simp_rw [hx, TensorProduct.sum_tmul, TensorProduct.smul_tmul]
    rw [Finset.sum_comm]
    simp_rw [← TensorProduct.tmul_sum, hν, TensorProduct.tmul_zero, Finset.sum_const_zero]
  simpa [t_single] using C.hdom l N ν h0 k

/-- A compatible family of maps `u j : R^(n (k+j)) → P` induces a map `M → P`. -/
theorem exists_lift (k : ℕ) {P : Type*} [AddCommGroup P] [Module R P]
    (u : ∀ j, (Fin (C.n (k + j)) → R) →ₗ[R] P) (hu : ∀ j, u (j + 1) ∘ₗ C.t (k + j) = u j) :
    ∃ z : M →ₗ[R] P, ∀ j c, z (C.H (k + j) c) = u j c := by
  have hu' : ∀ j c, u (j + 1) (C.t (k + j) c) = u j c := fun j c => LinearMap.congr_fun (hu j) c
  have push : ∀ i j (c : Fin (C.n (k + j)) → R), ∃ c' : Fin (C.n (k + (j + i))) → R,
      C.H (k + (j + i)) c' = C.H (k + j) c ∧ u (j + i) c' = u j c := by
    intro i
    induction i with
    | zero => intro j c; exact ⟨c, rfl, rfl⟩
    | succ i ih =>
      intro j c
      obtain ⟨c', h1, h2⟩ := ih j c
      exact ⟨C.t (k + (j + i)) c', (C.H_succ_t _ _).trans h1, (hu' _ _).trans h2⟩
  have push' : ∀ j j' (c : Fin (C.n (k + j)) → R), j ≤ j' → ∃ c' : Fin (C.n (k + j')) → R,
      C.H (k + j') c' = C.H (k + j) c ∧ u j' c' = u j c := by
    intro j j' c h
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    exact push i j c
  have hker : ∀ j c, C.H (k + j) c = 0 → u j c = 0 := by
    intro j c hc
    rw [← hu', C.t_eq_zero_of_H_eq_zero hc, map_zero]
  have hW : ∀ j c j' c', C.H (k + j) c = C.H (k + j') c' → u j c = u j' c' := by
    have key : ∀ j c j' c', j ≤ j' → C.H (k + j) c = C.H (k + j') c' → u j c = u j' c' := by
      intro j c j' c' hjj h
      obtain ⟨c'', h1, h2⟩ := push' j j' c hjj
      rw [← h2, ← sub_eq_zero, ← map_sub]
      apply hker
      rw [map_sub, h1, h, sub_self]
    intro j c j' c' h
    rcases le_total j j' with hjj | hjj
    · exact key j c j' c' hjj h
    · exact (key j' c' j c hjj h.symm).symm
  have hexh : ∀ m, ∃ j c, C.H (k + j) c = m := by
    intro m
    obtain ⟨l, hl, hm⟩ := C.hexh m k
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hl
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hm
    exact ⟨j, c, hc⟩
  choose jm cm hm using hexh
  refine ⟨{ toFun := fun m => u (jm m) (cm m), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro m₁ m₂
    obtain ⟨c₁, h₁, h₁'⟩ := push' (jm m₁) (max (jm m₁) (jm m₂)) (cm m₁) (le_max_left _ _)
    obtain ⟨c₂, h₂, h₂'⟩ := push' (jm m₂) (max (jm m₁) (jm m₂)) (cm m₂) (le_max_right _ _)
    rw [← h₁', ← h₂', ← map_add]
    apply hW
    rw [map_add, h₁, h₂, hm, hm, hm]
  · intro r m
    rw [RingHom.id_apply, ← map_smul]
    apply hW
    rw [map_smul, hm, hm]
  · intro j c
    exact hW _ _ _ _ (hm _)

/-- For every `l` there is `z : M → R^(n (l+1))` with `z ∘ H l = t l`. -/
theorem exists_z (l : ℕ) :
    ∃ z : M →ₗ[R] (Fin (C.n (l + 1)) → R), ∀ c, z (C.H l c) = C.t l c := by
  choose U hU using C.exists_t_eq_comp
  let w : ∀ j, (Fin (C.n (l + j + 1)) → R) →ₗ[R] (Fin (C.n (l + 1)) → R) := fun j =>
    Nat.rec (motive := fun j => (Fin (C.n (l + j + 1)) → R) →ₗ[R] (Fin (C.n (l + 1)) → R))
      LinearMap.id (fun j wj => wj ∘ₗ U (l + j)) j
  obtain ⟨z, hz⟩ := C.exists_lift l (fun j => w j ∘ₗ C.t (l + j)) (by
    intro j
    show ((w j ∘ₗ U (l + j)) ∘ₗ C.t (l + j + 1)) ∘ₗ C.t (l + j) = w j ∘ₗ C.t (l + j)
    simp only [LinearMap.comp_assoc]
    rw [← hU (l + j)])
  exact ⟨z, fun c => hz 0 c⟩

include C in
/-- The module of a dominated chain is projective: it is a direct summand of
`⨁ l, R^(n (l+1))`, via a telescoping sum of the maps `z l`. -/
theorem projective : Module.Projective R M := by
  classical
  choose z hz using C.exists_z
  let α : ℕ → M →ₗ[R] M := fun l => C.H (l + 1) ∘ₗ z l
  have hmono : Monotone fun l => LinearMap.range (C.H l) := by
    refine monotone_nat_of_le_succ fun l => ?_
    rintro _ ⟨c, rfl⟩
    exact ⟨C.t l c, C.H_succ_t l c⟩
  have hfix : ∀ l m, m ∈ LinearMap.range (C.H l) → α l m = m := by
    rintro l _ ⟨c, rfl⟩
    simp only [α, LinearMap.comp_apply, hz, H_succ_t]
  have hαα : ∀ l m, α (l + 1) (α l m) = α l m := fun l m => hfix (l + 1) _ ⟨z l m, rfl⟩
  let φ : ℕ → M →ₗ[R] Π₀ k : ℕ, (Fin (C.n (k + 1)) → R) := fun K =>
    DFinsupp.lsingle 0 ∘ₗ z 0 + ∑ k ∈ Finset.range K,
      DFinsupp.lsingle (k + 1) ∘ₗ z (k + 1) ∘ₗ (LinearMap.id - α k)
  let ψ : (Π₀ k : ℕ, (Fin (C.n (k + 1)) → R)) →ₗ[R] M := DFinsupp.lsum ℕ fun k => C.H (k + 1)
  have hφ0 : ∀ m, φ 0 m = DFinsupp.single 0 (z 0 m) := by
    intro m
    simp [φ]
  have hφsucc : ∀ K m, φ (K + 1) m = φ K m + DFinsupp.single (K + 1) (z (K + 1) (m - α K m)) := by
    intro K m
    simp [φ, Finset.sum_range_succ, add_assoc]
  have hψ : ∀ k x, ψ (DFinsupp.single k x) = C.H (k + 1) x := fun k x =>
    DFinsupp.lsum_single _ _ _ _
  have hψφ : ∀ K m, ψ (φ K m) = α K m := by
    intro K m
    induction K with
    | zero => rw [hφ0, hψ]; rfl
    | succ K ih =>
      rw [hφsucc, map_add, ih, hψ]
      change α K m + α (K + 1) (m - α K m) = α (K + 1) m
      rw [map_sub, hαα]
      abel
  have hstab : ∀ L m, m ∈ LinearMap.range (C.H L) → ∀ K, L ≤ K → φ K m = φ L m := by
    intro L m hm K hK
    induction K, hK using Nat.le_induction with
    | base => rfl
    | succ K hLK ih =>
      rw [hφsucc, hfix K m (hmono hLK hm), sub_self, map_zero, DFinsupp.single_zero, add_zero, ih]
  obtain ⟨Φ, hΦ⟩ := C.exists_lift 0 (fun j => φ j ∘ₗ C.H (0 + j)) (by
    intro j
    refine LinearMap.ext fun c => ?_
    change φ (j + 1) (C.H (0 + j + 1) (C.t (0 + j) c)) = φ j (C.H (0 + j) c)
    rw [C.H_succ_t, hstab (0 + j) _ ⟨c, rfl⟩ (j + 1) (by omega),
      hstab (0 + j) _ ⟨c, rfl⟩ j (by omega)])
  refine Module.Projective.of_split Φ ψ (LinearMap.ext fun m => ?_)
  obtain ⟨l, -, hl⟩ := C.hexh m 0
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.zero_le l)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hl
  change ψ (Φ (C.H (0 + j) c)) = C.H (0 + j) c
  rw [hΦ]
  change ψ (φ j (C.H (0 + j) c)) = C.H (0 + j) c
  rw [hψφ, hfix j _ (hmono (by omega) ⟨c, rfl⟩)]

/-- A module with dominated factorizations and a generating sequence `g` carries a dominated
chain: the `(l+1)`-st tuple is the factorization of `g l` adjoined to the `l`-th tuple. -/
theorem nonempty_of_hasDominatedFactorizations (h : HasDominatedFactorizations.{u} R M)
    (g : ℕ → M) (hg : Submodule.span R (Set.range g) = ⊤) : Nonempty (DominatedChain R M) := by
  choose mf Af yf hf using h
  let seq : ℕ → Σ p, Fin p → M := fun l => Nat.rec ⟨0, Fin.elim0⟩
    (fun l s => ⟨mf (s.1 + 1) (Matrix.vecCons (g l) s.2),
      yf (s.1 + 1) (Matrix.vecCons (g l) s.2)⟩) l
  have hx : ∀ l i, (seq l).2 i = ∑ k, Af ((seq l).1 + 1) (Matrix.vecCons (g l) (seq l).2) i.succ k
      • (seq (l + 1)).2 k := by
    intro l i
    have := (hf _ (Matrix.vecCons (g l) (seq l).2)).1 i.succ
    rwa [Matrix.cons_val_succ] at this
  have hmono : Monotone fun l => Submodule.span R (Set.range (seq l).2) := by
    refine monotone_nat_of_le_succ fun l => Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [hx l i]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hg' : ∀ l, g l ∈ Submodule.span R (Set.range (seq (l + 1)).2) := by
    intro l
    have := (hf _ (Matrix.vecCons (g l) (seq l).2)).1 0
    rw [Matrix.cons_val_zero] at this
    rw [this]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨{
    n := fun l => (seq l).1
    x := fun l => (seq l).2
    T := fun l i k => Af ((seq l).1 + 1) (Matrix.vecCons (g l) (seq l).2) i.succ k
    hx := hx
    hdom := ?_
    hexh := ?_ }⟩
  · intro l N _ _ ν hν k
    have h0 : ∑ i, Matrix.vecCons (g l) (seq l).2 i ⊗ₜ[R] (Matrix.vecCons 0 ν i : N) = 0 := by
      simpa [Fin.sum_univ_succ] using hν
    simpa [Fin.sum_univ_succ] using (hf _ (Matrix.vecCons (g l) (seq l).2)).2 N _ h0 k
  · intro m l₀
    have hm : m ∈ ⨆ l, Submodule.span R (Set.range (seq l).2) := by
      have : Submodule.span R (Set.range g) ≤ ⨆ l, Submodule.span R (Set.range (seq l).2) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨l, rfl⟩
        exact Submodule.mem_iSup_of_mem (l + 1) (hg' l)
      exact this (by rw [hg]; exact Submodule.mem_top)
    obtain ⟨l, hl⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hm
    exact ⟨max l l₀, le_max_right _ _, hmono (le_max_left _ _) hl⟩

end DominatedChain

section Projectivity

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A countably generated module with dominated factorizations is projective. -/
theorem projective_of_hasDominatedFactorizations
    (hM : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (h : HasDominatedFactorizations.{u} R M) : Module.Projective R M := by
  obtain ⟨s, hs, hspan⟩ := hM
  obtain ⟨g, hg⟩ := (hs.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
  have hg' : Submodule.span R (Set.range g) = ⊤ := by
    rw [← hg, Submodule.span_insert_zero, hspan]
  obtain ⟨C⟩ := DominatedChain.nonempty_of_hasDominatedFactorizations h g hg'
  exact C.projective

/-- A countably generated locally split module is projective. -/
theorem projective_of_locallySplit (hM : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (h : LocallySplit R M) : Module.Projective R M :=
  projective_of_hasDominatedFactorizations hM h.hasDominatedFactorizations

end Projectivity

/-- A countably generated flat module which becomes locally split after a faithfully flat base
change is projective. -/
theorem projective_of_locallySplit_baseChange {R R' M : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [Module.FaithfullyFlat R R'] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hM : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (h : LocallySplit R' (R' ⊗[R] M)) : Module.Projective R M :=
  projective_of_hasDominatedFactorizations hM
    (hasDominatedFactorizations_of_baseChange h.hasDominatedFactorizations)

end Langlands.CommutativeAlgebra
