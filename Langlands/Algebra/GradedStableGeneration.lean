import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Polynomial.Basic

/-! # Bounded generation of stable families of submodules -/

universe u v

open DirectSum

namespace Langlands.Algebra.GradedStableGeneration

variable {C : Type u} [CommRing C] {N : ℕ → Type v}
  [∀ n, AddCommGroup (N n)] [∀ n, Module C (N n)]

/-- The endomorphism of `⨁ n, N n` raising degrees by one through the maps `t n`. -/
noncomputable def total (t : ∀ n, N n →ₗ[C] N (n + 1)) : Module.End C (⨁ n, N n) :=
  DirectSum.toModule C ℕ _ fun n => (DirectSum.lof C ℕ N (n + 1)).comp (t n)

theorem total_lof (t : ∀ n, N n →ₗ[C] N (n + 1)) (n : ℕ) (x : N n) :
    total t (DirectSum.lof C ℕ N n x) = DirectSum.lof C ℕ N (n + 1) (t n x) :=
  DirectSum.toModule_lof C n x

theorem lof_apply_self (n : ℕ) (x : N n) : (DirectSum.lof C ℕ N n x) n = x :=
  DirectSum.of_eq_same n x

theorem lof_apply_of_ne {n m : ℕ} (x : N n) (h : m ≠ n) : (DirectSum.lof C ℕ N n x) m = 0 :=
  DirectSum.of_eq_of_ne n m x h

theorem total_apply_succ (t : ∀ n, N n →ₗ[C] N (n + 1)) (x : ⨁ n, N n) (n : ℕ) :
    total t x (n + 1) = t n (x n) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m y =>
      change total t (DirectSum.lof C ℕ N m y) (n + 1) = t n ((DirectSum.lof C ℕ N m y) n)
      rw [total_lof]
      by_cases h : n = m
      · subst h
        rw [lof_apply_self, lof_apply_self]
      · rw [lof_apply_of_ne _ h, lof_apply_of_ne _ (by omega), map_zero]
  | add x y hx hy => simp [hx, hy]

theorem total_apply_zero (t : ∀ n, N n →ₗ[C] N (n + 1)) (x : ⨁ n, N n) :
    total t x 0 = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m y =>
      change total t (DirectSum.lof C ℕ N m y) 0 = 0
      rw [total_lof, lof_apply_of_ne _ (by omega)]
  | add x y hx hy => simp [hx, hy]

theorem total_comm (t s : ∀ n, N n →ₗ[C] N (n + 1))
    (h : ∀ n (x : N n), t (n + 1) (s n x) = s (n + 1) (t n x)) :
    total t * total s = total s * total t := by
  apply DirectSum.linearMap_ext
  intro n
  ext x
  simp only [LinearMap.comp_apply, Module.End.mul_apply, total_lof, h]

section Action

variable {r : ℕ} (t : Fin r → ∀ n, N n →ₗ[C] N (n + 1))

theorem pairwise_commute (comm : ∀ i j n (x : N n), t i (n + 1) (t j n x) = t j (n + 1) (t i n x)) :
    (Set.range fun i => total (t i)).Pairwise Commute := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
  exact total_comm (t i) (t j) (comm i j)

open scoped IsMulCommutative in
/-- The action of polynomials on `⨁ n, N n`, the variable `X i` acting by `total (t i)`. -/
noncomputable def polyAct
    (comm : ∀ i j n (x : N n), t i (n + 1) (t j n x) = t j (n + 1) (t i n x)) :
    MvPolynomial (Fin r) C →ₐ[C] Module.End C (⨁ n, N n) :=
  haveI := Algebra.isMulCommutative_adjoin C (pairwise_commute t comm)
  (Algebra.adjoin C (Set.range fun i => total (t i))).val.comp
    (MvPolynomial.aeval fun i => ⟨total (t i), Algebra.subset_adjoin ⟨i, rfl⟩⟩)

variable {t}

theorem polyAct_X
    (comm : ∀ i j n (x : N n), t i (n + 1) (t j n x) = t j (n + 1) (t i n x)) (i : Fin r) :
    polyAct t comm (MvPolynomial.X i) = total (t i) := by
  simp [polyAct]

theorem polyAct_C
    (comm : ∀ i j n (x : N n), t i (n + 1) (t j n x) = t j (n + 1) (t i n x)) (c : C)
    (x : ⨁ n, N n) :
    polyAct t comm (MvPolynomial.C c) x = c • x := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rfl

end Action

/-- **Bounded generation of stable families.** Let `C` be a noetherian ring, `N n` finite
`C`-modules and `t i n : N n → N (n + 1)` (`i : Fin r`) pairwise commuting `C`-linear maps,
whose ranges together span `N (n + 1)` for all `n ≥ N₀`. Then every family of submodules
`K n` stable under all `t i` is generated in bounded degree: for all large `n`,
`K (n + 1)` is the span of the images of `K n` under the `t i`. -/
theorem exists_stable_generation [IsNoetherianRing C] [∀ n, Module.Finite C (N n)] {r : ℕ}
    (t : Fin r → ∀ n, N n →ₗ[C] N (n + 1))
    (comm : ∀ i j n (x : N n), t i (n + 1) (t j n x) = t j (n + 1) (t i n x))
    (N₀ : ℕ) (gen : ∀ n, N₀ ≤ n → ⨆ i, LinearMap.range (t i n) = ⊤)
    (K : ∀ n, Submodule C (N n)) (hK : ∀ i n, (K n).map (t i n) ≤ K (n + 1)) :
    ∃ N₁ : ℕ, ∀ n, N₁ ≤ n → K (n + 1) = ⨆ i, (K n).map (t i n) := by
  classical
  let A := MvPolynomial (Fin r) C
  let M := ⨁ n, N n
  let _ : Module A M := Module.compHom M (polyAct t comm).toRingHom
  have smul_def : ∀ (p : A) (x : M), p • x = polyAct t comm p x := fun _ _ => rfl
  have smul_C : ∀ (c : C) (x : M), (MvPolynomial.C c : A) • x = c • x := fun c x => by
    rw [smul_def, polyAct_C]
  have smul_X : ∀ (i : Fin r) (x : M), (MvPolynomial.X i : A) • x = total (t i) x :=
    fun i x => by rw [smul_def, polyAct_X]
  -- `M` is a finite module over the polynomial ring.
  have hgens : ∀ n, ∃ s : Set (N n), s.Finite ∧ Submodule.span C s = ⊤ := fun n =>
    (Submodule.fg_def.mp (Module.Finite.fg_top (R := C) (M := N n)))
  choose g hgfin hgspan using hgens
  let G : Set M := ⋃ n ∈ Finset.range (N₀ + 1), DirectSum.lof C ℕ N n '' g n
  have hGfin : G.Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => (hgfin n).image _
  let P : Submodule A M := Submodule.span A G
  have hlof : ∀ n (y : N n), DirectSum.lof C ℕ N n y ∈ P := by
    intro n
    induction n with
    | zero =>
        intro y
        have hy : y ∈ Submodule.span C (g 0) := by rw [hgspan]; trivial
        induction hy using Submodule.span_induction with
        | mem z hz =>
            exact Submodule.subset_span (Set.mem_biUnion (by simp) ⟨z, hz, rfl⟩)
        | zero => rw [map_zero]; exact P.zero_mem
        | add a b _ _ ha hb => rw [map_add]; exact P.add_mem ha hb
        | smul c a _ ha => rw [map_smul, ← smul_C]; exact P.smul_mem _ ha
    | succ m ih =>
        intro y
        by_cases hm : m + 1 ≤ N₀
        · have hy : y ∈ Submodule.span C (g (m + 1)) := by rw [hgspan]; trivial
          induction hy using Submodule.span_induction with
          | mem z hz =>
              exact Submodule.subset_span
                (Set.mem_biUnion (by simp; omega) ⟨z, hz, rfl⟩)
          | zero => rw [map_zero]; exact P.zero_mem
          | add a b _ _ ha hb => rw [map_add]; exact P.add_mem ha hb
          | smul c a _ ha => rw [map_smul, ← smul_C]; exact P.smul_mem _ ha
        · have hy : y ∈ ⨆ i, LinearMap.range (t i m) := by
            rw [gen m (by omega)]; trivial
          refine Submodule.iSup_induction _ (motive := fun z => DirectSum.lof C ℕ N (m + 1) z ∈ P)
            hy (fun i z hz => ?_) (by rw [map_zero]; exact P.zero_mem)
            (fun a b ha hb => by rw [map_add]; exact P.add_mem ha hb)
          obtain ⟨w, rfl⟩ := hz
          rw [← total_lof, ← smul_X]
          exact P.smul_mem _ (ih w)
  have hP : P = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using DirectSum.induction_on with
    | zero => exact P.zero_mem
    | of n y => exact hlof n y
    | add x y hx hy => exact P.add_mem hx hy
  have : Module.Finite A M := ⟨Submodule.fg_def.mpr ⟨G, hGfin, hP⟩⟩
  have : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
  -- The ascending chain of submodules generated by the `K n` in degrees at most `k`.
  let S : ℕ →o Submodule A M :=
    { toFun := fun k => Submodule.span A
        {x | ∃ n, n ≤ k ∧ ∃ y ∈ K n, x = DirectSum.lof C ℕ N n y}
      monotone' := fun a b hab => Submodule.span_mono fun x ⟨n, hn, y, hy, hx⟩ =>
        ⟨n, hn.trans hab, y, hy, hx⟩ }
  obtain ⟨D, hD⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance S
  -- The elements stable in all degrees and generated from below in degrees above `D`.
  let Q : M → Prop := fun x =>
    (∀ n, x n ∈ K n) ∧ ∀ n, D ≤ n → x (n + 1) ∈ ⨆ i, (K n).map (t i n)
  have hQadd : ∀ x y, Q x → Q y → Q (x + y) := fun x y hx hy =>
    ⟨fun n => by rw [DirectSum.add_apply]; exact add_mem (hx.1 n) (hy.1 n),
      fun n hn => by rw [DirectSum.add_apply]; exact add_mem (hx.2 n hn) (hy.2 n hn)⟩
  have hQsmul : ∀ (c : C) x, Q x → Q (c • x) := fun c x hx =>
    ⟨fun n => by rw [DirectSum.smul_apply]; exact Submodule.smul_mem _ c (hx.1 n),
      fun n hn => by rw [DirectSum.smul_apply]; exact Submodule.smul_mem _ c (hx.2 n hn)⟩
  have hQtotal : ∀ i x, Q x → Q (total (t i) x) := fun i x hx =>
    ⟨fun n => by
      cases n with
      | zero => rw [total_apply_zero]; exact (K 0).zero_mem
      | succ m => rw [total_apply_succ]; exact hK i m ⟨x m, hx.1 m, rfl⟩,
    fun n _ => by
      rw [total_apply_succ]
      exact Submodule.mem_iSup_of_mem i ⟨x n, hx.1 n, rfl⟩⟩
  have hQpoly : ∀ (p : A) x, Q x → Q (p • x) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => intro x hx; rw [smul_C]; exact hQsmul c x hx
    | add p q hp hq => intro x hx; rw [add_smul]; exact hQadd _ _ (hp x hx) (hq x hx)
    | mul_X p i hp => intro x hx; rw [mul_smul, smul_X]; exact hp _ (hQtotal i x hx)
  let W : Submodule A M :=
    { carrier := {x | Q x}
      add_mem' := fun {x y} hx hy => hQadd x y hx hy
      zero_mem' := ⟨fun n => by simp, fun n _ => by simp⟩
      smul_mem' := fun p x hx => hQpoly p x hx }
  have hSW : S D ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨m, hm, y, hy, rfl⟩
    refine ⟨fun n => ?_, fun n hn => ?_⟩
    · by_cases h : n = m
      · subst h; rw [lof_apply_self]; exact hy
      · rw [lof_apply_of_ne _ h]; exact (K n).zero_mem
    · rw [lof_apply_of_ne _ (by omega)]; exact Submodule.zero_mem _
  refine ⟨D, fun n hn => le_antisymm ?_ (iSup_le fun i => hK i n)⟩
  intro y hy
  have hmem : DirectSum.lof C ℕ N (n + 1) y ∈ S (n + 1) :=
    Submodule.subset_span ⟨n + 1, le_rfl, y, hy, rfl⟩
  rw [← hD (n + 1) (by omega)] at hmem
  have := (hSW hmem).2 n hn
  rwa [lof_apply_self] at this

end Langlands.Algebra.GradedStableGeneration
