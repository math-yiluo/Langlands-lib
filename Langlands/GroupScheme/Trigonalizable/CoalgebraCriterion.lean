import Langlands.GroupScheme.CoalgebraUnipotence.ConilpotenceFromMatrix
import Mathlib.RingTheory.Coalgebra.GroupLike

/-! # A coalgebra criterion for trigonalizability

A finite matrix corepresentation of a bialgebra `B` over a field has a stable line when some
nonzero coordinate vector `v` and some `c ∈ B` satisfy `∑ j, v j • a i j = v i • c` for every
row `i`. This file shows that the property "every nonzero finite matrix corepresentation has a
stable line" is equivalent to exhaustion of `B` by the filtration whose next level consists of
the elements sent into the previous level by every right translation with a functional
vanishing on all group-like elements. The filtration is visibly carried into itself by
bialgebra maps, so the matrix property passes to quotient bialgebras.
-/

noncomputable section

open Coalgebra TensorProduct Module
open Langlands.GroupScheme.AffineLinearEmbedding Langlands.GroupScheme.CoalgebraUnipotence

namespace Langlands.GroupScheme.CoalgebraTrigonalizable

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Bialgebra k B]
  {C : Type*} [Ring C] [Bialgebra k C]

variable (k B)

/-- Every nonzero finite matrix corepresentation has a stable line: a nonzero coordinate
vector `v` and an element `c` with `∑ j, v j • a i j = v i • c` for every row `i`. -/
def IsMatrixTrigonalizable : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a : Matrix (Fin n) (Fin n) B,
    IsCoefficientMatrix (k := k) a →
      ∃ v : Fin n → k, v ≠ 0 ∧ ∃ c : B, ∀ i, ∑ j, v j • a i j = v i • c

/-- The common-kernel filtration for right translations by functionals vanishing on every
group-like element. -/
def groupLikeLevel : ℕ → Submodule k B
  | 0 => ⊥
  | n + 1 =>
      ⨅ f : {f : Module.Dual k B // ∀ g : B, IsGroupLikeElem k g → f g = 0},
        (groupLikeLevel n).comap (rightAct f.1)

/-- Every element lies in some level of `groupLikeLevel`. -/
def IsGroupLikeExhausted : Prop :=
  ∀ b : B, ∃ n : ℕ, b ∈ groupLikeLevel k B n

variable {k B}

@[simp] theorem mem_groupLikeLevel_zero (b : B) :
    b ∈ groupLikeLevel k B 0 ↔ b = 0 := by
  simp [groupLikeLevel]

theorem mem_groupLikeLevel_succ (n : ℕ) (b : B) :
    b ∈ groupLikeLevel k B (n + 1) ↔
      ∀ f : Module.Dual k B, (∀ g : B, IsGroupLikeElem k g → f g = 0) →
        rightAct f b ∈ groupLikeLevel k B n := by
  simp [groupLikeLevel, Submodule.mem_iInf, Submodule.mem_comap]

theorem groupLikeLevel_le_succ (n : ℕ) :
    groupLikeLevel k B n ≤ groupLikeLevel k B (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    intro b hb
    rw [mem_groupLikeLevel_succ] at hb ⊢
    exact fun f hf => ih (hb f hf)

theorem groupLikeLevel_mono : Monotone (groupLikeLevel k B) :=
  monotone_nat_of_le_succ groupLikeLevel_le_succ

/-- A right translation acts on a group-like element by the value of its functional. -/
theorem rightAct_of_isGroupLikeElem (f : Module.Dual k B) {g : B}
    (hg : IsGroupLikeElem k g) : rightAct f g = f g • g := by
  simp [rightAct_apply, hg.comul_eq_tmul_self]

/-- Every right translation preserves every level. -/
theorem rightAct_mem_groupLikeLevel (n : ℕ) (g : Module.Dual k B) {b : B}
    (hb : b ∈ groupLikeLevel k B n) : rightAct g b ∈ groupLikeLevel k B n := by
  cases n with
  | zero =>
    have hb0 : b = 0 := (mem_groupLikeLevel_zero b).mp hb
    simp [hb0]
  | succ n =>
    rw [mem_groupLikeLevel_succ] at hb ⊢
    intro f hf
    rw [rightAct_rightAct]
    apply hb
    intro h hh
    simp [rightAct_of_isGroupLikeElem g hh, hf h hh]

/-! ### Bialgebra maps -/

theorem map_mem_groupLikeLevel (q : B →ₐc[k] C) (n : ℕ) {b : B}
    (hb : b ∈ groupLikeLevel k B n) : q b ∈ groupLikeLevel k C n := by
  induction n generalizing b with
  | zero =>
    have hb0 : b = 0 := (mem_groupLikeLevel_zero b).mp hb
    simp [hb0]
  | succ n ih =>
    rw [mem_groupLikeLevel_succ] at hb ⊢
    intro f hf
    rw [← map_rightAct q f b]
    exact ih (hb (f ∘ₗ (q : B →ₗ[k] C)) fun g hg => hf (q g) (hg.map q))

theorem isGroupLikeExhausted_of_surjective (q : B →ₐc[k] C)
    (hq : Function.Surjective q) (hB : IsGroupLikeExhausted k B) :
    IsGroupLikeExhausted k C := by
  intro c
  obtain ⟨b, rfl⟩ := hq c
  obtain ⟨n, hn⟩ := hB b
  exact ⟨n, map_mem_groupLikeLevel q n hn⟩

/-! ### Stable lines and group-like elements -/

/-- The multiplier of a stable line of a matrix corepresentation is group-like. -/
theorem isGroupLikeElem_of_stableLine {n : ℕ} {a : Matrix (Fin n) (Fin n) B}
    (ha : IsCoefficientMatrix (k := k) a) {v : Fin n → k} (hv : v ≠ 0) {c : B}
    (hc : ∀ i, ∑ j, v j • a i j = v i • c) : IsGroupLikeElem k c := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  constructor
  · have h := congrArg (counit (R := k)) (hc i)
    have hl : counit (R := k) (∑ j, v j • a i j) = v i :=
      counit_coefficientVector ha v i
    rw [hl, map_smul, smul_eq_mul] at h
    exact mul_left_cancel₀ hi (by rw [mul_one]; exact h.symm)
  · have h := congrArg (comul (R := k)) (hc i)
    have hl : comul (R := k) (∑ j, v j • a i j) = (v i • c) ⊗ₜ[k] c := by
      calc comul (R := k) (∑ j, v j • a i j)
          = ∑ j, v j • ∑ l, a i l ⊗ₜ[k] a l j := by
            simp only [map_sum, map_smul, ha.1]
        _ = ∑ l, a i l ⊗ₜ[k] (∑ j, v j • a l j) := by
            simp only [Finset.smul_sum, tmul_sum, tmul_smul]
            exact Finset.sum_comm
        _ = ∑ l, a i l ⊗ₜ[k] (v l • c) := by simp only [hc]
        _ = (∑ l, v l • a i l) ⊗ₜ[k] c := by
            simp only [sum_tmul, tmul_smul, smul_tmul']
        _ = (v i • c) ⊗ₜ[k] c := by rw [hc]
    rw [hl, map_smul] at h
    apply smul_right_injective _ hi
    change v i • comul (R := k) c = v i • (c ⊗ₜ[k] c)
    rw [← h, smul_tmul']

/-! ### From exhaustion to stable lines -/

/-- If every functional vanishing on the group-like elements kills all coordinates of a nonzero
coefficient vector, then the corepresentation has a stable line. -/
theorem exists_stableLine_of_forall_dual {n : ℕ} {a : Matrix (Fin n) (Fin n) B}
    (ha : IsCoefficientMatrix (k := k) a) {v : Fin n → k} (hv : v ≠ 0)
    (hkill : ∀ f : Module.Dual k B, (∀ g : B, IsGroupLikeElem k g → f g = 0) →
      ∀ j, f (coefficientVector a v j) = 0) :
    ∃ w : Fin n → k, w ≠ 0 ∧ ∃ c : B, ∀ i, ∑ j, w j • a i j = w i • c := by
  classical
  let S : Set B := {g | IsGroupLikeElem k g}
  have hli : LinearIndependent k (fun g : S => (g : B)) := linearIndepOn_isGroupLikeElem
  let U : Submodule k B := Submodule.span k (Set.range fun g : S => (g : B))
  let b : Basis S k U := Basis.span hli
  have hb : ∀ g : S, (b g : B) = g := fun g => Basis.coe_span_apply hli g
  have hgU : ∀ g : S, (g : B) ∈ U := fun g => Submodule.subset_span ⟨g, rfl⟩
  -- Every coefficient lies in the span of the group-like elements.
  have hxU : ∀ j, coefficientVector a v j ∈ U := by
    intro j
    by_contra hx
    obtain ⟨f, hf, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    apply hf
    apply hkill f _ j
    intro g hg
    have : f g ∈ U.map f := Submodule.mem_map_of_mem (hgU ⟨g, hg⟩)
    rw [hfU] at this
    exact (Submodule.mem_bot k).mp this
  obtain ⟨P, hP⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  have hPU : ∀ u : U, P (u : B) = u := fun u => LinearMap.congr_fun hP u
  -- The coordinate functional of a group-like element, extended to `B`.
  let φ : S → Module.Dual k B := fun g => b.coord g ∘ₗ P
  have hφS : ∀ g h : S, φ g (h : B) = if h = g then 1 else 0 := by
    intro g h
    have : P (h : B) = b h := by
      apply Subtype.ext
      rw [hb, hPU ⟨h, hgU h⟩]
    simp only [φ, LinearMap.comp_apply, this, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
  -- On the span of the group-likes, `rightAct (φ g)` is the `g`-coordinate times `g`.
  have hact : ∀ (g : S) (u : U), rightAct (φ g) (u : B) = φ g (u : B) • (g : B) := by
    intro g
    have hlin : (rightAct (φ g)) ∘ₗ U.subtype =
        (LinearMap.smulRight (φ g ∘ₗ U.subtype) (g : B)) := by
      apply b.ext
      intro h
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, hb]
      rw [rightAct_of_isGroupLikeElem _ h.2, hφS g h]
      by_cases hhg : h = g
      · subst hhg; simp
      · simp [hhg]
    intro u
    exact LinearMap.congr_fun hlin u
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hx₀ : coefficientVector a v i₀ ≠ 0 := by
    intro h
    apply hi₀
    rw [← counit_coefficientVector ha v i₀, h, map_zero]
  obtain ⟨g, hg⟩ : ∃ g : S, φ g (coefficientVector a v i₀) ≠ 0 := by
    by_contra h
    push Not at h
    apply hx₀
    have : (⟨coefficientVector a v i₀, hxU i₀⟩ : U) = 0 := by
      apply b.ext_elem
      intro g
      have hg := h g
      simp only [φ, LinearMap.comp_apply, Basis.coord_apply] at hg
      rw [hPU ⟨_, hxU i₀⟩] at hg
      simpa using hg
    exact congrArg Subtype.val this
  refine ⟨fun j => φ g (coefficientVector a v j), fun h => hg (congrFun h i₀), g, fun i => ?_⟩
  have h1 := rightAct_coefficientVector ha v (φ g) i
  have h2 := hact g ⟨_, hxU i⟩
  simp only at h2
  rw [h2] at h1
  exact h1.symm

theorem isMatrixTrigonalizable_of_isGroupLikeExhausted
    (hB : IsGroupLikeExhausted k B) : IsMatrixTrigonalizable k B := by
  classical
  intro n hn a ha
  let P : ℕ → Prop := fun m =>
    ∃ v : Fin n → k, v ≠ 0 ∧ ∀ i, coefficientVector a v i ∈ groupLikeLevel k B m
  have hex : ∃ m, P m := by
    let v : Fin n → k := fun _ => 1
    have hv : v ≠ 0 := by
      intro h
      exact one_ne_zero (congrFun h ⟨0, hn⟩)
    choose d hd using fun i => hB (coefficientVector a v i)
    refine ⟨Finset.univ.sup d, v, hv, fun i => ?_⟩
    exact groupLikeLevel_mono (Finset.le_sup (Finset.mem_univ i)) (hd i)
  obtain ⟨v, hv, hlevel⟩ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro hm
    apply hv
    funext i
    have hi : coefficientVector a v i = 0 := by
      exact (mem_groupLikeLevel_zero _).mp (hm ▸ hlevel i)
    have := congrArg (counit (R := k)) hi
    simpa [counit_coefficientVector ha] using this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hlevel' : ∀ i, coefficientVector a v i ∈ groupLikeLevel k B (m + 1) := by
    simpa only [hm] using hlevel
  have hkill : ∀ f : Module.Dual k B, (∀ g : B, IsGroupLikeElem k g → f g = 0) →
      ∀ j, f (coefficientVector a v j) = 0 := by
    intro f hf
    by_contra hne
    push Not at hne
    have hw : P m := by
      refine ⟨fun j => f (coefficientVector a v j), fun h => ?_, fun i => ?_⟩
      · obtain ⟨j, hj⟩ := hne
        exact hj (congrFun h j)
      · rw [← rightAct_coefficientVector ha]
        exact (mem_groupLikeLevel_succ m _).mp (hlevel' i) f hf
    have hle := Nat.find_min' hex hw
    omega
  exact exists_stableLine_of_forall_dual ha hv hkill

/-! ### From stable lines to exhaustion -/

/-- A nonzero finite-dimensional quotient of a right-translation-stable subspace has a nonzero
vector sent to zero by every right translation whose functional vanishes on the group-like
elements. -/
theorem exists_stable_mod_of_isMatrixTrigonalizable
    (hB : IsMatrixTrigonalizable k B) (W : Submodule k B)
    (hW : ∀ (f : Module.Dual k B) (w : W), rightAct f (w : B) ∈ W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (q : W →ₗ[k] V) (hq : Function.Surjective q)
    (hker : ∀ (f : Module.Dual k B) (w : W), q w = 0 →
      q ⟨rightAct f (w : B), hW f w⟩ = 0) :
    ∃ w : W, q w ≠ 0 ∧ ∀ f : Module.Dual k B, (∀ g : B, IsGroupLikeElem k g → f g = 0) →
      q ⟨rightAct f (w : B), hW f w⟩ = 0 := by
  classical
  let n := Module.finrank k V
  let e : Basis (Fin n) k V := Module.finBasis k V
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ v, q (s v) = v := fun v => LinearMap.congr_fun hs v
  obtain ⟨P, hP⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  have hPW : ∀ w : W, P (w : B) = w := fun w => LinearMap.congr_fun hP w
  let φ : Fin n → Module.Dual k B := fun i => e.coord i ∘ₗ q ∘ₗ P
  have hφ : ∀ (i : Fin n) (w : W), φ i (w : B) = e.coord i (q w) := by
    intro i w
    simp [φ, hPW]
  let M : Matrix (Fin n) (Fin n) B :=
    fun i j => leftAct (φ i) (s (e j) : B)
  have hM : ∀ i j, M i j = leftAct (φ i) (s (e j) : B) := fun _ _ => rfl
  have hleft_zero : ∀ (i : Fin n) (w : W), q w = 0 →
      leftAct (φ i) (w : B) = 0 := by
    intro i w hw
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro g
    rw [apply_leftAct]
    change φ i ((⟨rightAct g (w : B), hW g w⟩ : W) : B) = 0
    rw [hφ, hker g w hw, map_zero]
  have hleft_expand : ∀ (i : Fin n) (w : W),
      leftAct (φ i) (w : B) = ∑ l, e.coord l (q w) • M i l := by
    intro i w
    have hk : q (w - s (q w)) = 0 := by simp [hqs]
    have hz := hleft_zero i (w - s (q w)) hk
    have heq : leftAct (φ i) (w : B) = leftAct (φ i) (s (q w) : B) := by
      simpa only [Submodule.coe_sub, map_sub, sub_eq_zero] using hz
    rw [heq, ← e.sum_repr (q w), map_sum]
    simp [hM]
  have hright_coord : ∀ (g : Module.Dual k B) (j i : Fin n),
      e.coord i (q ⟨rightAct g (s (e j) : B), hW g (s (e j))⟩) = g (M i j) := by
    intro g j i
    rw [hM, apply_leftAct, ← hφ]
  have hcoeff : IsCoefficientMatrix (k := k) M := by
    constructor
    · intro i j
      apply tensor_ext
      intro g
      rw [← rightAct_apply, hM, rightAct_leftAct]
      rw [hleft_expand i ⟨rightAct g (s (e j) : B), hW g (s (e j))⟩]
      simp [hright_coord]
    · intro i j
      rw [hM, apply_leftAct, rightAct_counit]
      rw [hφ, hqs]
      simp [Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  obtain ⟨v, hv, c, hstable⟩ := hB n (Module.finrank_pos) M hcoeff
  have hc : IsGroupLikeElem k c := isGroupLikeElem_of_stableLine hcoeff hv hstable
  let y : V := ∑ j, v j • e j
  have hy : y ≠ 0 := by
    intro hy
    apply hv
    funext i
    have hi := congrArg (e.coord i) hy
    simpa [y, Basis.coord_apply, Finsupp.single_apply] using hi
  refine ⟨s y, by simpa [hqs] using hy, fun f hf => ?_⟩
  apply e.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  change e.coord i (q ⟨rightAct f (s y : B), hW f (s y)⟩) = 0
  rw [← hφ, ← apply_leftAct]
  have hleft_y : leftAct (φ i) (s y : B) = ∑ j, v j • M i j := by
    simp [y, hM]
  rw [hleft_y, hstable i, map_smul, hf c hc, smul_zero]

theorem exists_groupLikeLevel_containing_finite_stable
    (hB : IsMatrixTrigonalizable k B) (W : Submodule k B) [FiniteDimensional k W]
    (hW : ∀ (f : Module.Dual k B) (w : W), rightAct f (w : B) ∈ W) :
    ∃ n, W ≤ groupLikeLevel k B n := by
  classical
  let F : ℕ →o Submodule k W :=
    ⟨fun n => (groupLikeLevel k B n).comap W.subtype,
      fun _ _ hij => Submodule.comap_mono (groupLikeLevel_mono hij)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian k W) F
  have heq : F n = F (n + 1) := hn (n + 1) (Nat.le_succ n)
  have htop : F n = ⊤ := by
    by_contra hne
    let : Nontrivial (W ⧸ F n) := Submodule.Quotient.nontrivial_iff.mpr hne
    have hker : ∀ (f : Module.Dual k B) (w : W), (F n).mkQ w = 0 →
        (F n).mkQ ⟨rightAct f (w : B), hW f w⟩ = 0 := by
      intro f w hw
      have hw' : w ∈ F n := (Submodule.Quotient.mk_eq_zero _).mp hw
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact rightAct_mem_groupLikeLevel n f hw'
    obtain ⟨w, hw, hfixed⟩ := exists_stable_mod_of_isMatrixTrigonalizable
      hB W hW (F n).mkQ (F n).mkQ_surjective hker
    have hw_next : w ∈ F (n + 1) := by
      change (w : B) ∈ groupLikeLevel k B (n + 1)
      rw [mem_groupLikeLevel_succ]
      intro f hf
      have hmem : (⟨rightAct f (w : B), hW f w⟩ : W) ∈ F n :=
        (Submodule.Quotient.mk_eq_zero _).mp (hfixed f hf)
      exact hmem
    apply hw
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rwa [heq]
  refine ⟨n, fun b hb => ?_⟩
  have hmem : (⟨b, hb⟩ : W) ∈ F n := by rw [htop]; trivial
  exact hmem

theorem isGroupLikeExhausted_of_isMatrixTrigonalizable
    (hB : IsMatrixTrigonalizable k B) : IsGroupLikeExhausted k B := by
  classical
  intro b
  obtain ⟨n, M, hΔ, hε, hcontains⟩ :=
    exists_matrix_coefficients (K := k) ({b} : Finset B)
  let W : Submodule k B :=
    Submodule.span k (Set.range fun p : Fin n × Fin n => M p.1 p.2)
  let : FiniteDimensional k W :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))
  have hW : ∀ (f : Module.Dual k B) (w : W), rightAct f (w : B) ∈ W := by
    intro f w
    have hle : W ≤ W.comap (rightAct f) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hact : rightAct f (M i j) = ∑ l, f (M l j) • M i l := by
        simp [rightAct_apply, hΔ]
      change rightAct f (M i j) ∈ W
      rw [hact]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)
    exact hle w.2
  obtain ⟨m, hm⟩ := exists_groupLikeLevel_containing_finite_stable hB W hW
  exact ⟨m, hm (hcontains (by simp))⟩

/-- Stable lines in all nonzero finite matrix corepresentations are inherited by quotient
bialgebras. -/
theorem IsMatrixTrigonalizable.of_surjective (q : B →ₐc[k] C)
    (hq : Function.Surjective q) (hB : IsMatrixTrigonalizable k B) :
    IsMatrixTrigonalizable k C :=
  isMatrixTrigonalizable_of_isGroupLikeExhausted
    (isGroupLikeExhausted_of_surjective q hq
      (isGroupLikeExhausted_of_isMatrixTrigonalizable hB))

end Langlands.GroupScheme.CoalgebraTrigonalizable
