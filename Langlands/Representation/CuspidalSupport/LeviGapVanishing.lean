import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.LeviSplitContraction
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Conductor.Congruence

/-!
# Deep vanishing of averaged torus translates for quasicuspidal product-Levi representations

The integral subgroup of a product Levi as a compact open subgroup, the vanishing of
averages of translates by antitone torus elements with one deep gap, and the finiteness of
bounded-gap exponent tuples up to blockwise constants.
-/

noncomputable section

open Filter Topology

namespace Langlands.CuspidalSupport.LeviAdmissibility

open GeneralLinear Geometric

universe uF uV

section Levi

variable {K : Type uF} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The integral matrices of every rank form an open subset. -/
theorem isOpen_integralRange (m : ℕ) :
    IsOpen (Iwasawa.integralRange (ValuativeRel.valuation K) m :
      Set (GeneralLinear m K)) := by
  cases m with
  | zero =>
    convert isOpen_univ
    refine Set.eq_univ_of_forall fun g => ?_
    have hg : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    rw [hg]
    exact Subgroup.one_mem _
  | succ m =>
    have heq : (Conductor.levelOpenSubgroup K m 0 : Set (GeneralLinear (m + 1) K)) =
        Iwasawa.integralRange (ValuativeRel.valuation K) (m + 1) := by
      rw [Iwasawa.integralRange_succ]
      change (Conductor.levelSubgroup K m 0 : Set (GeneralLinear (m + 1) K)) = _
      rw [Conductor.levelSubgroup_zero]
    rw [← heq]
    exact (Conductor.levelOpenSubgroup K m 0).isOpen

/-- The integral matrices of every rank form a compact subset. -/
theorem isCompact_integralRange (m : ℕ) :
    IsCompact (Iwasawa.integralRange (ValuativeRel.valuation K) m :
      Set (GeneralLinear m K)) := by
  cases m with
  | zero =>
    refine Set.Subsingleton.isCompact fun x _ y _ => ?_
    exact Units.ext (Matrix.ext fun i _ => i.elim0)
  | succ m =>
    have heq : (Conductor.levelOpenSubgroup K m 0 : Set (GeneralLinear (m + 1) K)) =
        Iwasawa.integralRange (ValuativeRel.valuation K) (m + 1) := by
      rw [Iwasawa.integralRange_succ]
      change (Conductor.levelSubgroup K m 0 : Set (GeneralLinear (m + 1) K)) = _
      rw [Conductor.levelSubgroup_zero]
    rw [← heq]
    exact Conductor.isCompact_levelOpenSubgroup K m 0

variable {n : ℕ} (B : BlockShape n)

/-- The product of the integral subgroups of the blocks. -/
def integralLevi : OpenSubgroup (B.Levi K) where
  toSubgroup := Subgroup.pi Set.univ fun j =>
    Iwasawa.integralRange (ValuativeRel.valuation K) (B.size j)
  isOpen' := by
    have h := isOpen_set_pi Set.finite_univ fun j (_ : j ∈ Set.univ) =>
      isOpen_integralRange (K := K) (B.size j)
    rwa [← Subgroup.coe_pi] at h

theorem mem_integralLevi {g : B.Levi K} :
    g ∈ integralLevi B ↔
      ∀ j, g j ∈ Iwasawa.integralRange (ValuativeRel.valuation K) (B.size j) := by
  change g ∈ Subgroup.pi Set.univ _ ↔ _
  rw [Subgroup.mem_pi]
  simp

theorem isCompact_integralLevi :
    IsCompact ((integralLevi (K := K) B : OpenSubgroup (B.Levi K)) : Set (B.Levi K)) := by
  change IsCompact ((Subgroup.pi Set.univ fun j =>
    Iwasawa.integralRange (ValuativeRel.valuation K) (B.size j)) : Set (B.Levi K))
  rw [Subgroup.coe_pi]
  exact isCompact_univ_pi fun j => isCompact_integralRange (B.size j)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Deep vanishing: for a fixed vector and a fixed left translation, the average
over a compact open subgroup vanishes once one gap of the torus exponents is large. -/
theorem exists_gap_average_eq_zero (ρ : Representation ℂ (B.Levi K) V) (hρ : IsSmooth ρ)
    (hq : IsLeviQuasicuspidal B ρ) {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ)
    (H : OpenSubgroup (B.Levi K)) (hH : IsCompact (H : Set (B.Levi K))) (c : B.Levi K)
    (w : V) (i : Fin B.length) (a : ℕ) (ha : a + 1 < B.size i) :
    ∃ N : ℤ, ∀ lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ, (∀ j, Antitone (lam j)) →
      N ≤ lam i ⟨a, by omega⟩ - lam i ⟨a + 1, ha⟩ →
      Compact.averageMap ρ hρ H hH (ρ (c * leviTorus B ϖ lam) w) = 0 := by
  have hw : w ∈ Representation.Coinvariants.ker
      (ρ.comp (refinedUnipotent K B (splitRefinement B i a ha)).subtype) := by
    have := hq _ (splitRefinement_parabolic_ne_top i a ha)
    exact (Representation.Coinvariants.mk_eq_zero _).mp (Subsingleton.elim _ _)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨u, y⟩, rfl⟩ := hx
    obtain ⟨hone, hsplit⟩ := mem_splitRefinement_unipotent u.2
    have hsplit' := (mem_splitRefinement_unipotent (inv_mem u.2)).2
    let O : Set (GeneralLinear (B.size i) K) :=
      (fun g => c * Pi.mulSingle i g * c⁻¹) ⁻¹' (H : Set (B.Levi K))
    have hO : O ∈ 𝓝 1 := by
      apply IsOpen.mem_nhds
      · exact H.isOpen.preimage
          ((continuous_const.mul (continuous_mulSingle i)).mul continuous_const)
      · change c * Pi.mulSingle i 1 * c⁻¹ ∈ H
        rw [Pi.mulSingle_one, mul_one, mul_inv_cancel]
        exact H.one_mem
    obtain ⟨N, hN⟩ := torus_conj_eventually_mem ha hϖ hsplit hsplit' hO
    refine ⟨N, fun lam hlam hgap => ?_⟩
    have hk : c * (leviTorus B ϖ lam * u * (leviTorus B ϖ lam)⁻¹) * c⁻¹ ∈ H := by
      rw [leviTorus_conj_of_eq_one B ϖ lam hone]
      exact hN (lam i) (hlam i) hgap
    have hmul : c * leviTorus B ϖ lam * u =
        (c * (leviTorus B ϖ lam * u * (leviTorus B ϖ lam)⁻¹) * c⁻¹) *
          (c * leviTorus B ϖ lam) := by
      group
    change Compact.averageMap ρ hρ H hH (ρ (c * leviTorus B ϖ lam) (ρ u y - y)) = 0
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply,
      map_sub, sub_eq_zero]
    exact Compact.orbitMean_apply (ρ.comp H.toSubgroup.subtype) ⟨_, hk⟩ _
  | zero => exact ⟨0, fun lam _ _ => by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨max N₁ N₂, fun lam hlam hgap => ?_⟩
    rw [map_add, map_add, h₁ lam hlam (le_of_max_le_left hgap),
      h₂ lam hlam (le_of_max_le_right hgap), add_zero]
  | smul r x _ hx =>
    obtain ⟨N, h⟩ := hx
    exact ⟨N, fun lam hlam hgap => by rw [map_smul, map_smul, h lam hlam hgap, smul_zero]⟩

/-- A single bound for deep vanishing, uniform over finitely many translations and
vectors and over all split points of all blocks. -/
theorem exists_uniform_gap_bound (ρ : Representation ℂ (B.Levi K) V) (hρ : IsSmooth ρ)
    (hq : IsLeviQuasicuspidal B ρ) {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ)
    (H : OpenSubgroup (B.Levi K)) (hH : IsCompact (H : Set (B.Levi K)))
    {ι : Type*} [Finite ι] (c : ι → B.Levi K) (w : ι → V) :
    ∃ N : ℤ, ∀ x : ι, ∀ lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ,
      (∀ j, Antitone (lam j)) → ∀ (i : Fin B.length) (a : ℕ) (ha : a + 1 < B.size i),
      N ≤ lam i ⟨a, by omega⟩ - lam i ⟨a + 1, ha⟩ →
      Compact.averageMap ρ hρ H hH (ρ (c x * leviTorus B ϖ lam) (w x)) = 0 := by
  classical
  let f : ι × (Σ i : Fin B.length, Fin (B.size i)) → ℤ := fun p =>
    if h : p.2.2.val + 1 < B.size p.2.1 then
      Classical.choose
        (exists_gap_average_eq_zero B ρ hρ hq hϖ H hH (c p.1) (w p.1) p.2.1 p.2.2 h)
    else 0
  obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
  refine ⟨N, fun x lam hlam i a ha hgap => ?_⟩
  have hle : f (x, ⟨i, ⟨a, by omega⟩⟩) ≤ N := hN ⟨_, rfl⟩
  simp only [f, ha, ↓reduceDIte] at hle
  exact Classical.choose_spec
    (exists_gap_average_eq_zero B ρ hρ hq hϖ H hH (c x) (w x) i a ha) lam hlam
    (hle.trans hgap)

/-- Bounded-gap exponents: finitely many antitone exponent tuples represent, up to a
constant in each block, every tuple whose gaps are all below `N`. -/
def BoundedGapReps (N : ℤ) : Prop :=
  ∃ Λ₀ : Set (∀ j : Fin B.length, Fin (B.size j) → ℤ), Λ₀.Finite ∧
    ∀ lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ, (∀ j, Antitone (lam j)) →
      (∀ j (b : Fin (B.size j)) (h : b.val + 1 < B.size j),
        lam j b - lam j ⟨b.val + 1, h⟩ < N) →
      ∃ μ ∈ Λ₀, ∃ c : Fin B.length → ℤ, ∀ j b, lam j b = μ j b + c j

/-- An entry `k` steps before the last one exceeds the last one by at most `k * |N|`
when every gap is below `N`. -/
theorem sub_last_le {m : ℕ} (f : Fin m → ℤ) (N : ℤ) (hm : 0 < m)
    (hgap : ∀ (b : Fin m) (h : b.val + 1 < m), f b - f ⟨b.val + 1, h⟩ < N) :
    ∀ (k : ℕ) (b : Fin m), b.val + k = m - 1 → f b - f ⟨m - 1, by omega⟩ ≤ k * |N| := by
  intro k
  induction k with
  | zero =>
    intro b hb
    have hb' : b = ⟨m - 1, by omega⟩ := Fin.ext (by simpa using hb)
    rw [hb', sub_self]
    simp
  | succ k ih =>
    intro b hb
    have h1 : b.val + 1 < m := by omega
    have h2 := ih ⟨b.val + 1, h1⟩ (by simp only; omega)
    have h3 := hgap b h1
    have h4 := le_abs_self N
    have h5 : ((k + 1 : ℕ) : ℤ) * |N| = k * |N| + |N| := by push_cast; ring
    rw [h5]
    linarith

/-- Exponent tuples with bounded gaps are, up to a constant in each block, drawn
from a finite set. -/
theorem boundedGapReps (N : ℤ) : BoundedGapReps B N := by
  classical
  refine ⟨Set.univ.pi fun j => Set.univ.pi fun _ => Set.Icc 0 ((B.size j : ℤ) * |N|),
    Set.Finite.pi fun j => Set.Finite.pi fun _ => Set.finite_Icc _ _, ?_⟩
  intro lam hlam hgap
  let c : Fin B.length → ℤ := fun j => lam j ⟨B.size j - 1, by have := B.positive j; omega⟩
  refine ⟨fun j b => lam j b - c j, ?_, c, fun j b => by ring⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro j b
  have hm := B.positive j
  have hb := b.2
  constructor
  · have h := hlam j (show b ≤ ⟨B.size j - 1, by omega⟩ from
      Fin.le_iff_val_le_val.mpr (by simp only; omega))
    simp only [c]
    linarith
  · have h := sub_last_le (lam j) N hm (hgap j) (B.size j - 1 - b.val) b (by omega)
    have h' : ((B.size j - 1 - b.val : ℕ) : ℤ) * |N| ≤ (B.size j : ℤ) * |N| :=
      mul_le_mul_of_nonneg_right (by omega) (abs_nonneg N)
    exact h.trans h'

end Levi

end Langlands.CuspidalSupport.LeviAdmissibility
