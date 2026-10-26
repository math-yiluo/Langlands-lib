import Langlands.Representation.Classification.MaximalConePolygon
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-!
# Selection of a dominance-maximal cone

A finite family of block vectors, each with at least one cone, has a cone whose
positive part is not strictly dominated by the positive part of any cone of the
family. The selection maximizes the sum of all prefix sums of the positive part,
which strictly increases under strict dominance.
-/

namespace Langlands

open GeneralLinear
open scoped BigOperators

namespace MaximalConePolygon

variable {n : ℕ}

/-- The sum of all prefix sums of the positive part `(C, t)` in standard coordinates. -/
def potential (C : BlockShape n) (t : Fin C.length → ℝ) : ℝ :=
  ∑ k : Fin (n + 1), pre (fun x => t (Geometric.blockIndex C x)) k

/-- Strict dominance strictly increases the potential. -/
theorem potential_lt_of_strictlyDominates {C₁ C₂ : BlockShape n}
    {t₁ : Fin C₁.length → ℝ} {t₂ : Fin C₂.length → ℝ}
    (h : GLBlockPositivePartStrictlyDominates C₁ t₁ C₂ t₂) :
    potential C₂ t₂ < potential C₁ t₁ := by
  obtain ⟨_, hle, k, hk⟩ := h
  exact Finset.sum_lt_sum (fun k _ => hle k) ⟨k, Finset.mem_univ _, hk⟩

/-- The value of a positive part on a block, read off from the block totals. -/
noncomputable def coneValue (B : BlockShape n) (r : Fin B.length → ℝ) (C : BlockShape n)
    (q : Fin B.length → Fin C.length) (j : Fin C.length) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => q i = j), r i) / (C.size j : ℝ)

/-- The values of a cone are determined by the block vector and the coarsening. -/
theorem IsCone.eq_coneValue {B C : BlockShape n} {r : Fin B.length → ℝ}
    {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ} (hc : IsCone B r C q t) :
    t = coneValue B r C q := by
  funext j
  have hpos : (0 : ℝ) < C.size j := by exact_mod_cast C.positive j
  rw [coneValue, hc.total j, mul_div_cancel_left₀ _ hpos.ne']

/-- A finite family of block vectors, one of which has a cone, has a cone that no
cone of any member of the family strictly dominates. -/
theorem exists_maximal_cone (R : (B : BlockShape n) → Set (Fin B.length → ℝ))
    (hR : ∀ B, (R B).Finite)
    (hne : ∃ (B : BlockShape n) (r : Fin B.length → ℝ) (C : BlockShape n)
      (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ), r ∈ R B ∧ IsCone B r C q t) :
    ∃ (B : BlockShape n) (r : Fin B.length → ℝ) (C : BlockShape n)
      (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ),
      r ∈ R B ∧ IsCone B r C q t ∧
      ∀ (B' : BlockShape n) (r' : Fin B'.length → ℝ) (C' : BlockShape n)
        (q' : Fin B'.length → Fin C'.length) (t' : Fin C'.length → ℝ),
        r' ∈ R B' → IsCone B' r' C' q' t' →
        ¬ GLBlockPositivePartStrictlyDominates C' t' C t := by
  let V : Set ℝ := {v | ∃ (B : BlockShape n) (r : Fin B.length → ℝ) (C : BlockShape n)
    (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ),
    r ∈ R B ∧ IsCone B r C q t ∧ potential C t = v}
  have hV : V.Finite := by
    refine Set.Finite.subset (Set.finite_iUnion fun B : BlockShape n =>
      (hR B).biUnion fun r _ => Set.finite_iUnion fun C : BlockShape n =>
        Set.finite_range fun q : Fin B.length → Fin C.length =>
          potential C (coneValue B r C q)) ?_
    rintro v ⟨B, r, C, q, t, hr, hc, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨B, r, hr, C, q, by rw [hc.eq_coneValue]⟩
  have hVne : V.Nonempty := by
    obtain ⟨B, r, C, q, t, hr, hc⟩ := hne
    exact ⟨_, B, r, C, q, t, hr, hc, rfl⟩
  obtain ⟨v, ⟨B, r, C, q, t, hr, hc, rfl⟩, hmax⟩ := Set.exists_max_image V id hV hVne
  refine ⟨B, r, C, q, t, hr, hc, ?_⟩
  intro B' r' C' q' t' hr' hc' hdom
  have h1 := potential_lt_of_strictlyDominates hdom
  have h2 := hmax _ ⟨B', r', C', q', t', hr', hc', rfl⟩
  simp only [id] at h2
  linarith

end MaximalConePolygon

end Langlands
