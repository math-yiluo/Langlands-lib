import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Compact exhaustions by full adelic representation height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- The actual full adelic height sublevel, with no rational quotient taken. -/
def adelicHeightSublevel (B : ℝ) : Set (AdelicGroupPoints F G) :=
  {g | adelicHeight F G rho g ≤ B}

@[simp]
theorem mem_adelicHeightSublevel (B : ℝ) (g : AdelicGroupPoints F G) :
    g ∈ adelicHeightSublevel F G rho B ↔ adelicHeight F G rho g ≤ B := Iff.rfl

theorem adelicHeightSublevel_mono {B C : ℝ} (h : B ≤ C) :
    adelicHeightSublevel F G rho B ⊆ adelicHeightSublevel F G rho C :=
  fun _ hg => hg.trans h

@[simp]
theorem inv_mem_adelicHeightSublevel (B : ℝ) (g : AdelicGroupPoints F G) :
    g⁻¹ ∈ adelicHeightSublevel F G rho B ↔ g ∈ adelicHeightSublevel F G rho B := by
  simp only [mem_adelicHeightSublevel, adelicHeight_inv]

@[simp]
theorem inv_adelicHeightSublevel (B : ℝ) :
    (adelicHeightSublevel F G rho B)⁻¹ = adelicHeightSublevel F G rho B := by
  ext g
  simp only [Set.mem_inv, inv_mem_adelicHeightSublevel]

theorem mul_mem_adelicHeightSublevel (hN : 0 < N) {B C : ℝ}
    {g h : AdelicGroupPoints F G}
    (hg : g ∈ adelicHeightSublevel F G rho B)
    (hh : h ∈ adelicHeightSublevel F G rho C) :
    g * h ∈ adelicHeightSublevel F G rho (B * C) :=
  (adelicHeight_mul_le F G rho hN g h).trans
    (mul_le_mul hg hh (zero_le_one.trans (one_le_adelicHeight F G rho hN h))
      ((zero_le_one.trans (one_le_adelicHeight F G rho hN g)).trans hg))

theorem adelicHeightSublevel_mul_subset (hN : 0 < N) (B C : ℝ) :
    adelicHeightSublevel F G rho B * adelicHeightSublevel F G rho C ⊆
      adelicHeightSublevel F G rho (B * C) := by
  rintro _ ⟨g, hg, h, hh, rfl⟩
  exact mul_mem_adelicHeightSublevel F G rho hN hg hh

/-- Continuity alone bounds the height on every compact subset of actual adelic points. -/
theorem exists_nat_adelicHeight_bound_of_isCompact (hN : 0 < N)
    {K : Set (AdelicGroupPoints F G)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ adelicHeightSublevel F G rho n := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_adelicHeight F G rho hN).continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact ⟨n, fun g hg => (hB ⟨g, hg, rfl⟩).trans hn.le⟩

variable [IsAffine G.X.left]

/-- Closed matrix embeddings have compact full adelic height sublevels. -/
theorem isCompact_adelicHeightSublevel (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (B : ℝ) :
    IsCompact (adelicHeightSublevel F G rho B) := by
  have heq : adelicHeightSublevel F G rho B =
      adelicHeight F G rho ⁻¹' Set.Icc 1 B := by
    ext g
    exact ⟨fun hg => ⟨one_le_adelicHeight F G rho hN g, hg⟩, fun hg => hg.2⟩
  rw [heq]
  exact (isProperMap_adelicHeight F G rho hN hrho).isCompact_preimage isCompact_Icc

/-- Compact exhaustion of the original adelic topology by the exact natural height sublevels. -/
def adelicHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) :
    CompactExhaustion (AdelicGroupPoints F G) where
  toFun n := adelicHeightSublevel F G rho n
  isCompact' n := isCompact_adelicHeightSublevel F G rho hN hrho n
  subset_interior_succ' n := by
    have hopen : IsOpen {g : AdelicGroupPoints F G |
        adelicHeight F G rho g < ((n + 1 : ℕ) : ℝ)} :=
      isOpen_lt (continuous_adelicHeight F G rho hN) continuous_const
    have hsub : {g : AdelicGroupPoints F G |
        adelicHeight F G rho g < ((n + 1 : ℕ) : ℝ)} ⊆
        adelicHeightSublevel F G rho (n + 1 : ℕ) := by
      intro g hx
      change adelicHeight F G rho g ≤ ((n + 1 : ℕ) : ℝ)
      exact le_of_lt hx
    intro g hg
    change adelicHeight F G rho g ≤ (n : ℝ) at hg
    apply interior_maximal hsub hopen
    change adelicHeight F G rho g < ((n + 1 : ℕ) : ℝ)
    exact hg.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  iUnion_eq' := Set.iUnion_eq_univ_iff.mpr fun g => by
    obtain ⟨n, hn⟩ := exists_nat_gt (adelicHeight F G rho g)
    exact ⟨n, hn.le⟩

@[simp]
theorem adelicHeightCompactExhaustion_apply (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (n : ℕ) :
    adelicHeightCompactExhaustion F G rho hN hrho n =
      adelicHeightSublevel F G rho n := rfl

@[simp]
theorem mem_adelicHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (n : ℕ) (g : AdelicGroupPoints F G) :
    g ∈ adelicHeightCompactExhaustion F G rho hN hrho n ↔
      adelicHeight F G rho g ≤ n := Iff.rfl

@[simp]
theorem inv_adelicHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (n : ℕ) :
    (adelicHeightCompactExhaustion F G rho hN hrho n)⁻¹ =
      adelicHeightCompactExhaustion F G rho hN hrho n :=
  inv_adelicHeightSublevel F G rho n

theorem adelicHeightCompactExhaustion_mul_subset (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (m n : ℕ) :
    adelicHeightCompactExhaustion F G rho hN hrho m *
        adelicHeightCompactExhaustion F G rho hN hrho n ⊆
      adelicHeightCompactExhaustion F G rho hN hrho (m * n) := by
  simpa only [adelicHeightCompactExhaustion_apply, Nat.cast_mul] using
    adelicHeightSublevel_mul_subset F G rho hN (m : ℝ) (n : ℝ)

/-- The explicit height exhaustion contains every compact subset at some natural level. -/
theorem exists_adelicHeightCompactExhaustion_superset (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho)
    {K : Set (AdelicGroupPoints F G)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ adelicHeightCompactExhaustion F G rho hN hrho n :=
  exists_nat_adelicHeight_bound_of_isCompact F G rho hN hK

/-- Any real height sublevel is contained in a level for any other closed embedding. -/
theorem adelicHeightSublevel_subset_other_exhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho)
    {M : ℕ} (sigma : GroupScheme.MatrixRepresentation G (Fin M))
    (hM : 0 < M) (hsigma : GroupScheme.IsClosedSubgroup sigma) (B : ℝ) :
    ∃ m : ℕ, adelicHeightSublevel F G rho B ⊆
      adelicHeightCompactExhaustion F G sigma hM hsigma m :=
  exists_adelicHeightCompactExhaustion_superset F G sigma hM hsigma
    (isCompact_adelicHeightSublevel F G rho hN hrho B)

/-- The natural height exhaustions for any two closed matrix embeddings are cofinal. -/
theorem adelicHeightCompactExhaustion_cofinal (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho)
    {M : ℕ} (sigma : GroupScheme.MatrixRepresentation G (Fin M))
    (hM : 0 < M) (hsigma : GroupScheme.IsClosedSubgroup sigma) (n : ℕ) :
    ∃ m : ℕ, adelicHeightCompactExhaustion F G rho hN hrho n ⊆
      adelicHeightCompactExhaustion F G sigma hM hsigma m :=
  adelicHeightSublevel_subset_other_exhaustion F G rho hN hrho sigma hM hsigma n

end Langlands.Global.RepresentationGrowth
