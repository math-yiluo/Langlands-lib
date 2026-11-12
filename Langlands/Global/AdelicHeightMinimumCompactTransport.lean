import Langlands.Global.AdelicHeightChain
import Langlands.Global.AdelicOrbitHeightCompactBounds

/-! # Transport of simultaneous height inequalities through compact factors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- A single constant controls both height ratios for every representation in
a finite prefix and every nonzero rational vector. -/
def IsSimultaneousOrbitHeightDistortionBound (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (C : Set (AdelicGroupPoints F G)) (B : ℝ) : Prop :=
  ∀ i, i < r → ∀ k ∈ C, ∀ (g : AdelicGroupPoints F G)
    (v : Fin (d i) → F), v ≠ 0 →
      orbitHeight F G (ρ i) v (k * g) ≤ B * orbitHeight F G (ρ i) v g ∧
        orbitHeight F G (ρ i) v g ≤ B * orbitHeight F G (ρ i) v (k * g)

/-- Finitely many actual representations have one positive compact-factor
comparison constant. The empty prefix is included. -/
theorem exists_pos_simultaneous_orbitHeight_distortionBound
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (hd : ∀ i, i < r → 0 < d i)
    {C : Set (AdelicGroupPoints F G)} (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧
      IsSimultaneousOrbitHeightDistortionBound F G r d ρ C B := by
  choose b hb hbound using fun i : Fin r =>
    exists_pos_orbitHeight_bounds_of_isCompact F G (ρ i) (hd i i.isLt) hC
  let B : ℝ := 1 + ∑ i : Fin r, b i
  have hsum : 0 ≤ ∑ i : Fin r, b i :=
    Finset.sum_nonneg fun i _ => (hb i).le
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro i hi k hk g v hv
  let l : Fin r := ⟨i, hi⟩
  have hbB : b l ≤ B := by
    have hle := Finset.single_le_sum (fun j _ => (hb j).le)
      (Finset.mem_univ l)
    dsimp [B]
    linarith
  obtain ⟨hup, hlo⟩ := hbound l k hk g v hv
  exact ⟨hup.trans (mul_le_mul_of_nonneg_right hbB
      (orbitHeight_pos F G (ρ i) hv g).le),
    hlo.trans (mul_le_mul_of_nonneg_right hbB
      (orbitHeight_pos F G (ρ i) hv (k * g)).le)⟩

/-- A bounded left factor transfers all minimum inequalities, with the square
of the height distortion constant. Both directions use the same constant. -/
theorem IsSimultaneousOrbitHeightDistortionBound.chainHeightMinimalSet_transport
    {r : ℕ} {d : ℕ → ℕ}
    {ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i))}
    {C : Set (AdelicGroupPoints F G)} {B : ℝ}
    (h : IsSimultaneousOrbitHeightDistortionBound F G r d ρ C B)
    (hB : 0 ≤ B)
    (v : (i : ℕ) → Fin (d i) → F) (hv : ∀ i, i < r → v i ≠ 0)
    (Q : ℕ → Subgroup (RationalGroupPoints F G))
    (k : normOneSubgroup F G) (hk : (k : AdelicGroupPoints F G) ∈ C)
    (g : normOneSubgroup F G) {c : ℝ} (hc : 0 ≤ c) :
    (g ∈ chainHeightMinimalSet F G r d ρ v Q c →
      k * g ∈ chainHeightMinimalSet F G r d ρ v Q (B ^ 2 * c)) ∧
    (k * g ∈ chainHeightMinimalSet F G r d ρ v Q c →
      g ∈ chainHeightMinimalSet F G r d ρ v Q (B ^ 2 * c)) := by
  constructor
  · intro hg i hi q
    obtain ⟨hup, _⟩ := h i hi k hk g (v i) (hv i hi)
    obtain ⟨_, hlo⟩ := h i hi k hk
      ((g : AdelicGroupPoints F G) * rational F G q) (v i) (hv i hi)
    have hmin := hg i hi q
    change orbitHeight F G (ρ i) (v i)
        ((k : AdelicGroupPoints F G) * g) ≤
      (B ^ 2 * c) * orbitHeight F G (ρ i) (v i)
        (((k : AdelicGroupPoints F G) * g) * rational F G q)
    calc
      _ ≤ B * orbitHeight F G (ρ i) (v i) g := hup
      _ ≤ B * (c * orbitHeight F G (ρ i) (v i)
          ((g : AdelicGroupPoints F G) * rational F G q)) :=
        mul_le_mul_of_nonneg_left hmin hB
      _ ≤ B * (c * (B * orbitHeight F G (ρ i) (v i)
          ((k : AdelicGroupPoints F G) *
            ((g : AdelicGroupPoints F G) * rational F G q)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo hc) hB
      _ = _ := by simp only [mul_assoc]; ring
  · intro hkg i hi q
    obtain ⟨_, hlo⟩ := h i hi k hk g (v i) (hv i hi)
    obtain ⟨hup, _⟩ := h i hi k hk
      ((g : AdelicGroupPoints F G) * rational F G q) (v i) (hv i hi)
    have hmin := hkg i hi q
    change orbitHeight F G (ρ i) (v i)
        ((k : AdelicGroupPoints F G) * g) ≤
      c * orbitHeight F G (ρ i) (v i)
        (((k : AdelicGroupPoints F G) * g) * rational F G q) at hmin
    rw [mul_assoc] at hmin
    calc
      _ ≤ B * orbitHeight F G (ρ i) (v i)
          ((k : AdelicGroupPoints F G) * g) := hlo
      _ ≤ B * (c * orbitHeight F G (ρ i) (v i)
          ((k : AdelicGroupPoints F G) *
            ((g : AdelicGroupPoints F G) * rational F G q))) :=
        mul_le_mul_of_nonneg_left hmin hB
      _ ≤ B * (c * (B * orbitHeight F G (ρ i) (v i)
          ((g : AdelicGroupPoints F G) * rational F G q))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup hc) hB
      _ = _ := by ring

/-- Compact sets transfer all finite simultaneous minimum inequalities with
one positive constant, independent of the point, factor and rational subgroups. -/
theorem exists_pos_chainHeightMinimalSet_compact_transport
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (hd : ∀ i, i < r → 0 < d i)
    {C : Set (AdelicGroupPoints F G)} (hC : IsCompact C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (v : (i : ℕ) → Fin (d i) → F), (∀ i, i < r → v i ≠ 0) →
      ∀ (Q : ℕ → Subgroup (RationalGroupPoints F G))
        (k : normOneSubgroup F G), (k : AdelicGroupPoints F G) ∈ C →
      ∀ (g : normOneSubgroup F G) (c : ℝ), 0 ≤ c →
        (g ∈ chainHeightMinimalSet F G r d ρ v Q c →
          k * g ∈ chainHeightMinimalSet F G r d ρ v Q (D * c)) ∧
        (k * g ∈ chainHeightMinimalSet F G r d ρ v Q c →
          g ∈ chainHeightMinimalSet F G r d ρ v Q (D * c)) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_pos_simultaneous_orbitHeight_distortionBound F G r d ρ hd hC
  refine ⟨B ^ 2, pow_pos hB _, ?_⟩
  intro v hv Q k hk g c hc
  exact hbound.chainHeightMinimalSet_transport F G hB.le v hv Q k hk g hc

end Langlands.Global.RepresentationGrowth
