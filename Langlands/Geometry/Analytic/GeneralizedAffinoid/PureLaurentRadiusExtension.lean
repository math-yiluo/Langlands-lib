import Langlands.Geometry.Analytic.GeneralizedAffinoid.LaurentGaussField

/-! # Pure Laurent extensions and radical value-group radii -/

noncomputable section

universe u

namespace Langlands.Analytic

/-- A positive integral power of the radius is the norm of a field element. -/
def RadiusInRadicalValueGroup (K : Type u) [NormedField K] (r : ℝ) : Prop :=
  ∃ (a : K) (n : ℕ), 0 < n ∧ ‖a‖ = r ^ n

/-- The scalar map is a finite composite of the actual completed Gauss Laurent
inclusions, with no algebraic root extensions among its steps. -/
inductive IsPureLaurentTower (K : Type u) [NormedField K] [IsUltrametricDist K] :
    (L : Type u) → [NormedField L] → [IsUltrametricDist L] → (K →+* L) → Prop
  | refl : IsPureLaurentTower K K (RingHom.id K)
  | step {L : Type u} [NormedField L] [IsUltrametricDist L] {ι : K →+* L}
      (prior : IsPureLaurentTower K L ι)
      (r : ℝ) [Fact (0 < r)]
      (independent : ∀ (a : L) (n : ℤ), n ≠ 0 → ‖a‖ ≠ r ^ n) :
      letI := CompletedGaussLaurent.normedField independent
      IsPureLaurentTower K (CompletedGaussLaurent L r)
        ((CompletedGaussLaurent.ι (K := L) (t := r)).comp ι)

/-- A complete pure Laurent field extension in the universe of its base. -/
structure PureLaurentExtension (K : Type u) [NormedField K] [IsUltrametricDist K] where
  L : Type u
  [instNormedField : NormedField L]
  [instUltrametric : IsUltrametricDist L]
  [instComplete : CompleteSpace L]
  ι : K →+* L
  norm_ι : ∀ a, ‖ι a‖ = ‖a‖
  tower : IsPureLaurentTower K L ι

namespace PureLaurentExtension

attribute [instance] instNormedField instUltrametric instComplete

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- The tower with no steps. -/
def self [CompleteSpace K] : PureLaurentExtension K where
  L := K
  ι := RingHom.id K
  norm_ι _ := rfl
  tower := .refl

/-- Append an independent positive-radius Gauss Laurent step to the tower. -/
def adjoin (R : PureLaurentExtension K) (r : ℝ) [Fact (0 < r)]
    (H : ∀ (a : R.L) (n : ℤ), n ≠ 0 → ‖a‖ ≠ r ^ n) :
    PureLaurentExtension K :=
  letI := CompletedGaussLaurent.normedField H
  { L := CompletedGaussLaurent R.L r
    instNormedField := CompletedGaussLaurent.normedField H
    instUltrametric := completion_isUltrametricDist
    instComplete := inferInstanceAs
      (CompleteSpace (UniformSpace.Completion (GaussLaurent R.L r)))
    ι := CompletedGaussLaurent.ι.comp R.ι
    norm_ι a := by
      rw [RingHom.comp_apply, CompletedGaussLaurent.norm_ι, R.norm_ι]
    tower := .step R.tower r H }

omit [IsUltrametricDist K] in
/-- Existing positive-power norm witnesses survive every isometric field map. -/
theorem radiusInRadicalValueGroup_map {L : Type u} [NormedField L]
    (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖) {r : ℝ}
    (h : RadiusInRadicalValueGroup K r) :
    RadiusInRadicalValueGroup L r := by
  obtain ⟨a, n, hn, ha⟩ := h
  exact ⟨ι a, n, hn, by rw [hι, ha]⟩

omit [IsUltrametricDist K] in
/-- Outside the radical value group, every nonzero integral power of a positive
radius differs from every field norm. -/
theorem independent_of_not_radiusInRadicalValueGroup {r : ℝ}
    (h : ¬ RadiusInRadicalValueGroup K r) :
    ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ r ^ n := by
  intro a n hn ha
  apply h
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨a⁻¹, n.natAbs, by omega, ?_⟩
    rw [norm_inv, ha, ← zpow_natCast, Int.natCast_natAbs, abs_of_neg hneg, zpow_neg]
  · refine ⟨a, n.natAbs, by omega, ?_⟩
    rw [ha, ← zpow_natCast, Int.natCast_natAbs, abs_of_pos hpos]

/-- A finite family can be put in the radical value group using only pure
Laurent steps. Radii already in that group require no extension. -/
theorem exists_for_radii [CompleteSpace K] :
    ∀ (N : ℕ) (t : Fin N → ℝ), (∀ i, 0 < t i) →
      ∃ R : PureLaurentExtension K, ∀ i, RadiusInRadicalValueGroup R.L (t i)
  | 0, _, _ => ⟨self, fun i => Fin.elim0 i⟩
  | N + 1, t, ht => by
    obtain ⟨R, hR⟩ := exists_for_radii N (Fin.tail t) fun i => ht i.succ
    by_cases h : RadiusInRadicalValueGroup R.L (t 0)
    · exact ⟨R, fun i => Fin.cases h (fun j => hR j) i⟩
    · let : Fact (0 < t 0) := ⟨ht 0⟩
      let H := independent_of_not_radiusInRadicalValueGroup h
      let := CompletedGaussLaurent.normedField H
      let S := R.adjoin (t 0) H
      refine ⟨S, fun i => Fin.cases ?_ (fun j => ?_) i⟩
      · exact ⟨CompletedGaussLaurent.X, 1, by omega, by
          change ‖(CompletedGaussLaurent.X : CompletedGaussLaurent R.L (t 0))‖ = t 0 ^ 1
          simpa only [S, adjoin, pow_one] using
            (CompletedGaussLaurent.norm_X (K := R.L) (t := t 0))⟩
      · exact radiusInRadicalValueGroup_map
          (CompletedGaussLaurent.ι (K := R.L) (t := t 0))
          CompletedGaussLaurent.norm_ι (hR j)

/-- The same construction can always make the extension nontrivially valued:
include radius two among the positive radii before selecting the tower. -/
theorem exists_nontrivial_for_radii [CompleteSpace K] (N : ℕ) (t : Fin N → ℝ)
    (ht : ∀ i, 0 < t i) :
    ∃ R : PureLaurentExtension K,
      (∃ a : R.L, 1 < ‖a‖) ∧ ∀ i, RadiusInRadicalValueGroup R.L (t i) := by
  obtain ⟨R, hR⟩ := exists_for_radii (K := K) (N + 1) (Fin.cons 2 t)
    (fun i => Fin.cases (by norm_num) ht i)
  refine ⟨R, ?_, fun i => by simpa using hR i.succ⟩
  obtain ⟨a, n, hn, ha⟩ := hR 0
  refine ⟨a, ?_⟩
  rw [ha]
  change 1 < (2 : ℝ) ^ n
  exact one_lt_pow₀ (by norm_num) hn.ne'

end PureLaurentExtension

end Langlands.Analytic
