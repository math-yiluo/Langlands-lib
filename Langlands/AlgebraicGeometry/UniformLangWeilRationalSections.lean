import Langlands.AlgebraicGeometry.UniformLangWeilStatement
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!
# Actual fibre sections from a uniform Lang–Weil estimate

The numerical estimate in Conrad's Lemma 4.6 gives a rational point when the
residue-field cardinality exceeds the square of its constant. The construction
below takes the full published estimate as an explicit hypothesis.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The Lang–Weil error term is smaller than the main term when `C² < q`,
including when the relative dimension is zero. -/
theorem langWeil_count_pos {N q C : ℝ} (d : ℕ) (hC : 0 ≤ C)
    (hlarge : C ^ 2 < q)
    (hbound : |N - q ^ d| ≤ C * q ^ ((d : ℝ) - 1 / 2)) : 0 < N := by
  have hq : 0 < q := (sq_nonneg C).trans_lt hlarge
  have hs : C < Real.sqrt q := (Real.lt_sqrt hC).2 hlarge
  have hp : 0 < q ^ d := pow_pos hq d
  have herr : C * q ^ ((d : ℝ) - 1 / 2) < q ^ d := by
    rw [Real.rpow_sub hq, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    calc
      C * (q ^ d / Real.sqrt q) = (C * q ^ d) / Real.sqrt q := by
        rw [mul_div_assoc]
      _ < q ^ d := (div_lt_iff₀ (Real.sqrt_pos.2 hq)).2 (by nlinarith)
  have hlow := (abs_le.mp hbound).1
  linarith

/-- Positivity gives a section of the actual structure map, with no auxiliary
presentation of the rational-point set. -/
theorem nonempty_sections_of_langWeil_bound
    (K : Type u) [Field K] (V : Scheme.{u}) (π : V ⟶ Spec (CommRingCat.of K))
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (hlarge : C ^ 2 < (Nat.card K : ℝ))
    (hbound :
      |(Nat.card {s : Spec (CommRingCat.of K) ⟶ V // s ≫ π = 𝟙 _} : ℝ) -
          (Nat.card K : ℝ) ^ d| ≤
        C * (Nat.card K : ℝ) ^ ((d : ℝ) - 1 / 2)) :
    Nonempty {s : Spec (CommRingCat.of K) ⟶ V // s ≫ π = 𝟙 _} := by
  have hpos :
      0 < Nat.card {s : Spec (CommRingCat.of K) ⟶ V // s ≫ π = 𝟙 _} := by
    exact_mod_cast langWeil_count_pos d hC hlarge hbound
  exact (Nat.card_pos_iff.mp hpos).1

/-- Given the full uniform Lang–Weil statement and all its geometric hypotheses,
choose one positive uniform constant and an actual rational section over every
closed point whose residue field has cardinality greater than its square. -/
def uniformLangWeilLargeResidueSections
    (hLW : UniformLangWeilStatement.{u})
    (B Y : Scheme.{u}) (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (hBqc : CompactSpace B) (hsmooth : Smooth f)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f) (hsurj : Surjective f)
    (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hconn : GeometricallyConnected f)
    (hdim : ∀ b : B, SchemeFiberGeometry.HasPureDimension (f.fiber b) d) :
    Σ C : {C : ℝ // 0 < C},
      (b : B) → IsClosed ({b} : Set B) →
        C.1 ^ 2 < (Nat.card (B.residueField b) : ℝ) →
        {s : Spec (B.residueField b) ⟶ f.fiber b //
          s ≫ f.fiberToSpecResidueField b = 𝟙 _} := by
  classical
  let estimate := hLW B Y f d hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim
  let C := estimate.choose
  have hC : 0 < C := estimate.choose_spec.1
  have hbound := estimate.choose_spec.2
  refine ⟨⟨C, hC⟩, fun b hb hlarge => ?_⟩
  exact Classical.choice
    (nonempty_sections_of_langWeil_bound (B.residueField b) (f.fiber b)
      (f.fiberToSpecResidueField b) d hC.le hlarge (hbound b hb))

end Langlands.AlgebraicGeometry
