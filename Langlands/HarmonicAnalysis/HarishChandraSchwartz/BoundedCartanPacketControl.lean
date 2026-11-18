import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCentralHeight
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # Full-height controls on bounded-root Cartan regions -/

noncomputable section

open scoped NNReal

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe uE uG u

section Comparison

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- Rescale the central decay control at order `max r 0` by the height comparison
constant, obtaining a seminorm for the full-height bound on the region. -/
def heightComparisonSeminorm (P : ℝ → Seminorm ℂ E) (D r : ℝ) : Seminorm ℂ E :=
  (Real.toNNReal (D ^ (max r 0))) • P (max r 0)

@[simp]
theorem heightComparisonSeminorm_apply (P : ℝ → Seminorm ℂ E) {D : ℝ} (hD : 0 ≤ D)
    (r : ℝ) (q : E) :
    heightComparisonSeminorm P D r q = D ^ (max r 0) * P (max r 0) q := by
  simp only [heightComparisonSeminorm, smul_apply, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (Real.rpow_nonneg hD _)]

/-- A linear height comparison turns central decay into full-height decay at
any real order without changing the input beyond a nonnegative scalar factor. -/
theorem norm_le_heightComparisonSeminorm {X : Type uG} (P : ℝ → Seminorm ℂ E)
    (f : E → X → ℂ) (Ξ σ τ : X → ℝ) {D : ℝ} (hD : 1 ≤ D) (r : ℝ) (q : E) (g : X)
    (hΞ : 0 ≤ Ξ g) (hσ : 0 ≤ σ g) (hτ : 0 ≤ τ g)
    (hcompare : 1 + σ g ≤ D * (1 + τ g))
    (hbound : ‖f q g‖ ≤ P (max r 0) q * Ξ g * (1 + τ g) ^ (-(max r 0))) :
    ‖f q g‖ ≤ heightComparisonSeminorm P D r q * Ξ g * (1 + σ g) ^ (-r) := by
  let s := max r 0
  have hs : 0 ≤ s := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have ha : 0 < 1 + τ g := by linarith
  have hb : 0 < 1 + σ g := by linarith
  have hpow : (1 + τ g) ^ (-s) ≤ D ^ s * (1 + σ g) ^ (-s) := by
    have hx := Real.rpow_pos_of_pos ha s
    have hy := Real.rpow_pos_of_pos hb s
    rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ hx hy, one_mul, ← Real.mul_rpow hD0 ha.le]
    exact Real.rpow_le_rpow hb.le hcompare hs
  have horder : (1 + σ g) ^ (-s) ≤ (1 + σ g) ^ (-r) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (le_max_left _ _))
  have hP : 0 ≤ P s q * Ξ g := mul_nonneg (apply_nonneg _ _) hΞ
  calc ‖f q g‖ ≤ P s q * Ξ g * (1 + τ g) ^ (-s) := hbound
    _ ≤ P s q * Ξ g * (D ^ s * (1 + σ g) ^ (-s)) :=
      mul_le_mul_of_nonneg_left hpow hP
    _ ≤ P s q * Ξ g * (D ^ s * (1 + σ g) ^ (-r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left horder (Real.rpow_nonneg hD0 _)) hP
    _ = heightComparisonSeminorm P D r q * Ξ g * (1 + σ g) ^ (-r) := by
      rw [heightComparisonSeminorm_apply P hD0]
      dsimp [s]
      ring

/-- Continuity of the original input controls is preserved by the rescaling. -/
theorem continuous_heightComparisonSeminorm [TopologicalSpace E]
    (P : ℝ → Seminorm ℂ E) (hP : ∀ r, Continuous (P r)) (D r : ℝ) :
    Continuous (heightComparisonSeminorm P D r) :=
  (hP (max r 0)).const_smul _

end Comparison


section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {E : Type uE} [AddCommGroup E] [Module ℂ E]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

/-- The central Fourier control yields full matrix-height bounds on every
bounded-root Cartan cell, with one input seminorm for the whole region. -/
theorem exists_fullHeightControl_on_bounded_cartan_cells
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (F0 : Finset (centralizerPoints i)) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (T : ℝ) (hT : 0 ≤ T)
    (Ξ : rationalPoints G → ℝ) (hΞ : ∀ g, 0 ≤ Ξ g)
    (P : ℝ → Seminorm ℂ E) (f : E → rationalPoints G → ℂ)
    (hbound : ∀ (r : ℝ) (q : E) (g : rationalPoints G),
      ‖f q g‖ ≤ P r q * Ξ g * (1 + ‖rationalValuationCoordinates G hG g‖) ^ (-r)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (r : ℝ) (q : E) (y : cocharacterLattice S),
      (∀ β : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν,
        |(Langlands.Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤ T) →
      ∀ g ∈ rationalCartanCell i K0 F0 y,
        ‖f q g‖ ≤ heightComparisonSeminorm P D r q * Ξ g * (1 + rationalHeight (F := F) ρ g) ^ (-r) := by
  obtain ⟨D, hD, hcompare⟩ := exists_one_add_height_le_coordinates_on_bounded_cells hG hi hν hK0c F0 ρ T hT
  refine ⟨D, hD, fun r q y hβ g hg => ?_⟩
  exact norm_le_heightComparisonSeminorm P f Ξ (rationalHeight (F := F) ρ)
    (fun g => ‖rationalValuationCoordinates G hG g‖) hD r q g (hΞ g)
    (rationalHeight_nonneg ρ g) (norm_nonneg _) (hcompare y hβ g hg) (hbound _ q g)

end Rational

end Langlands.HarishChandraSchwartz
