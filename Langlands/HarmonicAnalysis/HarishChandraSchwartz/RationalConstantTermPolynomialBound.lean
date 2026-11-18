import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalPositivePartDecayAssembly

/-! # The full constant-term polynomial estimate from threshold and Xi comparison -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
  (hJ : J ⊆ simpleRelativeRoots i ν)
  {K : Subgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

/-- The square root of the minimal modulus on an actual minimal-Levi point. -/
def minimalLeviSqrtModulus (m : standardLeviPoints i ν ∅) : ℝ :=
  (NNReal.sqrt (rationalMinimalModulus i ν
    ⟨m, standardLevi_le_standardParabolic i ν ∅ _ m.2⟩ : ℝ≥0) : ℝ)

/-- The square root of the minimal modulus of `M_J`, restricted to the actual minimal Levi. -/
def standardLeviSqrtModulusOnMinimal (m : standardLeviPoints i ν ∅) : ℝ :=
  (NNReal.sqrt (standardLeviMinimalModulus i ν J
    ⟨m, ⟨standardLevi_le_standardParabolic i ν ∅ _ m.2,
      standardLeviPoints_empty_le hG hi hν J m.2⟩⟩ : ℝ≥0) : ℝ)

include hJ in
/-- Exact factorization of the minimal half modulus into the constant-term half modulus
and the standard-Levi minimal half modulus, on every actual minimal-Levi point. -/
theorem minimalLeviSqrtModulus_eq_mul (m : standardLeviPoints i ν ∅) :
    minimalLeviSqrtModulus (i := i) (ν := ν) m =
      ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ *
        standardLeviSqrtModulusOnMinimal hG hi hν (J := J) m := by
  have hf := rationalMinimalModulus_eq_mul hG hi hν hJ
    ⟨m, ⟨standardLevi_le_standardParabolic i ν ∅ _ m.2,
      (minimalLeviInclusion hG hi hν J m).2⟩⟩
  unfold minimalLeviSqrtModulus standardLeviSqrtModulusOnMinimal
  rw [hf, Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul]
  rw [standardHalfModulus, Complex.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact mul_comm _ _

/-- The ambient Xi function is bounded by the standard-Levi Xi times the constant-term
half modulus and a polynomial in the matrix height, on the full minimal closed chamber. -/
def HasRationalXiLeviComparison {n : ℕ} [Nonempty (Fin n)]
    (ρ : MatrixRepresentation G (Fin n)) : Prop :=
  ∃ C > 0, ∃ d : ℕ, ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
    rationalXi hKc hPK (m : rationalPoints G) ≤
      C * ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ *
        rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m) *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d

include hJ in
/-- The exact modulus factorization turns full-minimal-Levi ambient upper and Levi lower
bounds into the Xi comparison. These two analytic bounds are explicit intermediate premises. -/
theorem hasRationalXiLeviComparison_of_modulusBounds
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hupper : ∃ C > 0, ∃ d : ℕ, ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
      rationalXi hKc hPK (m : rationalPoints G) ≤
        C * minimalLeviSqrtModulus (i := i) (ν := ν) m *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d)
    (hlower : ∃ C > 0, ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
      standardLeviSqrtModulusOnMinimal hG hi hν (J := J) m ≤
        C * rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m)) :
    HasRationalXiLeviComparison hG hi hν hKc hPK hM ρ := by
  obtain ⟨Cu, hCu, d, hu⟩ := hupper
  obtain ⟨Cl, hCl, hl⟩ := hlower
  refine ⟨Cu * Cl, mul_pos hCu hCl, d, fun m hm => ?_⟩
  have hp : 0 ≤ (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d :=
    pow_nonneg (by linarith [rationalHeight_nonneg ρ (m : rationalPoints G)]) _
  calc rationalXi hKc hPK (m : rationalPoints G)
      ≤ Cu * minimalLeviSqrtModulus (i := i) (ν := ν) m *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d := hu m hm
    _ = Cu * ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ *
        standardLeviSqrtModulusOnMinimal hG hi hν (J := J) m *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d := by
      rw [minimalLeviSqrtModulus_eq_mul hG hi hν hJ]
      ring
    _ ≤ Cu * ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ *
        (Cl * rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m)) *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hl m hm) (mul_nonneg hCu.le (norm_nonneg _))) hp
    _ = _ := by ring

/-- The full constant-term estimate required by the positive-decay assembly, uniform in
the function-family parameter on a shifted closed chamber. -/
def HasRationalConstantTermPolynomialBound {κ : Type*} {n : ℕ} [Nonempty (Fin n)]
    (ρ : MatrixRepresentation G (Fin n)) (Φ : κ → standardLeviPoints i ν J → ℂ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ ∃ C : ℝ, ∃ d : ℕ, ∀ ω m,
    m ∈ rationalConstantTermThresholdRegion hG hi hν J t →
    ‖Φ ω (minimalLeviInclusion hG hi hν J m)‖ ≤
      C * rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m) *
        (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d

/-- A uniform threshold identity and a uniform original coefficient Xi bound yield the
full constant-term polynomial estimate once the actual full-chamber Xi comparison is given. -/
theorem hasRationalConstantTermPolynomialBound_of_threshold
    {κ : Type*} {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    {f : κ → rationalPoints G → ℂ} {Φ : κ → standardLeviPoints i ν J → ℂ}
    (hcomparison : HasRationalXiLeviComparison hG hi hν hKc hPK hM ρ)
    (hthreshold : ∃ t : ℝ, 0 ≤ t ∧ ∀ ω m,
      m ∈ rationalConstantTermThresholdRegion hG hi hν J t →
      f ω (m : rationalPoints G) =
        standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
          Φ ω (minimalLeviInclusion hG hi hν J m))
    (hcoeff : ∃ C > 0, ∀ ω g, ‖f ω g‖ ≤ C * rationalXi hKc hPK g) :
    HasRationalConstantTermPolynomialBound hG hi hν hKc hM ρ Φ := by
  obtain ⟨Cξ, hCξ, d, hξ⟩ := hcomparison
  obtain ⟨t, ht, hthreshold⟩ := hthreshold
  obtain ⟨Cf, hCf, hf⟩ := hcoeff
  refine ⟨t, ht, Cf * Cξ, d, fun ω m hm => ?_⟩
  have hpos : 0 < ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ :=
    norm_pos_iff.mpr (standardHalfModulus_ne_zero _)
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ *
        ‖Φ ω (minimalLeviInclusion hG hi hν J m)‖
      = ‖f ω (m : rationalPoints G)‖ := by rw [hthreshold ω m hm, norm_mul]
    _ ≤ Cf * rationalXi hKc hPK (m : rationalPoints G) := hf ω m
    _ ≤ Cf * (Cξ * ‖standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m)‖ *
        rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m) *
          (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d) :=
      mul_le_mul_of_nonneg_left (hξ m hm.1) hCf.le
    _ = _ := by ring

end Langlands.HarishChandraSchwartz
