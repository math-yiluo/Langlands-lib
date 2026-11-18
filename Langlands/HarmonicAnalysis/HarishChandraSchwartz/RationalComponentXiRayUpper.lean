import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalComponentValuation
import Langlands.Geometry.Building.CocharacterUniformizerCone
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability

/-! # Polynomial Xi upper bounds along actual strict component rays -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)

/-- Along the powers of the component point `a`, Xi is bounded by the
radical half-modulus times a polynomial in the power. -/
abbrev HasPolynomialXiComponentRayBound
    (Ξ : rationalPoints G → ℝ) (a : rationalPoints A.toGrp) : Prop :=
  ∃ (C : ℝ) (d : ℕ), ∀ n : ℕ, 1 ≤ n →
    Ξ ((standardComponentHom hA a : rationalPoints G) ^ n) ≤
      C * ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ ^ n * (1 + n) ^ d

include hG hi hν hJ hbasis in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
/-- The separately owned upper Xi statement supplies the exact polynomial
ray bound used by the actual Jacquet exponent argument. Component points are
central in the target Levi, so the ambient minimal modulus is exactly its
unchanged radical modulus. -/
theorem exists_rationalXi_component_ray_bound_of_upperBound
    (hupper : RationalXiUpperBoundStatement.{u})
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ)
    (a : rationalPoints A.toGrp)
    (ha : a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν J q)) :
    HasPolynomialXiComponentRayBound hA (rationalXi hKc hPK) a := by
  have hbasis' := hbasis
  obtain ⟨B0, hB0, hBJ⟩ := hbasis'
  obtain ⟨_, A0, q0, hA0, _⟩ := hBJ ∅ (Set.empty_subset _)
  obtain ⟨d, hd⟩ := hupper F G hG S i hi ν hν K0 hbasis A0 q0 hA0
    K.toSubgroup K.isOpen hKc hPK N ρ hρ
  obtain ⟨C, hC⟩ := hd 1 1
  let m := standardComponentHom hA a
  let g : rationalPoints G := m
  have hgP : g ∈ standardParabolicPoints i ν ∅ :=
    standardLevi_le_standardParabolic i ν ∅ _ (map_mem_standardLeviPoints_empty q a)
  let gP : standardParabolicPoints i ν ∅ := ⟨g, hgP⟩
  have hδ : rationalMinimalModulus i ν gP = standardRadicalModulus i ν J m := by
    exact rationalMinimalModulus_eq_standardUnipotentModulus_of_commute hG hi hν hJ
      ⟨g, hgP, m.property⟩ (fun y hy =>
        congrArg Subtype.val (standardComponentHom_commute hA a ⟨y, hy⟩))
  have hs : (NNReal.sqrt (rationalMinimalModulus i ν gP : ℝ≥0) : ℝ) =
      ‖standardHalfModulus i ν J m‖ := by
    rw [hδ, standardHalfModulus, Complex.norm_of_nonneg (NNReal.coe_nonneg _)]
  have hsPow : ∀ n : ℕ,
      (NNReal.sqrt (rationalMinimalModulus i ν (gP ^ n) : ℝ≥0) : ℝ) =
        ‖standardHalfModulus i ν J m‖ ^ n := by
    intro n
    change (NNReal.sqrtHom (rationalMinimalModulus i ν (gP ^ n) : ℝ≥0) : ℝ) = _
    rw [map_pow, Units.val_pow_eq_pow_val, map_pow, NNReal.coe_pow]
    change (NNReal.sqrt (rationalMinimalModulus i ν gP : ℝ≥0) : ℝ) ^ n = _
    rw [hs]
  have haPlus : a ∈ CocharacterUniformizer.CAplus F A
      (standardParabolicComponentCharacters i ν J q) :=
    ⟨ha.1, fun α hα => (ha.2 α hα).le⟩
  have hpowPlus : ∀ n : ℕ, g ^ n ∈ standardComponentCAplus i ν ∅ q0 := by
    intro n
    have han : a ^ n ∈ CocharacterUniformizer.CAplus F A
        (standardParabolicComponentCharacters i ν J q) := by
      apply (CocharacterUniformizer.mem_CAplusMonoid _ _ _ _).mp
      exact (CocharacterUniformizer.CAplusMonoid F A _).pow_mem
        ((CocharacterUniformizer.mem_CAplusMonoid _ _ _ _).mpr haPlus) n
    have hgn : g ^ n ∈ standardComponentCAplus i ν J q := by
      refine ⟨a ^ n, han, ?_⟩
      change ((standardComponentHom hA) (a ^ n) : rationalPoints G) = _
      rw [map_pow, Subgroup.coe_pow]
    obtain ⟨y, hy, _, hy0⟩ := hA.exists_eq_uniformizerPowers hJ hgn
    rw [hy]
    exact (uniformizerPowers_mem_standardComponentChambers hi
      ⟨ν, isStandardCocharacter_empty_self i ν⟩ hA0 y (by simp) hy0).2
  let B : ℝ := 1 + rationalHeight (F := F) ρ 1 + rationalHeight (F := F) ρ g
  have hB0 : 0 < B := by
    have h1 := rationalHeight_nonneg (F := F) ρ 1
    have hg := rationalHeight_nonneg (F := F) ρ g
    dsimp only [B]
    linarith
  refine ⟨max C 1 * B ^ d, d, fun n _hn => ?_⟩
  have huppern := hC (g ^ n) ((gP ^ n).property) (hpowPlus n)
  simp only [one_mul, mul_one] at huppern
  have hsPow' : (NNReal.sqrt (rationalMinimalModulus i ν
      ⟨g ^ n, (gP ^ n).property⟩ : ℝ≥0) : ℝ) =
      ‖standardHalfModulus i ν J m‖ ^ n := hsPow n
  rw [hsPow'] at huppern
  have hheight : (1 + rationalHeight (F := F) ρ (g ^ n)) ^ d ≤
      B ^ d * (1 + n) ^ d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by linarith [rationalHeight_nonneg (F := F) ρ (g ^ n)])
    have hp := le_add_nsmul_of_subadditive (rationalHeight_mul_le (F := F) ρ) g n
    have h1 := rationalHeight_nonneg (F := F) ρ 1
    have hg := rationalHeight_nonneg (F := F) ρ g
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp only [B]
    nlinarith
  calc rationalXi hKc hPK (g ^ n)
      ≤ C * ‖standardHalfModulus i ν J m‖ ^ n *
          (1 + rationalHeight (F := F) ρ (g ^ n)) ^ d := huppern
    _ ≤ max C 1 * ‖standardHalfModulus i ν J m‖ ^ n *
          (1 + rationalHeight (F := F) ρ (g ^ n)) ^ d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (pow_nonneg (by linarith [rationalHeight_nonneg (F := F) ρ (g ^ n)]) _)
    _ ≤ max C 1 * ‖standardHalfModulus i ν J m‖ ^ n * (B ^ d * (1 + n) ^ d) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = max C 1 * B ^ d * ‖standardHalfModulus i ν J m‖ ^ n * (1 + n) ^ d := by ring

end Langlands.HarishChandraSchwartz
