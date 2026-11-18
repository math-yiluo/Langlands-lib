import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCellHeight
import Langlands.Representation.Plancherel.RenardParahoricCompactTransport
import Langlands.Representation.Plancherel.RenardDominantValuation
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The matrix height on the full minimal Levi is controlled by `H₀` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

/-- Every linear form on a finite-dimensional real vector space is bounded by each
positive-definite seminorm on that space. No norm or topology is fixed in the premise. -/
theorem exists_abs_apply_le_seminorm {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (N : Seminorm ℝ E) (hN : ∀ v, N v = 0 → v = 0)
    (f : E →ₗ[ℝ] ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, |f v| ≤ C * N v := by
  let n : AddGroupNorm E :=
    { N.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := hN }
  let : NormedAddCommGroup E := n.toNormedAddCommGroup
  let : NormedSpace ℝ E :=
    { norm_smul_le := fun a v => (map_smul_eq_mul N a v).le }
  let L : E →L[ℝ] ℝ := f.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun v => ?_⟩
  exact L.le_opNorm v

section MinimalLevi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- The uniformizer point of a cocharacter, read in the actual minimal Levi. -/
def minimalLeviUniformizer (y : cocharacterLattice S) : standardLeviPoints i ν ∅ :=
  Standard.leviPointsEquiv i ν ∅
    (rationalPoints.map (Standard.leviTorusHom i ν ∅)
      (Langlands.Plancherel.RenardCartan.uniformizerSection S (.ofAdd y)))

@[simp] theorem coe_minimalLeviUniformizer (y : cocharacterLattice S) :
    (minimalLeviUniformizer (i := i) (ν := ν) y : rationalPoints G) =
      Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) := by
  change rationalPoints.map (Standard.leviHom i ν ∅)
      (rationalPoints.map (Standard.leviTorusHom i ν ∅) _) = rationalPoints.map i _
  simp only [rationalPoints.map_apply, Category.assoc]
  change _ ≫ (Standard.leviTorusHom i ν ∅ ≫ Standard.leviHom i ν ∅).hom.hom = _
  rw [Standard.leviTorusHom_comp]

/-- The `H₀` of the actual uniformizer point is the positive scalar extension `1 ⊗ y`. -/
theorem rationalMinimalH0_minimalLeviUniformizer (y : cocharacterLattice S) :
    rationalMinimalH0 hG hi hν (minimalLeviUniformizer (i := i) (ν := ν) y) =
      (1 : ℝ) ⊗ₜ[ℤ] y := by
  unfold rationalMinimalH0 minimalLeviUniformizer
  rw [MulEquiv.symm_apply_apply]
  exact Langlands.Plancherel.RenardCartan.centralizerValuation_uniformizerSection _ _ y

/-- A compact subgroup's minimal-Levi points have zero `H₀`. The compact subgroup need not
be a special compact, and no building availability statement is used. -/
theorem rationalMinimalH0_eq_zero_of_mem_compact {K0 : Subgroup (rationalPoints G)}
    (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    {m : standardLeviPoints i ν ∅} (hm : (m : rationalPoints G) ∈ K0) :
    rationalMinimalH0 hG hi hν m = 0 := by
  let z := (Standard.leviPointsEquiv i ν ∅).symm m
  have hz : z ∈ K0.comap (rationalPoints.map (Standard.leviHom i ν ∅)) := by
    change (Standard.leviPointsEquiv i ν ∅ z : rationalPoints G) ∈ K0
    simpa [z] using hm
  have hn := Langlands.Plancherel.RenardCartan.compact_comap_le_normKernel
    (Standard.leviHom i ν ∅) (Standard.isClosedSubgroup_leviHom i ν ∅) K0 hK0 hz
  have hk : z ∈ (Langlands.BruhatTits.Cartan.centralizerValuation
      (Standard.leviTorusHom i ν ∅) (minimalLevi_restrictionEvaluation_bijective hG hi hν)).ker := by
    rw [Langlands.BruhatTits.Cartan.centralizerValuation_ker]
    exact hn
  exact congrArg Multiplicative.toAdd (show
    Langlands.BruhatTits.Cartan.centralizerValuation
      (Standard.leviTorusHom i ν ∅) (minimalLevi_restrictionEvaluation_bijective hG hi hν) z = 1
    from hk)

omit [IsAffineHom G.X.hom] in
include hi in
/-- Height along the actual cocharacter uniformizer section is bounded by every norm on
the full real cocharacter space. The matrix representation need not be a closed embedding. -/
theorem exists_rationalHeight_uniformizerPowers_le_seminorm
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : cocharacterLattice S,
      rationalHeight (F := F) ρ (Langlands.Aubert.General.uniformizerPowers i (.ofAdd y)) ≤
        C * N ((1 : ℝ) ⊗ₜ[ℤ] y) := by
  let := hi.isSplitSubtorus.1.finite_realCocharacterSpace
  obtain ⟨Idx, _, α, M, hM, hbound⟩ :=
    exists_rationalHeight_uniformizerPowers_le_sum hi.isSplitSubtorus.1 i ρ
  choose C hC hCb using fun k => exists_abs_apply_le_seminorm N hN (RealTorusSpace.eval S (α k))
  refine ⟨∑ k, M k * C k, Finset.sum_nonneg fun k _ => mul_nonneg (hM k) (hC k),
    fun y => (hbound y).trans ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hM k)
  simpa only [RealTorusSpace.eval_tmul, one_mul] using hCb k ((1 : ℝ) ⊗ₜ[ℤ] y)

/-- On all points of the minimal Levi, the height associated to `ρ` is bounded by
`1 + N(H₀)`, for a single positive constant. -/
def HasMinimalLeviHeightComparison (N : Seminorm ℝ (RealTorusSpace.V S))
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n) : Prop :=
  ∃ C > 0, ∀ m : standardLeviPoints i ν ∅,
    1 + rationalHeight (F := F) ρ (m : rationalPoints G) ≤
      C * (1 + N (rationalMinimalH0 hG hi hν m))

/-- The minimal-Levi clause of the existing Cartan covering and compactness of the compact
factors suffice to control the height on every minimal-Levi point by its `H₀` norm. -/
theorem hasMinimalLeviHeightComparison_of_cartanCovering
    [LocallyOfFiniteType G.X.hom]
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n) :
    HasMinimalLeviHeightComparison hG hi hν N ρ := by
  classical
  obtain ⟨F0, hcover⟩ := hcover
  obtain ⟨bK, hbK⟩ := hK0.bddAbove_image (continuous_rationalHeight (F := F) ρ).continuousOn
  obtain ⟨bF, hbF⟩ := (F0.image fun f : centralizerPoints i =>
    rationalHeight (F := F) ρ (f : rationalPoints G)).exists_le
  let f0 : centralizerPoints i → standardLeviPoints i ν ∅ := fun f =>
    ⟨f, by rw [standardLeviPoints_empty_eq_centralizerPoints hG hi hν]; exact f.2⟩
  obtain ⟨bH, hbH⟩ := (F0.image fun f : centralizerPoints i =>
    N (rationalMinimalH0 hG hi hν (f0 f))).exists_le
  obtain ⟨C, hC, hCy⟩ := exists_rationalHeight_uniformizerPowers_le_seminorm hi N hN ρ
  let c0 := 2 * bK + bF + C * bH
  refine ⟨1 + |c0| + C, by positivity, fun m => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hm⟩ := hcover m m.2
  obtain ⟨y, rfl⟩ := ha.1
  change (m : rationalPoints G) =
    k₁ * (f : rationalPoints G) * Langlands.Aubert.General.uniformizerPowers i y * k₂ at hm
  let m₁ : standardLeviPoints i ν ∅ := ⟨k₁, hk₁.2⟩
  let m₂ : standardLeviPoints i ν ∅ := ⟨k₂, hk₂.2⟩
  have h₁ : rationalMinimalH0 hG hi hν m₁ = 0 :=
    rationalMinimalH0_eq_zero_of_mem_compact hG hi hν hK0 hk₁.1
  have h₂ : rationalMinimalH0 hG hi hν m₂ = 0 :=
    rationalMinimalH0_eq_zero_of_mem_compact hG hi hν hK0 hk₂.1
  have hm' : m = m₁ * f0 f * minimalLeviUniformizer (i := i) (ν := ν) y.toAdd * m₂ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_minimalLeviUniformizer]
    exact hm
  have hH : rationalMinimalH0 hG hi hν m =
      rationalMinimalH0 hG hi hν (f0 f) + (1 : ℝ) ⊗ₜ[ℤ] y.toAdd := by
    rw [hm']
    simp only [rationalMinimalH0_mul, h₁, h₂, rationalMinimalH0_minimalLeviUniformizer,
      zero_add, add_zero]
  have hvec : (1 : ℝ) ⊗ₜ[ℤ] y.toAdd =
      rationalMinimalH0 hG hi hν m - rationalMinimalH0 hG hi hν (f0 f) := by
    rw [hH, add_sub_cancel_left]
  have hNy : N ((1 : ℝ) ⊗ₜ[ℤ] y.toAdd) ≤ N (rationalMinimalH0 hG hi hν m) + bH := by
    rw [hvec]
    exact (map_sub_le_add N _ _).trans
      (add_le_add_right (hbH _ (Finset.mem_image_of_mem _ hf)) _)
  have hσy := (hCy y.toAdd).trans (mul_le_mul_of_nonneg_left hNy hC)
  change rationalHeight (F := F) ρ (Langlands.Aubert.General.uniformizerPowers i y) ≤
    C * (N (rationalMinimalH0 hG hi hν m) + bH) at hσy
  have hσ₁ := rationalHeight_mul_le (F := F) ρ
    (k₁ * (f : rationalPoints G) * Langlands.Aubert.General.uniformizerPowers i y) k₂
  have hσ₂ := rationalHeight_mul_le (F := F) ρ
    (k₁ * (f : rationalPoints G)) (Langlands.Aubert.General.uniformizerPowers i y)
  have hσ₃ := rationalHeight_mul_le (F := F) ρ k₁ (f : rationalPoints G)
  have hheight : rationalHeight (F := F) ρ (m : rationalPoints G) ≤
      c0 + C * N (rationalMinimalH0 hG hi hν m) := by
    have hK₁ := hbK ⟨k₁, hk₁.1, rfl⟩
    have hK₂ := hbK ⟨k₂, hk₂.1, rfl⟩
    have hF := hbF _ (Finset.mem_image_of_mem _ hf)
    rw [hm]
    dsimp only [c0]
    linarith only [hσ₁, hσ₂, hσ₃, hK₁, hK₂, hF, hσy]
  have hNm : 0 ≤ N (rationalMinimalH0 hG hi hν m) := apply_nonneg N _
  nlinarith [le_abs_self c0, mul_nonneg (abs_nonneg c0) hNm]

end MinimalLevi

end Langlands.HarishChandraSchwartz
