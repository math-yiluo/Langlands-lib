import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralProjection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness
import Langlands.GroupScheme.Rational.CharacterPolynomialGrowth
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Global.Hecke.LatticePoissonGeneral

/-! # Heights on the split centre: proof of `RationalSplitCenterHeightStatement`

For a connected reductive `G` over a nonarchimedean local field, a split component `s : T → G`
with image `A_G(F)` and a closed matrix representation `ρ` with height `σ`, this module proves
the two height properties of `RationalSplitCenterHeightStatement`. The integer valuations
`H_χ(g)` of finitely many rational characters `χ_j` of `G` control `σ` on `A_G(F)` from above
(`exists_splitCenter_comparison`), and every `H_χ` is bounded by a multiple of `1 + σ`
(`exists_abs_valuation_le`). Clause 1 follows since `H_χ(a g) = H_χ(a)` for
`g ∈ G¹`; clause 2 by summing over the fibres of `a ↦ (H_{χ_j}(a))_j`, which are translates of a
subset of the compact set `A_G(F) ∩ G¹`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

namespace SplitCenterHeight

section Subadditive

variable {M : Type*} [AddCommGroup M] (τ : M → ℝ)

/-- A subadditive, even function with `τ 0 = 0` satisfies `τ (n • x) ≤ |n| τ x`. -/
theorem zsmul_le_natAbs_mul (h0 : τ 0 = 0) (hadd : ∀ x y, τ (x + y) ≤ τ x + τ y)
    (hneg : ∀ x, τ (-x) = τ x) (n : ℤ) (x : M) :
    τ (n • x) ≤ (n.natAbs : ℝ) * τ x := by
  have hnat : ∀ k : ℕ, τ (k • x) ≤ (k : ℝ) * τ x := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      rw [succ_nsmul]
      calc τ (k • x + x) ≤ τ (k • x) + τ x := hadd _ _
        _ ≤ (k : ℝ) * τ x + τ x := by linarith
        _ = ((k + 1 : ℕ) : ℝ) * τ x := by push_cast; ring
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [natCast_zsmul, Int.natAbs_natCast]
    exact hnat k
  · rw [neg_zsmul, natCast_zsmul, hneg, Int.natAbs_neg, Int.natAbs_natCast]
    exact hnat k

/-- A subadditive, even function with `τ 0 = 0` satisfies
`τ (∑ j, n j • b j) ≤ ∑ j, |n j| τ (b j)`. -/
theorem sum_zsmul_le {I : Type*} [Fintype I] (h0 : τ 0 = 0)
    (hadd : ∀ x y, τ (x + y) ≤ τ x + τ y) (hneg : ∀ x, τ (-x) = τ x) (n : I → ℤ)
    (b : I → M) :
    τ (∑ j, n j • b j) ≤ ∑ j, |(n j : ℝ)| * τ (b j) := by
  refine (Finset.le_sum_of_subadditive τ h0.le hadd _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)
  have h := zsmul_le_natAbs_mul τ h0 hadd hneg (n j) (b j)
  rwa [Nat.cast_natAbs, Int.cast_abs] at h

end Subadditive

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The integer valuation `H_χ(g) = ord_F(χ(g))` of a rational character `χ` at `g ∈ G(F)`, so
that `|χ(g)|_F = q^{-H_χ(g)}`. -/
abbrev valuation (χ : rationalCharacters G) (g : rationalPoints G) : ℤ :=
  (Plancherel.rationalCharacterValuation G g).toAdd χ

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `H_χ(g h) = H_χ(g) + H_χ(h)`. -/
theorem valuation_mul (χ : rationalCharacters G) (g h : rationalPoints G) :
    valuation χ (g * h) = valuation χ g + valuation χ h := by
  simp only [valuation, map_mul, toAdd_mul, AddMonoidHom.add_apply]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `H_χ(g⁻¹) = -H_χ(g)`. -/
theorem valuation_inv (χ : rationalCharacters G) (g : rationalPoints G) :
    valuation χ g⁻¹ = -valuation χ g := by
  simp only [valuation, map_inv, toAdd_inv, AddMonoidHom.neg_apply]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Every `H_χ` vanishes on `G¹`. -/
theorem valuation_eq_zero_of_mem {g : rationalPoints G}
    (hg : g ∈ Plancherel.rationalCommonNormKernel G) (χ : rationalCharacters G) :
    valuation χ g = 0 :=
  (Plancherel.mem_rationalCommonNormKernel_iff_valuation G g).mp hg χ

/-- `H_χ` is locally constant: it factors through the discrete valuation image. -/
theorem continuous_valuation (χ : rationalCharacters G) :
    Continuous (valuation (G := G) χ) := by
  have h : Continuous ((fun y : Plancherel.rationalDiscreteValuationImage G =>
      (Subtype.val (p := fun x => x ∈ Plancherel.rationalCharacterValuationImage G) y).toAdd χ) ∘
      (Plancherel.rationalValuationImageProjection G)) :=
    continuous_of_discreteTopology.comp (Plancherel.continuous_rationalValuationImageProjection G)
  exact h

omit [LocallyOfFiniteType G.X.hom] in
/-- **Upper bound for the valuations**: `|H_χ(g)| ≤ C (1 + σ(g))` for every rational character
`χ` and every closed matrix representation `ρ`. -/
theorem exists_abs_valuation_le {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ) (χ : rationalCharacters G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
      |(valuation χ g : ℝ)| ≤ C * (1 + rationalHeight (F := F) ρ g) := by
  obtain ⟨C, hC, hb⟩ :=
    MatrixRepresentation.rationalCharacter_abs_log_rationalMatrixNorm_bound F ρ hρ χ
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hlog : 0 < Real.log (LocalField.residueCardinality F : ℝ) := Real.log_pos hq
  refine ⟨C / Real.log (LocalField.residueCardinality F : ℝ), div_pos hC hlog, fun g => ?_⟩
  have h := hb g
  have hspec := Plancherel.rationalNormLogarithm_spec G g χ
  rw [Plancherel.rationalNormLogarithm_eq_intValuation] at hspec
  rw [← hspec, Real.log_rpow (by linarith), abs_mul, abs_neg, abs_of_pos hlog] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
  exact h

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Restriction of a character along `s` computes its valuation on `A_G(F)`. -/
theorem valuation_map (χ : rationalCharacters G) (t : rationalPoints T.toGrp) :
    valuation χ (rationalPoints.map s t) =
      (Plancherel.rationalCharacterValuation T.toGrp t).toAdd (characterRestrict s χ) :=
  (Plancherel.rationalCharacterValuation_characterRestrict s χ t).symm

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `s` maps the norm-one points of `T(F)` into `G¹`. -/
theorem map_mem_commonNormKernel {t : rationalPoints T.toGrp}
    (ht : t ∈ Plancherel.rationalCommonNormKernel T.toGrp) :
    rationalPoints.map s t ∈ Plancherel.rationalCommonNormKernel G := by
  rw [Plancherel.mem_rationalCommonNormKernel_iff_valuation]
  intro χ
  rw [← Plancherel.rationalCharacterValuation_characterRestrict]
  exact (Plancherel.mem_rationalCommonNormKernel_iff_valuation _ t).mp ht _

/-- **Comparison on the split centre.** For a split component `s : T → G` there are finitely
many rational characters `χ_j` of `G` and constants `B, β ≥ 0` with
`σ(a) ≤ B + β ∑_j |H_{χ_j}(a)|` on `A_G(F)`, and a point of `A_G(F)` at which every `H_{χ_j}`
vanishes lies in `G¹`. -/
theorem exists_splitCenter_comparison (hG : IsConnectedReductive G) (hs : IsSplitComponent s)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n) :
    ∃ (I : Type u) (_ : Fintype I) (χ : I → rationalCharacters G) (B β : ℝ), 0 ≤ B ∧ 0 ≤ β ∧
      (∀ a ∈ (rationalPoints.map s).range,
        rationalHeight (F := F) ρ a ≤ B + β * ∑ j, |(valuation (χ j) a : ℝ)|) ∧
      (∀ a ∈ (rationalPoints.map s).range, (∀ j, valuation (χ j) a = 0) →
        a ∈ Plancherel.rationalCommonNormKernel G) := by
  have hT : IsSplitTorus T.toGrp := hs.1.1.1
  obtain ⟨I, hI, ⟨e⟩⟩ := hT.exists_cocharacterCoordinates
  let : Fintype I := Fintype.ofFinite I
  have := CocharacterUniformizer.latticePairing_isPerfPair F T hT
  have hα : ∀ k : I, ∃ α : characterLattice T, ∀ y, latticePairing T α y = e y k := fun k => by
    obtain ⟨α, hα⟩ := (LinearMap.IsPerfPair.bijective_left (latticePairing T)).2
      ((LinearMap.proj k).comp e.toLinearMap)
    exact ⟨α, fun y => LinearMap.congr_fun hα y⟩
  choose α hα using hα
  have hfi := hs.finiteIndex_range_characterRestrict hG
  set M := (characterRestrict s).range.index with hM
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have hMpos : (0 : ℝ) < M := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hM0)
  have hχ : ∀ k, ∃ χ : rationalCharacters G, characterRestrict s χ =
      M • (rationalCharacters.equivCharacterLattice T).symm (α k) := fun k =>
    AddSubgroup.nsmul_index_mem (characterRestrict s).range _
  choose χ hχ using hχ
  have hsec := CocharacterUniformizer.isUniformizerLatticeSection F T hT
  have hval : ∀ (t : rationalPoints T.toGrp) (c : Multiplicative (cocharacterLattice T)),
      t * (CocharacterUniformizer.latticeSection F T c)⁻¹ ∈
        Plancherel.rationalCommonNormKernel T.toGrp →
      ∀ k, valuation (χ k) (rationalPoints.map s t) = (M : ℤ) * e c.toAdd k := by
    intro t c hc k
    rw [valuation_map, hχ k, map_nsmul,
      (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff F T t c).mp hc (α k), hα k,
      nsmul_eq_mul]
  -- the height along the lattice section
  let τ : cocharacterLattice T → ℝ := fun y => rationalHeight (F := F) ρ
    (rationalPoints.map s (CocharacterUniformizer.latticeSection F T (Multiplicative.ofAdd y)))
  have hτ0 : τ 0 = 0 := by
    simp only [τ, ofAdd_zero, map_one, rationalHeight_one]
  have hτadd : ∀ x y, τ (x + y) ≤ τ x + τ y := fun x y => by
    simp only [τ, ofAdd_add, map_mul]
    exact rationalHeight_mul_le ρ _ _
  have hτneg : ∀ x, τ (-x) = τ x := fun x => by
    simp only [τ, ofAdd_neg, map_inv, rationalHeight_inv]
  have hτnn : ∀ x, 0 ≤ τ x := fun x => rationalHeight_nonneg ρ _
  let b := (Pi.basisFun ℤ I).map e.symm
  have hbrepr : ∀ y k, b.repr y k = e y k := fun y k => by
    simp [b]
  have hτle : ∀ y, τ y ≤ (∑ k, τ (b k)) * ∑ k, |(e y k : ℝ)| := fun y => by
    have h := sum_zsmul_le τ hτ0 hτadd hτneg (fun k => b.repr y k) b
    rw [b.sum_repr y] at h
    refine h.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hbrepr, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hτnn (b j)) (Finset.mem_univ k)) (abs_nonneg _)
  -- the bound on the compact set `A_G(F) ∩ G¹`
  have hK := isCompact_splitComponent_inf_commonNormKernel G s hG hs
  obtain ⟨B, hB⟩ := (hK.image (continuous_rationalHeight (F := F) ρ)).bddAbove
  set β₀ := ∑ k, τ (b k)
  have hβ₀ : 0 ≤ β₀ := Finset.sum_nonneg fun k _ => hτnn (b k)
  refine ⟨I, inferInstance, χ, max B 0, β₀ / M, le_max_right _ _,
    div_nonneg hβ₀ hMpos.le, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨c, hc, -⟩ := hsec.2.2 t
    have ht : t = (t * (CocharacterUniformizer.latticeSection F T c)⁻¹) *
        CocharacterUniformizer.latticeSection F T c := by group
    have h0 : rationalPoints.map s (t * (CocharacterUniformizer.latticeSection F T c)⁻¹) ∈
        ((rationalPoints.map s).range ⊓ Plancherel.rationalCommonNormKernel G :
          Subgroup (rationalPoints G)) :=
      ⟨⟨_, rfl⟩, map_mem_commonNormKernel hc⟩
    have hB0 := hB ⟨_, h0, rfl⟩
    have h1 := rationalHeight_mul_le (F := F) ρ
      (rationalPoints.map s (t * (CocharacterUniformizer.latticeSection F T c)⁻¹))
      (rationalPoints.map s (CocharacterUniformizer.latticeSection F T c))
    rw [← map_mul, ← ht] at h1
    have h2 := hτle c.toAdd
    have h3 : ∑ k, |(e c.toAdd k : ℝ)| = (∑ k, |(valuation (χ k) (rationalPoints.map s t) : ℝ)|) / M := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hval t c hc k, Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast,
        mul_div_cancel_left₀ _ hM0]
    have h4 : τ c.toAdd = rationalHeight (F := F) ρ
        (rationalPoints.map s (CocharacterUniformizer.latticeSection F T c)) := rfl
    rw [h3, h4] at h2
    have h5 : β₀ * ((∑ k, |(valuation (χ k) (rationalPoints.map s t) : ℝ)|) / M) =
        β₀ / M * ∑ k, |(valuation (χ k) (rationalPoints.map s t) : ℝ)| := by ring
    have := le_max_left B 0
    linarith
  · rintro _ ⟨t, rfl⟩ hv
    obtain ⟨c, hc, -⟩ := hsec.2.2 t
    have hc0 : c = 1 := by
      have : c.toAdd = 0 := by
        apply e.injective
        funext k
        have h := hval t c hc k
        rw [hv k] at h
        have : (M : ℤ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
        rw [map_zero, Pi.zero_apply]
        exact (mul_eq_zero.mp h.symm).resolve_left this
      exact this
    subst hc0
    rw [map_one, inv_one, mul_one] at hc
    exact map_mem_commonNormKernel hc

end SplitCenterHeight

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

open SplitCenterHeight Langlands.Global.Hecke in
/-- **Heights on the split centre** (`RationalSplitCenterHeightStatement`): for a split
component `s : T → G` of a connected reductive `G` and a closed matrix representation `ρ` with
height `σ`, (1) `1 + σ(a) ≤ C (1 + σ(a g))` for `a ∈ A_G(F)` and `g ∈ G¹`, and (2) for every Haar
measure on `A_G(F)` some `(1 + σ)^{-r₀}` is integrable. -/
theorem rationalSplitCenterHeight : RationalSplitCenterHeightStatement.{u} := by
  intro F _ _ _ _ G _ _ hG T s hs N _ ρ hρ
  obtain ⟨I, _, χ, B, β, hB, hβ, hup, hker⟩ := exists_splitCenter_comparison hG hs ρ
  choose C hC hCb using fun j => exists_abs_valuation_le ρ hρ (χ j)
  set Γ := ∑ j, C j with hΓdef
  have hΓ : 0 ≤ Γ := Finset.sum_nonneg fun j _ => (hC j).le
  -- `∑_j |H_{χ_j}(g)| ≤ Γ (1 + σ(g))`
  have hsum : ∀ g, ∑ j, |(valuation (χ j) g : ℝ)| ≤ Γ * (1 + rationalHeight (F := F) ρ g) :=
    fun g => by
      rw [hΓdef, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hCb j g
  refine ⟨⟨1 + B + β * Γ, fun a ha g hg => ?_⟩, fun muA _ => ?_⟩
  · have hvag : ∀ j, valuation (χ j) (a * g) = valuation (χ j) a := fun j => by
      rw [valuation_mul, valuation_eq_zero_of_mem hg, add_zero]
    have h1 := hup a ha
    have h2 := hsum (a * g)
    simp only [hvag] at h2
    have h3 := rationalHeight_nonneg (F := F) ρ (a * g)
    have h4 := mul_le_mul_of_nonneg_left h2 hβ
    nlinarith [mul_nonneg hB h3, mul_nonneg (mul_nonneg hβ hΓ) h3]
  · -- the valuation coordinates on `A_G(F)`
    let Φ : (rationalPoints.map s).range → (I → ℤ) := fun a j =>
      valuation (χ j) (a : rationalPoints G)
    have hΦc : Continuous Φ :=
      continuous_pi fun j => (continuous_valuation (χ j)).comp continuous_subtype_val
    have hΦm : Measurable Φ :=
      measurable_to_countable' fun m => ((isOpen_discrete {m}).preimage hΦc).measurableSet
    -- the summable majorant
    set r : ℝ := Fintype.card I + 1 with hrdef
    have hr0 : 0 ≤ r := by positivity
    let bI := Pi.basisFun ℝ I
    let w : (I → ℤ) → ℝ := fun m => (1 + Γ) ^ r * (1 + ‖latticeVec bI m‖) ^ (-r)
    have hw0 : ∀ m, 0 ≤ w m := fun m =>
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _)
    have hws : Summable w :=
      (summable_one_add_norm_latticeVec_rpow bI (r := r)
        (by rw [Module.finrank_fintype_fun_eq_card, hrdef]; linarith)).mul_left _
    have hnorm : ∀ m : I → ℤ, ‖latticeVec bI m‖ ≤ ∑ j, |(m j : ℝ)| := fun m => by
      have hv : latticeVec bI m = fun j => (m j : ℝ) := by
        funext j
        simpa [bI] using repr_latticeVec bI m j
      rw [hv, pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
      intro j
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun j => |(m j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
    have hpt : ∀ a : (rationalPoints.map s).range,
        (1 + rationalHeight (F := F) ρ a) ^ (-r) ≤ w (Φ a) := fun a => by
      refine rpow_neg_le_of_le_mul (by positivity) (by linarith) hr0 ?_
      have h1 := hnorm (Φ a)
      have h2 := hsum a
      have h3 := rationalHeight_nonneg (F := F) ρ a
      nlinarith
    -- the fibres of `Φ` have measure at most that of the compact set `A_G(F) ∩ G¹`
    let K : Set (rationalPoints.map s).range := Subtype.val ⁻¹'
      (((rationalPoints.map s).range ⊓ Plancherel.rationalCommonNormKernel G :
        Subgroup (rationalPoints G)) : Set (rationalPoints G))
    have hKc : IsCompact K := by
      rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
      · exact isCompact_splitComponent_inf_commonNormKernel G s hG hs
      · rw [Subtype.range_coe_subtype]
        exact fun x hx => hx.1
    have hfib : ∀ m, muA (Φ ⁻¹' {m}) ≤ muA K := fun m => by
      rcases (Φ ⁻¹' {m}).eq_empty_or_nonempty with h | ⟨a₀, ha₀⟩
      · rw [h, measure_empty]
        exact bot_le
      · calc muA (Φ ⁻¹' {m}) ≤ muA ((fun h => a₀⁻¹ * h) ⁻¹' K) := measure_mono ?_
          _ = muA K := measure_preimage_mul muA a₀⁻¹ K
        intro a ha
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ha₀
        refine ⟨(a₀⁻¹ * a).2, hker _ (a₀⁻¹ * a).2 fun j => ?_⟩
        change valuation (χ j) ((a₀ : rationalPoints G)⁻¹ * a) = 0
        rw [valuation_mul, valuation_inv]
        have h1 := congrFun ha j
        have h2 := congrFun ha₀ j
        simp only [Φ] at h1 h2
        rw [h1, h2, neg_add_cancel]
    have hKfin : muA K < ⊤ := hKc.measure_lt_top
    refine ⟨r, ?_⟩
    calc ∫⁻ a, ENNReal.ofReal ((1 + rationalHeight (F := F) ρ a) ^ (-r)) ∂muA
        ≤ ∫⁻ a, ENNReal.ofReal (w (Φ a)) ∂muA :=
          lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hpt a)
      _ = ∫⁻ m, ENNReal.ofReal (w m) ∂(muA.map Φ) :=
          (lintegral_map (f := fun m => ENNReal.ofReal (w m)) (measurable_of_countable _)
            hΦm).symm
      _ = ∑' m, ENNReal.ofReal (w m) * muA.map Φ {m} := lintegral_countable' _
      _ ≤ ∑' m, ENNReal.ofReal (w m) * muA K := ENNReal.tsum_le_tsum fun m => by
          rw [Measure.map_apply hΦm (measurableSet_singleton m)]
          exact mul_le_mul_of_nonneg_left (hfib m) bot_le
      _ = ENNReal.ofReal (∑' m, w m) * muA K := by
          rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg hw0 hws]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin

end Langlands.HarishChandraSchwartz
