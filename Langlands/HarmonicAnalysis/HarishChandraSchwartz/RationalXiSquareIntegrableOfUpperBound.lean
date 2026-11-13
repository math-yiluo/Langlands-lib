import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LatticeQuotientVolumeBound
import Langlands.Representation.Aubert.General.RationalRayVolumeIndex
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics
import Langlands.Representation.Jacquet.StandardDynamicConstantTerm
import Langlands.Representation.Plancherel.RationalUniformizerCoordinateHeightProof
import Langlands.GroupScheme.Rational.CharacterPolynomialGrowth
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.Geometry.Building.CocharacterUniformizerProof

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Cells

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The Cartan cell `⋃_{f ∈ F₀} K₀ ϖ^y f K₀` of a cocharacter `y` of `S`, for a subgroup `K₀`
of `G(F)` and a finite set `F₀` of points of the centralizer of `S`, where
`ϖ^y = i(y(ϖ))` is the uniformizer power of `y`. -/
def rationalCartanCell (i : S.toGrp ⟶ G) (K0 : Subgroup (rationalPoints G))
    (F0 : Finset (centralizerPoints i))
    (y : cocharacterLattice S) : Set (rationalPoints G) :=
  {g | ∃ k₁ ∈ K0, ∃ k₂ ∈ K0, ∃ f ∈ F0,
    g = k₁ * Aubert.General.uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) * k₂}

end Cells

section Translates

/-- A compact subset `C` of a topological group is covered by finitely many left translates
`c⁻¹ K` of an open subgroup `K`. -/
theorem exists_finset_mul_mem_of_isCompact {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {K : Subgroup H} (hK : IsOpen (K : Set H)) {C : Set H}
    (hC : IsCompact C) : ∃ t : Finset H, ∀ x ∈ C, ∃ c ∈ t, c * x ∈ K := by
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC
    (show (interior (K : Set H)).Nonempty from ⟨1, by rw [hK.interior_eq]; exact K.one_mem⟩)
  refine ⟨t, fun x hx => ?_⟩
  obtain ⟨c, hc, hx'⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact ⟨c, hc, hx'⟩

/-- For a left-invariant measure `μ`, the union `⋃_{f ∈ F₀} K₀ w φ(f) K₀` over a finite family
of elements `φ(f)` commuting with `w` has measure at most `N μ(K₀ w K₀)`, with `N` independent
of `w`: the compact set `φ(f)⁻¹ K₀ φ(f)` is covered by finitely many translates `c⁻¹ K₀`, so
`K₀ w φ(f) K₀ = φ(f) (φ(f)⁻¹ K₀ φ(f)) w K₀` lies in finitely many left translates of
`K₀ w K₀`. -/
theorem exists_measure_cell_le_doubleCoset {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [MeasurableMul H] (mu : Measure H)
    [mu.IsMulLeftInvariant] {K0 : Subgroup H} (hK0o : IsOpen (K0 : Set H))
    (hK0c : IsCompact (K0 : Set H)) {Idx : Type*} (F0 : Finset Idx) (φ : Idx → H) :
    ∃ N : ℕ, ∀ w : H, (∀ f ∈ F0, φ f * w = w * φ f) →
      mu {g | ∃ k₁ ∈ K0, ∃ k₂ ∈ K0, ∃ f ∈ F0, g = k₁ * w * φ f * k₂} ≤
        N * mu (DoubleCoset.doubleCoset w K0 K0) := by
  have hC (f : Idx) : IsCompact ((fun k => (φ f)⁻¹ * k * φ f) '' (K0 : Set H)) :=
    hK0c.image (by fun_prop)
  choose t ht using fun f => exists_finset_mul_mem_of_isCompact hK0o (hC f)
  refine ⟨∑ f ∈ F0, (t f).card, fun w hw => ?_⟩
  set D := DoubleCoset.doubleCoset w (K0 : Set H) K0
  have hsub : {g | ∃ k₁ ∈ K0, ∃ k₂ ∈ K0, ∃ f ∈ F0, g = k₁ * w * φ f * k₂} ⊆
      ⋃ f ∈ F0, ⋃ c ∈ t f, (φ f * c⁻¹) • D := by
    rintro g ⟨k₁, hk₁, k₂, hk₂, f, hf, rfl⟩
    obtain ⟨c, hc, hck⟩ := ht f _ ⟨k₁, hk₁, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨f, hf, Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩⟩
    refine Set.mem_smul_set.mpr ⟨c * ((φ f)⁻¹ * k₁ * φ f) * w * k₂,
      DoubleCoset.mem_doubleCoset.mpr ⟨_, hck, k₂, hk₂, rfl⟩, ?_⟩
    rw [smul_eq_mul]
    calc φ f * c⁻¹ * (c * ((φ f)⁻¹ * k₁ * φ f) * w * k₂) = k₁ * (φ f * w) * k₂ := by group
      _ = k₁ * w * φ f * k₂ := by rw [hw f hf]; group
  calc mu {g | ∃ k₁ ∈ K0, ∃ k₂ ∈ K0, ∃ f ∈ F0, g = k₁ * w * φ f * k₂}
      ≤ mu (⋃ f ∈ F0, ⋃ c ∈ t f, (φ f * c⁻¹) • D) := measure_mono hsub
    _ ≤ ∑ f ∈ F0, mu (⋃ c ∈ t f, (φ f * c⁻¹) • D) := measure_biUnion_finset_le _ _
    _ ≤ ∑ f ∈ F0, ∑ c ∈ t f, mu ((φ f * c⁻¹) • D) :=
      Finset.sum_le_sum fun f _ => measure_biUnion_finset_le _ _
    _ = ∑ f ∈ F0, ((t f).card : ℝ≥0∞) * mu D := by
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
    _ = ((∑ f ∈ F0, (t f).card : ℕ) : ℝ≥0∞) * mu D := by
      rw [← Finset.sum_mul, Nat.cast_sum]

end Translates

section Bounds

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [LocallyOfFiniteType G.X.hom] in
/-- The covering clause of the Cartan decomposition, in terms of the cells
`rationalCartanCell`: every point lies in the cell of a dominant cocharacter. -/
theorem exists_mem_rationalCartanCell {K0 : Subgroup (rationalPoints G)}
    {F0 : Finset (centralizerPoints i)}
    (hF0 : ∀ g : rationalPoints G,
      ∃ (k₁ k₂ : rationalPoints G) (f : centralizerPoints i) (a : rationalPoints S.toGrp),
        k₁ ∈ K0 ∧ k₂ ∈ K0 ∧ f ∈ F0 ∧
          a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν) ∧
          g = k₁ * (f : rationalPoints G) * rationalPoints.map i a * k₂)
    (g : rationalPoints G) :
    ∃ y : cocharacterLattice S,
      (∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
        0 ≤ Aubert.General.simpleRootPairing i ν β y) ∧ g ∈ rationalCartanCell i K0 F0 y := by
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hrep⟩ := hF0 g
  obtain ⟨x, rfl, hx⟩ := Aubert.General.exists_cocharacter_of_mem_CAplus i ν ha
  have he : rationalPoints.map i (CocharacterUniformizer.latticeSection F S (.ofAdd x)) =
      Aubert.General.uniformizerPowers i (.ofAdd x) := rfl
  rw [he] at hrep
  have hxT : Aubert.General.uniformizerPowers i (.ofAdd x) ∈
      Aubert.General.RationalPointFamily.torusPoints i :=
    (Aubert.General.RationalPointFamily.mem_torusPoints i _).mpr
      ⟨CocharacterUniformizer.latticeSection F S (.ofAdd x), rfl⟩
  have hcomm : (f : rationalPoints G) * Aubert.General.uniformizerPowers i (.ofAdd x) =
      Aubert.General.uniformizerPowers i (.ofAdd x) * (f : rationalPoints G) :=
    (Aubert.General.RationalPointFamily.centralizerPoints_le_pointCentralizer i
      f.property _ hxT).symm
  refine ⟨x, hx, k₁, hk₁, k₂, hk₂, f, hf, ?_⟩
  rw [hrep, mul_assoc k₁, hcomm, ← mul_assoc]

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)

/-- On a Cartan cell, the height of the uniformizer power is bounded by the height of any
point of the cell, up to an additive constant independent of the cell. -/
theorem exists_rationalHeight_uniformizerPowers_le {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G))) (F0 : Finset (centralizerPoints i)) :
    ∃ B : ℝ, ∀ (y : cocharacterLattice S), ∀ g ∈ rationalCartanCell i K0 F0 y,
      rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y)) ≤
        rationalHeight (F := F) ρ g + B := by
  obtain ⟨b, hb⟩ := hK0c.bddAbove_image (continuous_rationalHeight (F := F) ρ).continuousOn
  obtain ⟨b', hb'⟩ := (F0.image fun f : centralizerPoints i => rationalHeight (F := F) ρ
    (f : rationalPoints G)⁻¹).exists_le
  refine ⟨2 * b + b', fun y g hg => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, rfl⟩ := hg
  set w := Aubert.General.uniformizerPowers i (.ofAdd y)
  have hw : w = k₁⁻¹ * (k₁ * w * (f : rationalPoints G) * k₂) * k₂⁻¹ *
      (f : rationalPoints G)⁻¹ := by group
  have h₁ : rationalHeight (F := F) ρ k₁⁻¹ ≤ b := by
    rw [rationalHeight_inv]; exact hb ⟨k₁, hk₁, rfl⟩
  have h₂ : rationalHeight (F := F) ρ k₂⁻¹ ≤ b := by
    rw [rationalHeight_inv]; exact hb ⟨k₂, hk₂, rfl⟩
  have h₃ : rationalHeight (F := F) ρ (f : rationalPoints G)⁻¹ ≤ b' :=
    hb' _ (Finset.mem_image_of_mem _ hf)
  have := rationalHeight_mul_le (F := F) ρ
    (k₁⁻¹ * (k₁ * w * (f : rationalPoints G) * k₂) * k₂⁻¹) (f : rationalPoints G)⁻¹
  have := rationalHeight_mul_le (F := F) ρ
    (k₁⁻¹ * (k₁ * w * (f : rationalPoints G) * k₂)) k₂⁻¹
  have := rationalHeight_mul_le (F := F) ρ k₁⁻¹ (k₁ * w * (f : rationalPoints G) * k₂)
  have hw' : rationalHeight (F := F) ρ w = rationalHeight (F := F) ρ
      (k₁⁻¹ * (k₁ * w * (f : rationalPoints G) * k₂) * k₂⁻¹ * (f : rationalPoints G)⁻¹) :=
    congrArg _ hw
  linarith

/-- On a Cartan cell, the two-sided upper bound of Lemma II.1.1 (for all `g₁, g₂` with a
constant depending on them) gives a bound by the value at the uniformizer power with one
constant: `K₀` is covered by finitely many translates of `K`, and `Ξ` is bi-`K`-invariant. -/
theorem exists_rationalXi_le_of_mem_rationalCartanCell {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G))) (F0 : Finset (centralizerPoints i))
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {P : rationalPoints G → Prop} {Φ : ∀ a, P a → ℝ} (hΦ : ∀ a ha, 0 ≤ Φ a ha)
    (hd : ∀ g₁ g₂ : rationalPoints G, ∃ C : ℝ, ∀ a (ha : P a),
      rationalXi hKc hPK (g₁ * a * g₂) ≤ C * Φ a ha) :
    ∃ M : ℝ, ∀ (y : cocharacterLattice S)
      (hy : P (Aubert.General.uniformizerPowers i (.ofAdd y))),
      ∀ g ∈ rationalCartanCell i K0 F0 y,
        rationalXi hKc hPK g ≤ M * Φ _ hy := by
  obtain ⟨t, ht⟩ := exists_finset_mul_mem_of_isCompact hKo hK0c
  choose Cf hCf using hd
  obtain ⟨M, hM⟩ := ((t ×ˢ (F0 ×ˢ t)).image fun p : rationalPoints G ×
    (centralizerPoints i × rationalPoints G) =>
      Cf p.1 ((p.2.1 : rationalPoints G) * p.2.2⁻¹)).exists_le
  refine ⟨M, fun y hy g hg => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, rfl⟩ := hg
  obtain ⟨c₁, hc₁, hc₁'⟩ := ht k₁⁻¹ (K0.inv_mem hk₁)
  obtain ⟨c₂, hc₂, hc₂'⟩ := ht k₂ hk₂
  set w := Aubert.General.uniformizerPowers i (.ofAdd y)
  have hrw : k₁ * w * (f : rationalPoints G) * k₂ =
      (c₁ * k₁⁻¹)⁻¹ * (c₁ * w * ((f : rationalPoints G) * c₂⁻¹)) * (c₂ * k₂) := by group
  rw [hrw, rationalXi_mul_mul hKo hKc hPK (K.inv_mem hc₁') hc₂']
  refine (hCf c₁ ((f : rationalPoints G) * c₂⁻¹) w hy).trans
    (mul_le_mul_of_nonneg_right (hM _ (Finset.mem_image.mpr ⟨(c₁, f, c₂), ?_, rfl⟩))
      (hΦ _ _))
  exact Finset.mem_product.mpr ⟨hc₁, Finset.mem_product.mpr ⟨hf, hc₂⟩⟩

end Bounds

section Volume

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

open Aubert.General Aubert.General.RationalPointFamily in
/-- **The upper bound of Waldspurger I.1 (5)** on actual rational points: for a compact open
`K₀` with Renard's simultaneous standard basis, there is `C` with
`μ(K₀ ϖ^y K₀) ≤ C δ₀(ϖ^y)⁻¹` for every dominant cocharacter `y`. A basis member `L ≤ K₀` has
`[L : L ∩ ϖ^y L ϖ^{-y}] ≤ δ₀(ϖ^y)⁻¹` (`standardBasisMember_rayIndex`), and
`μ(K₀ ϖ^y K₀) ≤ [L : L ∩ ϖ^y L ϖ^{-y}] [K₀ : L] μ(K₀)`. -/
theorem exists_measure_doubleCoset_uniformizerPowers_le (hi : IsMaximalSplitTorus i)
    {K0 : Subgroup (rationalPoints G)} (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (mu : Measure (rationalPoints G)) [mu.IsHaarMeasure] :
    ∃ C : ℝ≥0, ∀ (y : cocharacterLattice S),
      (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) →
      ∀ (hyP : uniformizerPowers i (.ofAdd y) ∈ standardParabolicPoints i ν ∅),
        mu (DoubleCoset.doubleCoset (uniformizerPowers i (.ofAdd y))
            (K0 : Set (rationalPoints G)) K0) ≤
          C * ENNReal.ofReal ((rationalMinimalModulus i ν ⟨_, hyP⟩ : ℝ≥0) : ℝ)⁻¹ := by
  have : @LocallyCompactSpace (RationalPoint F G.X) pointTopology :=
    rationalWeightsLocallyCompact
  have : @NonarchimedeanGroup (RationalPoint F G.X) _ pointTopology :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨B, hB, hBJ⟩ := hbasis
  obtain ⟨-, A, q, hcomp, hmem⟩ := hBJ (rootSet i ν ∅) (rootSet_subset i ν ∅)
  obtain ⟨L, hLB, -⟩ := hB.2.mem_iff.mp Filter.univ_mem
  obtain ⟨hLK0, -, hLo, hLc⟩ := hB.1 L hLB
  let Lop : OpenSubgroup (RationalPoint F G.X) := ⟨L, hLo⟩
  have hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν ∅) ζ :=
    ⟨ν, by rw [rootSet_empty]; exact isStandardCocharacter_empty_self i ν⟩
  have hU : IsClosed (unipotent i ν ∅ : Set (RationalPoint F G.X)) :=
    isClosed_standardUnipotentPoints i ν _
  have hrel : L.relIndex K0 ≠ 0 := relIndex_ne_zero_of_open_compact L hLo K0 hK0c
  have hK0fin : mu K0 ≠ ⊤ := hK0c.measure_lt_top.ne
  refine ⟨(L.relIndex K0 : ℝ≥0) * (mu K0).toNNReal, fun y hdom hyP => ?_⟩
  set w := uniformizerPowers i (.ofAdd y)
  let z : Subgroup.center (levi i ν ∅) := ⟨⟨w, uniformizerPowers_mem_levi i ν ∅ y⟩,
    Subgroup.mem_center_iff.mpr fun m => Subtype.ext
      (commute_uniformizerPowers i ν hfinite ∅ hexists y (by simp) m m.property)⟩
  have hray := standardBasisMember_rayIndex i ν hi hfinite ∅ hexists hU q hcomp Lop hLc
    (hmem L hLB) y (by simp) (fun β _ => hdom β) z rfl
  have hδ : HaarModulus.closedRestrictCharacter (unipotent i ν ∅) hU (levi i ν ∅)
      (levi_le_normalizer i ν ∅) (z : levi i ν ∅) = rationalMinimalModulus i ν ⟨w, hyP⟩ :=
    Jacquet.closedRestrictCharacter_congr
      (congrArg (standardUnipotentPoints i ν) (rootSet_empty i ν)) hU
      (isClosed_standardUnipotentPoints i ν ∅) (levi_le_normalizer i ν ∅)
      (standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅) rfl
  rw [hδ] at hray
  have hmeas := (measure_doubleCoset_bounds mu hLK0 hLo.measurableSet hK0o.measurableSet w
    hray.1 hrel).2
  refine hmeas.trans ?_
  have hidx : (doubleCosetIndex L w : ℝ≥0∞) ≤
      ENNReal.ofReal ((rationalMinimalModulus i ν ⟨w, hyP⟩ : ℝ≥0) : ℝ)⁻¹ := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hray.2
  calc (doubleCosetIndex L w : ℝ≥0∞) * (L.relIndex K0 : ℝ≥0∞) * mu K0
      = ((L.relIndex K0 : ℝ≥0) * (mu K0).toNNReal : ℝ≥0) * (doubleCosetIndex L w : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hK0fin, ENNReal.coe_natCast]; ring
    _ ≤ _ := by gcongr

end Volume

section Norm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

open CocharacterUniformizer in
/-- For a closed subgroup `i : S → G` and a closed matrix representation `ρ`, every character
`α` of `S` satisfies `|⟨α, y⟩| ≤ C (1 + σ(ϖ^y))` for all cocharacters `y`: the norm of
`α(ϖ^y)` is `q^{-⟨α, y⟩}`, and the logarithm of the norm of a rational character is bounded
by a multiple of `1 + σ`. -/
theorem exists_abs_latticePairing_le (i : S.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ) (α : characterLattice S) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : cocharacterLattice S,
      |(latticePairing S α y : ℝ)| ≤
        C * (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom i.hom.hom.left
  obtain ⟨C, hC, hb⟩ :=
    MatrixRepresentation.rationalNormCharacters_abs_log_rationalMatrixNorm_bound F
      (ρ.restrict i) (hi.comp hρ) ((rationalCharacters.equivCharacterLattice S).symm α)
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hlog : 0 < Real.log (LocalField.residueCardinality F : ℝ) := Real.log_pos hq
  refine ⟨C / Real.log (LocalField.residueCardinality F : ℝ), div_pos hC hlog, fun y => ?_⟩
  have h := hb (latticeSection F S (.ofAdd y))
  have he : (((Plancherel.rationalNormCharacters S.toGrp
      ((rationalCharacters.equivCharacterLattice S).symm α)).toMul
        (latticeSection F S (.ofAdd y)) : ℝ≥0) : ℝ) =
      (LocalField.residueCardinality F : ℝ) ^ (-latticePairing S α y) :=
    characterNorm_latticeSection F S α y
  rw [he, Real.log_zpow, Plancherel.rationalMatrixNorm_restrict, abs_mul,
    abs_of_pos hlog, Int.cast_neg, abs_neg] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
  exact h

/-- **The lower bound of Waldspurger I.1 (6)** in coordinates: for a closed split subtorus
`i : S → G` and a closed matrix representation `ρ`, there are a finite type `I`, an injective
map `H` from the cocharacters of `S` into the standard lattice `ℤ^I ⊆ ℝ^I` (coordinates of
`X_*(S) ≅ ℤ^I`) and `C > 0` with `1 + ‖H(y)‖ ≤ C (1 + σ(ϖ^y))`. Each coordinate is the pairing
with a character of `S` (the pairing `X^*(S) × X_*(S) → ℤ` is perfect), so it is bounded by
`exists_abs_latticePairing_le`. -/
theorem exists_cocharacterCoordinates_norm_le (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)
    (hi : IsClosedSubgroup i) (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ) :
    ∃ (I : Type u) (_ : Fintype I)
      (H : cocharacterLattice S → Submodule.span ℤ (Set.range (Pi.basisFun ℝ I))) (C : ℝ),
      Function.Injective H ∧ 0 < C ∧ ∀ y : cocharacterLattice S,
        1 + ‖H y‖ ≤
          C * (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS.exists_cocharacterCoordinates
  let : Fintype I := Fintype.ofFinite I
  have := CocharacterUniformizer.latticePairing_isPerfPair F S hS
  have hα : ∀ k : I, ∃ α : characterLattice S, ∀ y, latticePairing S α y = e y k := fun k => by
    obtain ⟨α, hα⟩ := (LinearMap.IsPerfPair.bijective_left (latticePairing S)).2
      ((LinearMap.proj k).comp e.toLinearMap)
    exact ⟨α, fun y => LinearMap.congr_fun hα y⟩
  choose α hα using hα
  choose C hC hb using fun k => exists_abs_latticePairing_le i hi ρ hρ (α k)
  let H : cocharacterLattice S → Submodule.span ℤ (Set.range (Pi.basisFun ℝ I)) := fun y =>
    ⟨fun k => (e y k : ℝ), ((Pi.basisFun ℝ I).mem_span_iff_repr_mem ℤ _).mpr
      fun k => ⟨e y k, by simp⟩⟩
  have hCs : 0 ≤ ∑ k, C k := Finset.sum_nonneg fun k _ => (hC k).le
  refine ⟨I, inferInstance, H, 1 + ∑ k, C k, ?_, by linarith, fun y => ?_⟩
  · intro y y' h
    apply e.injective
    funext k
    have : (e y k : ℝ) = e y' k := congrFun (congrArg Subtype.val h) k
    exact_mod_cast this
  · set σ := rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))
    have hσ : 0 ≤ σ := rationalHeight_nonneg ρ _
    have hnorm : ‖H y‖ ≤ (∑ k, C k) * (1 + σ) := by
      change ‖(fun k => (e y k : ℝ))‖ ≤ _
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
      rw [Real.norm_eq_abs, ← hα k y]
      exact (hb k y).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => (hC k).le) (Finset.mem_univ k)) (by linarith))
    nlinarith

end Norm

section Main

open Aubert.General Aubert.General.RationalPointFamily

/-- **Waldspurger, Lemme II.1.5** (printed p. 252) on actual rational points, derived from the
upper bound of Lemma II.1.1 (`RationalXiUpperBoundStatement`). The cells are the Cartan cells
`⋃_{f ∈ F₀} K₀ ϖ^y f K₀` of the dominant cocharacters `y` (Renard's covering clause), and the
inputs of `CartanSquareBound` are: the volume bound of I.1 (5)
(`exists_measure_cell_le_doubleCoset`, `exists_measure_doubleCoset_uniformizerPowers_le`), the
upper bound of II.1.1 transported to the cells (`exists_rationalXi_le_of_mem_rationalCartanCell`,
`exists_rationalHeight_uniformizerPowers_le`) and the lower bound of I.1 (6)
(`exists_cocharacterCoordinates_norm_le`). -/
theorem rationalXiSquareIntegrable_of_upperBound (h : RationalXiUpperBoundStatement.{u}) :
    RationalXiSquareIntegrableStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K0 hK0o hK0c hbasis hcover K hKo hKc hPK N _ ρ hρ mu _
  obtain ⟨F0, hF0⟩ := hcover
  have hbasis' := hbasis
  obtain ⟨Bs, -, hBJ⟩ := hbasis'
  obtain ⟨-, A, q, hA, -⟩ := hBJ ∅ (Set.empty_subset _)
  have hexists : ∃ ζ, IsStandardCocharacter i ν ∅ ζ := ⟨ν, isStandardCocharacter_empty_self i ν⟩
  let Idx := {y : cocharacterLattice S // ∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y}
  have hCA (y : Idx) : uniformizerPowers i (.ofAdd y.1) ∈ standardComponentCAplus i ν ∅ q :=
    (uniformizerPowers_mem_standardComponentChambers hi hexists hA y.1 (by simp)
      fun β hβ => by simpa using y.2 ⟨β, hβ⟩).2
  have hP (y : Idx) : uniformizerPowers i (.ofAdd y.1) ∈ standardParabolicPoints i ν ∅ :=
    mem_standardParabolicPoints_of_mem_standardComponentCAplus hA (hCA y)
  let δ : Idx → ℝ := fun y => ((rationalMinimalModulus i ν ⟨_, hP y⟩ : ℝ≥0) : ℝ)
  let cell : Idx → Set (rationalPoints G) := fun y => rationalCartanCell i K0 F0 y.1
  obtain ⟨B, hB⟩ := exists_rationalHeight_uniformizerPowers_le ρ hK0c F0
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hσ (y : Idx) (g : rationalPoints G) (hg : g ∈ cell y) :
      1 + rationalHeight (F := F) ρ (uniformizerPowers i (.ofAdd y.1)) ≤
        (1 + B') * (1 + rationalHeight (F := F) ρ g) := by
    have h1 := hB y.1 g hg
    have h2 := rationalHeight_nonneg (F := F) ρ g
    have h3 : B ≤ B' := le_max_left _ _
    nlinarith
  obtain ⟨I, _, H, CH, hHinj, hCH, hHb⟩ :=
    exists_cocharacterCoordinates_norm_le i hi.isSplitSubtorus.1 hi.isSplitSubtorus.2 ρ hρ
  obtain ⟨I', hI', ⟨e⟩⟩ := hi.isSplitSubtorus.1.exists_cocharacterCoordinates
  have : Countable (cocharacterLattice S) := e.injective.countable
  obtain ⟨d, hd⟩ := h F G hG S i hi ν hν K0 hbasis A q hA K hKo hKc hPK N ρ hρ
  obtain ⟨M, hM⟩ := exists_rationalXi_le_of_mem_rationalCartanCell hK0c F0 hKo hKc hPK
    (P := fun a => a ∈ standardParabolicPoints i ν ∅ ∧ a ∈ standardComponentCAplus i ν ∅ q)
    (Φ := fun a ha => (NNReal.sqrt (rationalMinimalModulus i ν ⟨a, ha.1⟩ : ℝ≥0) : ℝ) *
      (1 + rationalHeight (F := F) ρ a) ^ d)
    (fun a _ => mul_nonneg (NNReal.coe_nonneg _)
      (pow_nonneg (by linarith [rationalHeight_nonneg (F := F) ρ a]) _))
    (fun g₁ g₂ => by
      obtain ⟨C, hC⟩ := hd g₁ g₂
      exact ⟨C, fun a ha => by rw [← mul_assoc]; exact hC a ha.1 ha.2⟩)
  obtain ⟨Nc, hNc⟩ := exists_measure_cell_le_doubleCoset mu hK0o hK0c F0
    (fun f : centralizerPoints i => (f : rationalPoints G))
  obtain ⟨Cv, hCv⟩ := exists_measure_doubleCoset_uniformizerPowers_le hi hK0o hK0c hbasis mu
  refine CartanSquareBound.squareIntegrableWeight (cell := cell) (δ := δ)
    (H := fun y => H y.1) ⟨inferInstance, ?_, fun g => rationalHeight_nonneg ρ g, fun y => ?_,
      ⟨Nc * Cv, fun y => ?_⟩, ⟨max M 0 * (1 + B') ^ d, d, fun y g hg => ?_⟩,
      ⟨CH * (1 + B'), mul_pos hCH (by linarith), fun y g hg => ?_⟩,
      hHinj.comp Subtype.val_injective⟩
  · refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨y, hy, hg⟩ := exists_mem_rationalCartanCell hF0 g
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hg⟩
  · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  · have hw : ∀ f ∈ F0, (f : rationalPoints G) * uniformizerPowers i (.ofAdd y.1) =
        uniformizerPowers i (.ofAdd y.1) * (f : rationalPoints G) := fun f _ =>
      (centralizerPoints_le_pointCentralizer i f.property _
        ((mem_torusPoints i _).mpr ⟨CocharacterUniformizer.latticeSection F S (.ofAdd y.1),
          rfl⟩)).symm
    calc mu (cell y)
        ≤ Nc * mu (DoubleCoset.doubleCoset (uniformizerPowers i (.ofAdd y.1))
            (K0 : Set (rationalPoints G)) K0) := hNc _ hw
      _ ≤ Nc * (Cv * ENNReal.ofReal (δ y)⁻¹) := by
        gcongr
        exact hCv y.1 y.2 (hP y)
      _ = ((Nc * Cv : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (δ y)⁻¹ := by push_cast; ring
  · have hxi := hM y.1 ⟨hP y, hCA y⟩ g hg
    have hs : (NNReal.sqrt (rationalMinimalModulus i ν ⟨_, hP y⟩ : ℝ≥0) : ℝ) =
        Real.sqrt (δ y) := Real.coe_sqrt
    rw [hs] at hxi
    have hw0 : 0 ≤ rationalHeight (F := F) ρ (uniformizerPowers i (.ofAdd y.1)) :=
      rationalHeight_nonneg ρ _
    have ht := pow_le_pow_left₀ (by linarith) (hσ y g hg) d
    have hs0 : 0 ≤ Real.sqrt (δ y) := Real.sqrt_nonneg _
    have ht0 : 0 ≤ (1 + rationalHeight (F := F) ρ (uniformizerPowers i (.ofAdd y.1))) ^ d :=
      pow_nonneg (by linarith) _
    have hM0 : 0 ≤ max M 0 := le_max_right _ _
    rw [abs_of_pos (rationalXi_pos hKo hKc hPK g), Real.rpow_natCast]
    calc rationalXi hKc hPK g
        ≤ M * (Real.sqrt (δ y) *
          (1 + rationalHeight (F := F) ρ (uniformizerPowers i (.ofAdd y.1))) ^ d) := hxi
      _ ≤ max M 0 * (Real.sqrt (δ y) *
          (1 + rationalHeight (F := F) ρ (uniformizerPowers i (.ofAdd y.1))) ^ d) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hs0 ht0)
      _ ≤ max M 0 * (Real.sqrt (δ y) * ((1 + B') * (1 + rationalHeight (F := F) ρ g)) ^ d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hs0) hM0
      _ = max M 0 * (1 + B') ^ d * Real.sqrt (δ y) * (1 + rationalHeight (F := F) ρ g) ^ d := by
        rw [mul_pow]; ring
  · calc 1 + ‖H y.1‖
        ≤ CH * (1 + rationalHeight (F := F) ρ (uniformizerPowers i (.ofAdd y.1))) := hHb y.1
      _ ≤ CH * ((1 + B') * (1 + rationalHeight (F := F) ρ g)) :=
        mul_le_mul_of_nonneg_left (hσ y g hg) hCH.le
      _ = CH * (1 + B') * (1 + rationalHeight (F := F) ρ g) := by ring

end Main

end Langlands.HarishChandraSchwartz
