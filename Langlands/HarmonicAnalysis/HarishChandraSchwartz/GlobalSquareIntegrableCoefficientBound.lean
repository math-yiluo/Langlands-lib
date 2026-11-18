import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupSquareIntegrabilityTransfer

/-! # Global coefficient Xi bounds from square integrability -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal BigOperators
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalDecaySecondCountable
  rationalDecayT2 rationalDecayNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

include hKo in
/-- Every coefficient of a representation square integrable modulo the actual
split component is globally bounded by Xi. The finite Cartan cover and basis
are retained, but no valuation index or matrix-height hypothesis is used. -/
theorem hasXiBoundedCoefficients_of_splitComponentSquareIntegrable
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
        HasXiBoundedCoefficients (rationalXi hKc hPK) A.representation := by
  intro mu hmu A hsq v φ
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype (SimpleRoot i ν) := hfinite.fintype
  have hfull : levi i ν Finset.univ = ⊤ := levi_univ_eq_top i ν standardCocharacter hG hi hν
  have hexists (I : Finset (SimpleRoot i ν)) :
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ :=
    (standardCocharacter F G hG S i hi ν hν _ (rootSet_subset i ν I)).1
  have hstd (I : Finset (SimpleRoot i ν)) : ∃ ζ : cocharacterLattice S,
      (∀ β ∈ I, simpleRootPairing i ν β ζ = 0) ∧
        ∀ β ∉ I, 0 < simpleRootPairing i ν β ζ := by
    obtain ⟨ζ, hζ⟩ := hexists I
    exact ⟨ζ, fun β hβ => hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ),
      fun β hβ => hζ.2.2 β.1 β.2 fun h' => hβ ((val_mem_rootSet i ν I β).mp h')⟩
  have hcentral (x : cocharacterLattice S) (hx : ∀ α, simpleRootPairing i ν α x = 0) :
      uniformizerPowers i (.ofAdd x) ∈ Subgroup.center (rationalPoints G) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact commute_uniformizerPowers i ν hfinite Finset.univ (hexists _) x
      (fun β _ => hx β) g (by rw [hfull]; exact Subgroup.mem_top _)
  -- the chamber lattice: one generator per simple root, up to a finite set and the centre
  obtain ⟨gen, hgenpos, hgenzero, hgenR⟩ := finiteChamberLattice (SimpleRoot i ν)
    (cocharacterLattice S) (simpleRootPairing i ν) hstd
  obtain ⟨R, hRfin, hR⟩ := hgenR 0
  obtain ⟨F0, hF0⟩ := hcover
  let F₁ : Set (rationalPoints G) :=
    (fun p : cocharacterLattice S × centralizerPoints i =>
      uniformizerPowers i (.ofAdd p.1) * (p.2 : rationalPoints G)) ''
        (R ×ˢ (F0 : Set (centralizerPoints i)))
  have hF₁ : F₁.Finite := (hRfin.prod F0.finite_toSet).image _
  -- geometric decay of the coefficient on compact translates of the chamber lattice
  obtain ⟨q, C, hq0, hq1, hgeo⟩ := exists_geometric_coefficient_bound hKo hKc hPK hG hi hν
    hK0c hbasis gen hgenpos hgenzero hF₁ hs mu hmu A hsq φ v
  obtain ⟨-, c, -⟩ := hsq
  refine ⟨1 + max C 0, by positivity, fun g => ?_⟩
  obtain ⟨y, hy0, hy⟩ := exists_mem_rationalCartanCell hF0 g
  obtain ⟨r, hr, n, z, hz, hyeq⟩ := hR y (fun α => by rw [neg_zero]; exact hy0 α)
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, hgeq⟩ := id hy
  have hzc := hcentral z hz
  have hyw : uniformizerPowers i (.ofAdd y) = uniformizerPowers i (.ofAdd z) *
      (uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) * uniformizerPowers i (.ofAdd r)) := by
    rw [← map_mul, ← map_mul, ← ofAdd_add, ← ofAdd_add, hyeq]
    congr 2
    abel
  set Z := uniformizerPowers i (.ofAdd z) with hZ
  set W := uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) with hW
  set Pr := uniformizerPowers i (.ofAdd r) with hPr
  have hgeq' : g = Z * (k₁ * W * (Pr * (f : rationalPoints G)) * k₂) := by
    have hcomm : k₁ * Z = Z * k₁ := Subgroup.mem_center_iff.mp hzc k₁
    rw [hgeq, hyw]
    calc k₁ * (Z * (W * Pr)) * (f : rationalPoints G) * k₂ =
        (k₁ * Z) * W * (Pr * (f : rationalPoints G)) * k₂ := by simp only [mul_assoc]
      _ = Z * (k₁ * W * (Pr * (f : rationalPoints G)) * k₂) := by
        rw [hcomm]
        simp only [mul_assoc]
  set g' := k₁ * W * (Pr * (f : rationalPoints G)) * k₂ with hg'
  have hcoef : ‖φ.val (A.representation g v)‖ = ‖φ.val (A.representation g' v)‖ := by
    rw [hgeq', map_mul, Module.End.mul_apply]
    have hact : A.representation Z (A.representation g' v) =
        (c.character ⟨Z, hzc⟩ : ℂ) • A.representation g' v := c.acts ⟨Z, hzc⟩ _
    rw [hact, map_smul, norm_smul, c.norm_eq_one, one_mul]
  have hXi : rationalXi hKc hPK g = rationalXi hKc hPK g' := by
    rw [hgeq']
    exact rationalXi_mul_of_mem_center hKo hKc hPK
      (uniformizerPowers_mem_standardParabolicPoints i ν z) hzc _
  have hgb := hgeo n k₁ hk₁ (Pr * (f : rationalPoints G))
    ⟨(r, f), Set.mk_mem_prod hr (Finset.mem_coe.mpr hf), rfl⟩ k₂ hk₂
  have hΞ0 := rationalXi_nonneg hKc hPK g'
  have hqpow0 : 0 ≤ q ^ (∑ a, n a) := pow_nonneg hq0.le _
  have hqpow1 : q ^ (∑ a, n a) ≤ 1 := pow_le_one₀ hq0.le hq1.le
  rw [hcoef, hXi]
  calc ‖φ.val (A.representation g' v)‖ ≤ C * rationalXi hKc hPK g' * q ^ (∑ a, n a) := hgb
    _ ≤ max C 0 * rationalXi hKc hPK g' * q ^ (∑ a, n a) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hΞ0) hqpow0
    _ ≤ max C 0 * rationalXi hKc hPK g' :=
      mul_le_of_le_one_right (mul_nonneg (le_max_right _ _) hΞ0) hqpow1
    _ ≤ (1 + max C 0) * rationalXi hKc hPK g' :=
      mul_le_mul_of_nonneg_right (by linarith) hΞ0

include hKo in
/-- The global Xi coefficient estimate for an irreducible representation square
integrable modulo any Borel-compatible central subgroup, without an index
premise. The supplied split component is only used in the internal transfer. -/
theorem hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s)
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
    (C : Subgroup (rationalPoints G)) [C.Normal] (hC : C ≤ Subgroup.center (rationalPoints G))
    [MeasurableSpace (rationalPoints G ⧸ C)] [BorelSpace (rationalPoints G ⧸ C)]
    (muC : Measure (rationalPoints G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muC) :
    HasXiBoundedCoefficients (rationalXi hKc hPK) π.obj.representation := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  let : BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := ⟨rfl⟩
  let muA : Measure (rationalPoints G ⧸ (rationalPoints.map s).range) := Measure.haar
  have hsqA := isSquareIntegrable_splitComponent_of_centralSubgroup hG s hs π C hC muC hsq muA
  exact hasXiBoundedCoefficients_of_splitComponentSquareIntegrable hKo hKc hPK hG hi hν
    hK0c hbasis hcover hs muA π.obj hsqA

/-- A positive global coefficient-Xi constant selected from the proved
arbitrary-central-subgroup estimate, retaining the original coefficient. -/
def centralSubgroupXiCoefficientConstant
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s)
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
    (C : Subgroup (rationalPoints G)) [C.Normal] (hC : C ≤ Subgroup.center (rationalPoints G))
    [MeasurableSpace (rationalPoints G ⧸ C)] [BorelSpace (rationalPoints G ⧸ C)]
    (muC : Measure (rationalPoints G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muC)
    (v : π.obj) (ℓ : SmoothDual π.obj.representation) : ℝ :=
  Classical.choose (hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable
    hKo hKc hPK hG hi hν hK0c hbasis hcover hs π C hC muC hsq v ℓ)

/-- The selected constant is positive and bounds the same original coefficient
at every actual rational point. -/
theorem centralSubgroupXiCoefficientConstant_spec
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s)
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
    (C : Subgroup (rationalPoints G)) [C.Normal] (hC : C ≤ Subgroup.center (rationalPoints G))
    [MeasurableSpace (rationalPoints G ⧸ C)] [BorelSpace (rationalPoints G ⧸ C)]
    (muC : Measure (rationalPoints G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muC)
    (v : π.obj) (ℓ : SmoothDual π.obj.representation) :
    0 < centralSubgroupXiCoefficientConstant hKo hKc hPK hG hi hν hK0c hbasis hcover hs
      π C hC muC hsq v ℓ ∧
    ∀ g, ‖ℓ.val (π.obj.representation g v)‖ ≤
      centralSubgroupXiCoefficientConstant hKo hKc hPK hG hi hν hK0c hbasis hcover hs
        π C hC muC hsq v ℓ * rationalXi hKc hPK g :=
  Classical.choose_spec (hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable
    hKo hKc hPK hG hi hν hK0c hbasis hcover hs π C hC muC hsq v ℓ)

end Langlands.HarishChandraSchwartz
