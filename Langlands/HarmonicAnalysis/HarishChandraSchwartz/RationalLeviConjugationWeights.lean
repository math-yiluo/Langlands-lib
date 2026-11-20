import Langlands.BruhatTits.SpecialCompact.StandardLeviSimultaneousBasisTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompactHeightEnvelope
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInvariantHeightWeights
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiFullChamber

/-! # Xi averaging and chamber weights on an actual standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

include hKo hKc in
/-- The published compact envelope supplies the invariant height hypotheses
for Xi averaging. -/
theorem rationalCompactHeight_isConvolutionHeightMajorant :
    IsConvolutionHeightMajorant K (rationalHeight (F := F) ρ) (rationalCompactHeight ρ K) := by
  let L : OpenSubgroup (rationalPoints G) := ⟨K, hKo⟩
  obtain ⟨_, _, hbound⟩ := rationalCompactHeight_bounds ρ K hKc
  refine ⟨rationalCompactHeight_nonneg ρ K hKc,
    (isLocallyConstant_rationalCompactHeight ρ L).continuous,
    rationalCompactHeight_mul_le ρ K hKc, ?_, fun g => (hbound g).1⟩
  intro k hk g
  simpa only [Subgroup.coe_one, mul_one] using rationalCompactHeight_mul_mul ρ K ⟨k, hk⟩ 1 g

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)

local notation "M" => standardLeviPoints i ν J
local notation "P₀M" => Subgroup.subgroupOf (standardParabolicPoints i ν ∅) M
local notation "KM" => Subgroup.subgroupOf K M

variable (hM : IsIwasawaPair
  ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
  (K.subgroupOf (standardLeviPoints i ν J)))

local notation "ΞM" => rationalLeviXi (i := i) (ν := ν) (J := J) (K := K) hKc hM

/-- The actual intrinsic minimal Iwasawa half-weight on `M_J(F)`. -/
def rationalLeviConjugationHalfWeight (m : standardLeviPoints i ν J) : ℝ :=
  iwasawaWeight hM (standardLeviMinimalModulusOf i ν J) m

include hKo hKc hG hi hν hJ in
/-- On the Levi minimal parabolic the squared intrinsic half-weight times
`δ_U` is the ambient minimal modulus. -/
theorem rationalLeviConjugationHalfWeight_sq_mul_modulus (a : P₀M) :
    rationalLeviConjugationHalfWeight hM a ^ 2 *
        ((standardUnipotentModulus i ν J (a : M) : ℝ≥0) : ℝ) =
      ((rationalMinimalModulus i ν
        ⟨((a : M) : rationalPoints G), Subgroup.mem_subgroupOf.mp a.2⟩ : ℝ≥0) : ℝ) := by
  have hsqrt : rationalLeviConjugationHalfWeight hM a =
      (NNReal.sqrt (standardLeviMinimalModulusOf i ν J a : ℝ≥0) : ℝ) := by
    simpa only [rationalLeviConjugationHalfWeight, mul_one] using
      iwasawaWeight_mul (hPK := hM)
        (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p
          (Subgroup.mem_subgroupOf.mp hp))
        a.2 (Subgroup.one_mem KM)
  have hsq : rationalLeviConjugationHalfWeight hM a ^ 2 =
      (standardLeviMinimalModulusOf i ν J a : ℝ≥0) := by
    rw [hsqrt]
    exact_mod_cast NNReal.sq_sqrt (standardLeviMinimalModulusOf i ν J a : ℝ≥0)
  let p : (standardParabolicPoints i ν ∅ ⊓ M : Subgroup (rationalPoints G)) :=
    ⟨(a : M).val, Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp a.2, (a : M).2⟩⟩
  have heq := congrArg (fun d : ℝ≥0ˣ => ((d : ℝ≥0) : ℝ))
    (rationalMinimalModulus_eq_mul hG hi hν hJ p)
  rw [hsq, standardLeviMinimalModulusOf_apply]
  simpa only [Units.val_mul, NNReal.coe_mul, p] using heq.symm

section Averaging

include hKo hG hi hν hJ in
/-- The local Levi Xi-square estimate gives actual convolution weights on the
Levi subgroup with the restriction of the ambient compact envelope. -/
theorem rationalLeviConvolutionWeights_of_squareIntegrableWeight
    {muM : Measure M}
    (hsq : SquareIntegrableWeight muM ΞM
      (fun m : M => rationalHeight (F := F) ρ m)) :
    haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
    ConvolutionWeights muM KM ΞM (fun m : M => rationalCompactHeight ρ K m) := by
  letI : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  letI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  have hδ (p : P₀M) (hp : (p : M) ∈ KM) :=
    standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p (Subgroup.mem_subgroupOf.mp hp)
  have hKMo : IsOpen (KM : Set M) := hKo.preimage continuous_subtype_val
  have hσ := rationalCompactHeight_isConvolutionHeightMajorant hKo hKc ρ
  exact {
    pos := rationalLeviXi_pos hKo hKc hG hi hν hJ hM
    nonneg := fun m => hσ.1 m
    continuous_xi := continuous_xi (hPK := hM) hδ hKMo
    continuous_sigma := hσ.2.1.comp continuous_subtype_val
    one_add_le := one_add_le_of_le_add (fun m : M => hσ.1 m)
      (fun g h : M => hσ.2.2.1 g h)
    xi_mul_left := fun _ hk m => xi_mul_left (hPK := hM)
      (δ := standardLeviMinimalModulusOf i ν J) hk m
    sigma_mul_left := fun k hk m => hσ.2.2.2.1 k (Subgroup.mem_subgroupOf.mp hk) m
    xi_inv := rationalLeviXi_inv hG hi hν hJ hKo hKc hM
    integral_xi := integral_xi_mul_mul (hPK := hM) hδ hKMo
    square := hsq.mono_height (fun m => rationalHeight_nonneg ρ m)
      (fun m => hσ.2.2.2.2 m) }

include hKo hG hi hν hJ in
/-- The inherited basis and Cartan covering give the local Levi Xi-square
input to averaging from the lattice Xi upper statement. -/
theorem rationalLeviConvolutionWeights_of_upperBound (hupper : RationalXiUpperBoundStatement.{u})
    (hρ : IsClosedSubgroup ρ)
    {K0 : Subgroup (rationalPoints G)} (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G))) (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : StandardLeviCartanCovering F i ν J K0)
    (muM : Measure M) [muM.IsHaarMeasure] :
    haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
    ConvolutionWeights muM KM ΞM (fun m : M => rationalCompactHeight ρ K m) :=
  rationalLeviConvolutionWeights_of_squareIntegrableWeight hKo hKc ρ hG hi hν hJ hM
    (rationalLeviSquareIntegrableWeight_of_upperBound (i := i) (ν := ν) (J := J)
      hG hi hν hJ hKo hKc ρ hρ hM
      (isOpen_leviSchemeCompact hK0o) (isCompact_leviSchemeCompact hK0c)
      (hbasis.leviScheme i ν J hG hi hν hJ)
      (finiteCartanCovering_leviScheme i ν J hG hi hν hJ hcover) muM hupper)

end Averaging

include hKo hG hi hν hJ in
/-- For the same compact choice, the Levi Xi upper bound applies to every
point of the full ambient chamber, with height restricted from `G(F)`. -/
theorem rationalLeviXiUpperBound_on_ambientChamber (hupper : RationalXiUpperBoundStatement.{u})
    (hρ : IsClosedSubgroup ρ)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0) :
    XiUpperBound ΞM (fun m : M => rationalHeight (F := F) ρ m)
      (Subtype.val ⁻¹' rationalMinimalChamber i ν) (rationalLeviConjugationHalfWeight hM) := by
  have := leviScheme_isAffineHom i ν J
  have := leviScheme_locallyOfFiniteType i ν J
  let e := leviSchemePointsEquiv i ν J
  let iL := Standard.leviTorusHom i ν J
  let hML := isIwasawaPair_leviSchemeCompact hG hi hν hJ hM
  have hL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := isGenericCocharacter_leviTorusHom (J := J) hν
  obtain ⟨C, D, hup⟩ := hupper.fullChamberXiUpperBound hL hiL hνL
    (hbasis.leviScheme i ν J hG hi hν hJ) (isOpen_leviSchemeCompact hKo)
    (isCompact_leviSchemeCompact hKc) hML (isClosedSubgroup_restrict_leviHom ρ hρ)
  refine ⟨C, D, fun m hm => ?_⟩
  obtain ⟨a, ha, horder⟩ := (mem_rationalMinimalChamber_iff_order i ν (m : rationalPoints G)).mp hm
  let x := e.symm m
  have hx : e x = m := e.apply_symm_apply m
  have hxg : rationalPoints.map (Standard.leviHom i ν J) x = m.val :=
    map_leviSchemePointsEquiv_symm i ν J m
  have hxa : x = rationalPoints.map iL a := by
    apply map_leviHom_injective
    rw [hxg]
    rw [← Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply,
      Standard.leviTorusHom_comp]
    exact ha.symm
  have hxch : x ∈ rationalMinimalChamber iL ν := by
    refine (mem_rationalMinimalChamber_iff_order iL ν x).mpr ⟨a, hxa.symm, ?_⟩
    intro α hα
    change α ∈ simpleRelativeRoots (Standard.leviTorusHom i ν J) ν at hα
    rw [simpleRelativeRoots_leviScheme i ν J hG hi hν hJ] at hα
    exact horder α (hJ hα)
  have hw := iwasawaWeight_map e (hPK := hML) (hPK' := hM)
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p
      (Subgroup.mem_subgroupOf.mp hp))
    (fun p hp => (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ p).1 hp)
    (fun k hk => (mem_leviSchemeCompact_iff k).mp hk)
    (fun p => standardLeviMinimalModulus_leviHom hG hi hν hJ p) x
  have hb := hup x hxch
  rw [rationalXi_leviScheme hG hi hν hJ hKo hKc hM,
    rationalHeight_restrict_leviHom, ← hw, hx, hxg] at hb
  exact hb

end Langlands.HarishChandraSchwartz
