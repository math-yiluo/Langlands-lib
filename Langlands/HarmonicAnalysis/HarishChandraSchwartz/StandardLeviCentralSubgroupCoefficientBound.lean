import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GlobalSquareIntegrableCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviTempered
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness

/-! # Global Xi coefficients for arbitrary central quotients of a standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))

set_option hygiene false in
local notation "rootsI" => RationalPointFamily.rootSet i ν I
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν rootsI
set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν rootsI
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν rootsI

local instance standardLeviCentralXiBoundAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν rootsI
local instance standardLeviCentralXiBoundAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviCentralXiBoundFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν rootsI
local instance standardLeviCentralXiBoundTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviCentralXiBoundNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
  rationalPoints_nonarchimedeanGroup 𝐋

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf 𝐌)
    ((K : Subgroup (rationalPoints G)).subgroupOf 𝐌))
  {K0L : Subgroup (rationalPoints 𝐋)}
  (hK0Lc : IsCompact (K0L : Set (rationalPoints 𝐋)))
  (hbasis : Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt iL ν K0L)
  (hcover : RationalPointFamily.FiniteCartanCovering F iL ν K0L)

include hG hi hν hsq hK0Lc hbasis hcover in
/-- Global Xi control on the literal standard Levi from square integrability
modulo any Borel-compatible central subgroup. No split-component, valuation
index or matrix representation is an extra input. -/
theorem hasXiBoundedCoefficients_standardLeviCentralSubgroupSquareIntegrable :
    HasXiBoundedCoefficients (rationalLeviXi hKc hMK) π.obj.representation := by
  let e := leviSchemePointsEquiv i ν rootsI
  let CL : Subgroup (rationalPoints 𝐋) := C.comap e.toMonoidHom
  have hCL : CL ≤ Subgroup.center (rationalPoints 𝐋) :=
    (Subgroup.comap_mono hC).trans (Subgroup.comap_center_le_center e.injective)
  have hCLmap : CL.map e.toMulEquiv.toMonoidHom = C :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective C
  let : MeasurableSpace (rationalPoints 𝐋 ⧸ CL) := borel _
  let : BorelSpace (rationalPoints 𝐋 ⧸ CL) := ⟨rfl⟩
  let eQ := quotientContinuousMulEquiv e C CL hCLmap
  let muL : Measure (rationalPoints 𝐋 ⧸ CL) := mu.map eQ.symm
  have : muL.IsHaarMeasure := eQ.symm.isHaarMeasure_map mu
  have hmap : muL.map eQ = mu :=
    MeasurableEquiv.map_map_symm eQ.toHomeomorph.toMeasurableEquiv
  let πL := IrreducibleAdmissibleRep.pullback e π
  have hsqL : IsSquareIntegrableModCentralSubgroup CL hCL πL.obj.representation muL :=
    (isSquareIntegrableModCentralSubgroup_comp_iff e C hC CL hCL hCLmap mu muL hmap
      π.obj.representation).mpr hsq
  obtain ⟨T, s, hs⟩ := exists_isSplitComponent_standardLevi I hG hi hν
  have hbound := hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable
    (isOpen_leviSchemeCompact (i := i) (ν := ν) (J := rootsI) K.isOpen)
    (isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootsI) hKc)
    (isIwasawaPair_leviSchemeCompact hG hi hν (RationalPointFamily.rootSet_subset i ν I) hMK)
    (isConnectedReductive_leviScheme_rootSet hG hi hν I)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν rootsI hi)
    (isGenericCocharacter_leviTorusHom hν) hK0Lc hbasis hcover hs πL CL hCL muL hsqL
  exact (hasXiBoundedCoefficients_leviSchemeRepresentation_iff hG hi hν
    (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hMK π.obj).mp hbound

/-- A positive global Xi constant for the original literal-Levi coefficient
with its original central-subgroup square-integrability data. -/
def standardLeviCentralSubgroupXiCoefficientConstant (v : π.obj)
    (ℓ : SmoothDual π.obj.representation) : ℝ :=
  Classical.choose (hasXiBoundedCoefficients_standardLeviCentralSubgroupSquareIntegrable
    hG hi hν I π C hC mu hsq hKc hMK hK0Lc hbasis hcover v ℓ)

/-- The selected constant is positive and bounds the same original coefficient
at every literal standard-Levi point. -/
theorem standardLeviCentralSubgroupXiCoefficientConstant_spec (v : π.obj)
    (ℓ : SmoothDual π.obj.representation) :
    0 < standardLeviCentralSubgroupXiCoefficientConstant hG hi hν I π C hC mu hsq
      hKc hMK hK0Lc hbasis hcover v ℓ ∧
    ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤
      standardLeviCentralSubgroupXiCoefficientConstant hG hi hν I π C hC mu hsq
        hKc hMK hK0Lc hbasis hcover v ℓ * rationalLeviXi hKc hMK m :=
  Classical.choose_spec (hasXiBoundedCoefficients_standardLeviCentralSubgroupSquareIntegrable
    hG hi hν I π C hC mu hsq hKc hMK hK0Lc hbasis hcover v ℓ)

end Langlands.HarishChandraSchwartz
