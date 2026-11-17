import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralFiniteIndexCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviTempered
import Langlands.Representation.Plancherel.StandardLeviCharacterMeasure

/-! # Actual standard-Levi square-integrable coefficient Xi bounds -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
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

local instance standardLeviXiBoundAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν rootsI
local instance standardLeviXiBoundAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviXiBoundFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν rootsI
local instance standardLeviXiBoundTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviXiBoundNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
  rationalPoints_nonarchimedeanGroup 𝐋

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs
set_option hygiene false in
local notation "CL" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hCL" => hs.isCentralSplitTorus.isCentral.range_le_center

variable [(CM).Normal] [(CL).Normal]
local instance standardLeviXiBoundIntrinsicQuotientMeasurable :
    MeasurableSpace (rationalPoints 𝐋 ⧸ CL) := borel _
local instance standardLeviXiBoundIntrinsicQuotientBorel :
    BorelSpace (rationalPoints 𝐋 ⧸ CL) := ⟨rfl⟩

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf 𝐌)
    ((K : Subgroup (rationalPoints G)).subgroupOf 𝐌))
  {K0L : Subgroup (rationalPoints 𝐋)}
  (hK0Lc : IsCompact (K0L : Set (rationalPoints 𝐋)))
  (hbasis : Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt iL ν K0L)
  (hcover : RationalPointFamily.FiniteCartanCovering F iL ν K0L)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

include hG hi hν hs hindex hsq hK0Lc hbasis hcover ρ in
/-- Derive the global coefficient Xi bound on the literal standard Levi from
square integrability, the original finite-index premise and the intrinsic Levi's
explicit structural basis and Cartan data. -/
theorem hasXiBoundedCoefficients_standardLeviSquareIntegrable :
    HasXiBoundedCoefficients (rationalLeviXi hKc hMK) π.obj.representation := by
  let AL := leviSchemeRepresentation i ν rootsI π.obj
  let muL := standardLeviIntrinsicQuotientHaar I s mu
  have hsqL : IsSquareIntegrableModCentralSubgroup CL hCL AL.representation muL := by
    exact (isSquareIntegrableModCentralSubgroup_comp_iff
      (RationalPointFamily.leviRationalPointHomeomorph i ν I) CM hCM CL hCL rfl
      mu muL (map_standardLeviIntrinsicQuotientHaar I s mu) π.obj.representation).mpr hsq
  have hbound := hasXiBoundedCoefficients_of_rationalSquareIntegrable
    (isOpen_leviSchemeCompact (i := i) (ν := ν) (J := rootsI) K.isOpen)
    (isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootsI) hKc)
    (isIwasawaPair_leviSchemeCompact hG hi hν (RationalPointFamily.rootSet_subset i ν I) hMK)
    (isConnectedReductive_leviScheme_rootSet hG hi hν I)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν rootsI hi)
    (isGenericCocharacter_leviTorusHom hν) hK0Lc hbasis hcover
    (ρ.restrict (Standard.leviHom i ν rootsI)) hs hindex muL AL hsqL
  exact (hasXiBoundedCoefficients_leviSchemeRepresentation_iff hG hi hν
    (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hMK π.obj).mp hbound

/-- A positive Xi bound for each coefficient of the original standard-Levi representation. -/
def standardLeviSquareIntegrableCoefficientConstant (v : π.obj)
    (ℓ : SmoothDual π.obj.representation) : ℝ :=
  Classical.choose (hasXiBoundedCoefficients_standardLeviSquareIntegrable hG hi hν I s hs hindex
    π mu hsq hKc hMK hK0Lc hbasis hcover ρ v ℓ)

/-- The constant bounds the actual coefficient at all literal Levi points. -/
theorem standardLeviSquareIntegrableCoefficientConstant_spec (v : π.obj)
    (ℓ : SmoothDual π.obj.representation) :
    0 < standardLeviSquareIntegrableCoefficientConstant hG hi hν I s hs hindex π mu hsq
      hKc hMK hK0Lc hbasis hcover ρ v ℓ ∧
    ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤
      standardLeviSquareIntegrableCoefficientConstant hG hi hν I s hs hindex π mu hsq
        hKc hMK hK0Lc hbasis hcover ρ v ℓ * rationalLeviXi hKc hMK m :=
  Classical.choose_spec (hasXiBoundedCoefficients_standardLeviSquareIntegrable hG hi hν I s hs hindex
    π mu hsq hKc hMK hK0Lc hbasis hcover ρ v ℓ)

end Langlands.HarishChandraSchwartz
