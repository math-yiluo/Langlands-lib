import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitPlancherelWeight
import Langlands.Representation.Plancherel.DynamicOppositeCompactChange
import Langlands.Representation.Plancherel.RationalPlancherelConstantFinite

/-! # Compact change for the density package and unitary orbit weight -/

noncomputable section

set_option maxRecDepth 2048

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.DynamicInducedOrbit.DensityPackage

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar UnramifiedOperatorFamily
open RationalDynamicSource RationalPlancherelDensity

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (j : T.toGrp ⟶ H) (ζ : cocharacterLattice T)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hH : IsConnectedReductive H)

set_option hygiene false in
local notation "χ" => (CommGroupScheme.groupHom ζ ≫ j)
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ j)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ j) hH
set_option hygiene false in
local notation "Reg" => unramifiedRegularFunctions (normCharacters (CommGroupScheme.groupHom ζ ≫ j))
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (normCharacters (CommGroupScheme.groupHom ζ ≫ j))

variable {A : SmoothRep.{0, u, uV} ℂ (levi (CommGroupScheme.groupHom ζ ≫ j))}

private theorem fieldConstant_inv (c : ℂ) :
    fieldConstant j ζ hH c⁻¹ = (fieldConstant j ζ hH c)⁻¹ :=
  map_inv₀ ((algebraMap Reg (DensityField j ζ hH)).comp (algebraMap ℂ Reg)) c

variable {j ζ hRefl hCST hH}
  (P : DensityPackage j ζ hRefl hCST hH A)
  (L : OpenSubgroup (RationalPoint F H.X))
  (hL : IsCompact (L : Set (RationalPoint F H.X)))
  (hPL : ∀ g : RationalPoint F H.X,
    ∃ p : parabolic (CommGroupScheme.groupHom ζ ≫ j), ∃ l : L,
      g = (p : RationalPoint F H.X) * (l : RationalPoint F H.X))
  (hOppL : ∀ g : RationalPoint F H.X,
    ∃ p : oppositeParabolic (CommGroupScheme.groupHom ζ ≫ j), ∃ l : L,
      g = (p : RationalPoint F H.X) * (l : RationalPoint F H.X))

set_option hygiene false in
local notation "pL" => forwardContinuationChangeCompact χ P.K L P.hK hL hRefl hCST hH A
  P.hPK P.hOppK hPL hOppL P.p
set_option hygiene false in
local notation "qL" => reverseContinuationChangeCompact χ P.K L P.hK hL hRefl hCST hH A
  P.hPK P.hOppK hPL hOppL P.q
set_option hygiene false in
local notation "hForwardL" => Set.Subset.trans P.hDForwardΩ
  (Eq.ge (forwardFullDomainRegion_changeCompact χ P.K L P.hK hL A))
set_option hygiene false in
local notation "hReverseL" => Set.Subset.trans P.hDReverseΩ
  (Eq.ge (reverseFullDomainRegion_changeCompact χ P.K L P.hK hL A))
set_option hygiene false in
local notation "haarScale" => (oppositeQuotientHaarScale χ P.K L P.hK hL : ℝ)
set_option hygiene false in
local notation "canonicalL" => conditionalCanonicalRationalScalar χ hRefl hCST hH L hL hPL hOppL A
  pL qL P.hneForward hForwardL P.hneReverse hReverseL P.hne P.hirr

set_option maxHeartbeats 700000 in
private theorem canonicalInverse_changeCompact :
    (canonicalL)⁻¹ = fieldConstant j ζ hH (haarScale : ℂ)⁻¹ * P.canonicalScalar⁻¹ := by
  have hscalar := conditionalCanonicalRationalScalar_changeCompact χ P.K L P.hK hL hRefl hCST hH A
    P.hPK P.hOppK hPL hOppL P.p P.q P.hDForward P.hneForward P.hDForwardΩ
    P.hDReverse P.hneReverse P.hDReverseΩ P.hD P.hne P.hirr
  calc
    _ = (fieldConstant j ζ hH (haarScale : ℂ) * P.canonicalScalar)⁻¹ := congrArg Inv.inv hscalar
    _ = _ := by rw [mul_inv_rev, ← fieldConstant_inv j ζ hH, mul_comm]

set_option maxHeartbeats 700000 in
/-- Change the continuation compact and transport unitary regularity of the same
canonical inverse by the inverse quotient Haar factor. -/
def changeCompact : DensityPackage j ζ hRefl hCST hH A where
  K := L
  hK := hL
  hPK := hPL
  hOppK := hOppL
  p := pL
  q := qL
  DForward := P.DForward
  DReverse := P.DReverse
  hDForward := P.hDForward
  hneForward := P.hneForward
  hDForwardΩ := hForwardL
  hDReverse := P.hDReverse
  hneReverse := P.hneReverse
  hDReverseΩ := hReverseL
  D := P.D
  hD := P.hD
  hne := P.hne
  hirr := P.hirr
  hreg :=
    Eq.mpr (congrArg (RationalFunctionUnitaryRegular MS hMS)
      (canonicalInverse_changeCompact P L hL hPL hOppL))
      ((rationalFunctionUnitaryRegular_algebraMap MS hMS
        (algebraMap ℂ Reg (haarScale : ℂ)⁻¹)).mul MS hMS P.hreg)

set_option maxHeartbeats 700000 in
private theorem inverseValue_changeCompact (z : UL) :
    rationalUnitaryValue MS hMS (P.changeCompact L hL hPL hOppL).canonicalScalar⁻¹
        (P.changeCompact L hL hPL hOppL).hreg z =
      (haarScale : ℂ)⁻¹ * rationalUnitaryValue MS hMS P.canonicalScalar⁻¹ P.hreg z := by
  let c : Reg := algebraMap ℂ Reg (haarScale : ℂ)⁻¹
  let hc := rationalFunctionUnitaryRegular_algebraMap MS hMS c
  let hprod := hc.mul MS hMS P.hreg
  have h := congrFun (rationalUnitaryValue_congr MS hMS
    (canonicalInverse_changeCompact P L hL hPL hOppL)
    (P.changeCompact L hL hPL hOppL).hreg hprod) z
  have hm := rationalUnitaryValue_mul MS hMS hc P.hreg z
  have hv := rationalUnitaryValue_algebraMap MS hMS c z
  exact h.trans (hm.trans (congrArg (fun w =>
    w * rationalUnitaryValue MS hMS P.canonicalScalar⁻¹ P.hreg z) hv))

/-- The ratio of the two rank-one density constants, divided by the
forward and reverse quotient Haar product. -/
def compactDensityScale : ℝ :=
  plancherelDensityConstant j ζ L hL / (plancherelDensityConstant j ζ P.K P.hK * haarScale)

include hH in
private theorem densityConstant_pos (K : OpenSubgroup (RationalPoint F H.X))
    (hK : IsCompact (K : Set (RationalPoint F H.X))) (hT : IsSplitTorus T.toGrp) :
    0 < plancherelDensityConstant j ζ K hK := by
  let : Smooth H.X.hom := hH.smooth
  let : ConnectedSpace H.X.left := hH.connectedSpace
  exact plancherelDensityConstant_pos j ζ K hK
    (rankOneGammaProduct_ne_top_of_isSplitTorus j ζ K hK hT)

theorem compactDensityScale_pos (hT : IsSplitTorus T.toGrp) :
    0 < P.compactDensityScale L hL :=
  div_pos (densityConstant_pos (j := j) (ζ := ζ) (hH := hH) L hL hT)
    (mul_pos (densityConstant_pos (j := j) (ζ := ζ) (hH := hH) P.K P.hK hT)
      (NNReal.coe_pos.mpr (oppositeQuotientHaarScale_pos χ P.K L P.hK hL)))

set_option maxHeartbeats 600000 in
private theorem weight_eq_const_mul (z : UL) :
    P.weight z = (plancherelDensityConstant j ζ P.K P.hK : ℂ) *
        rationalUnitaryValue MS hMS P.canonicalScalar⁻¹ P.hreg z :=
  plancherelWeight_eq j ζ hRefl hCST hH P.K P.hK P.hPK P.hOppK A P.p P.q
    P.hneForward P.hDForwardΩ P.hneReverse P.hDReverseΩ P.hne P.hirr P.hreg z

private theorem mul_inv_value (k l s : ℝ) (hk : k ≠ 0) (hs : s ≠ 0) (v : ℂ) :
    (l : ℂ) * ((s : ℂ)⁻¹ * v) =
      ((l / (k * s) : ℝ) : ℂ) * ((k : ℂ) * v) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp [hkC, hsC]

set_option maxHeartbeats 900000 in
/-- The unitary weight is multiplied by the positive compact density scale.
The factor depends on compact normalizations and is independent of the character. -/
theorem changeCompact_weight (hT : IsSplitTorus T.toGrp) (z : UL) :
    (P.changeCompact L hL hPL hOppL).weight z = (P.compactDensityScale L hL : ℂ) * P.weight z := by
  let v := rationalUnitaryValue MS hMS P.canonicalScalar⁻¹ P.hreg z
  have hk := densityConstant_pos (j := j) (ζ := ζ) (hH := hH) P.K P.hK hT
  have hs : 0 < haarScale := NNReal.coe_pos.mpr (oppositeQuotientHaarScale_pos χ P.K L P.hK hL)
  calc
    _ = (plancherelDensityConstant j ζ L hL : ℂ) *
        rationalUnitaryValue MS hMS (P.changeCompact L hL hPL hOppL).canonicalScalar⁻¹
          (P.changeCompact L hL hPL hOppL).hreg z :=
      weight_eq_const_mul (P.changeCompact L hL hPL hOppL) z
    _ = (plancherelDensityConstant j ζ L hL : ℂ) * ((haarScale : ℂ)⁻¹ * v) :=
      congrArg ((plancherelDensityConstant j ζ L hL : ℂ) * ·)
        (inverseValue_changeCompact P L hL hPL hOppL z)
    _ = (P.compactDensityScale L hL : ℂ) * ((plancherelDensityConstant j ζ P.K P.hK : ℂ) * v) :=
      mul_inv_value _ _ _ hk.ne' hs.ne' v
    _ = _ := congrArg ((P.compactDensityScale L hL : ℂ) * ·) (weight_eq_const_mul P z).symm

section Orbit

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
    (G := levi (CommGroupScheme.groupHom ζ ≫ j)))
  (C : Subgroup (levi (CommGroupScheme.groupHom ζ ≫ j))) [C.Normal]
  (hC : C ≤ Subgroup.center (levi (CommGroupScheme.groupHom ζ ≫ j)))
  [MeasurableSpace (levi (CommGroupScheme.groupHom ζ ≫ j) ⧸ C)]
  (mu : Measure (levi (CommGroupScheme.groupHom ζ ≫ j) ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (Pπ : DensityPackage j ζ hRefl hCST hH π.obj)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu (leviNormCharacters χ)
  (discreteSeriesClass C hC mu π hsq)

set_option maxHeartbeats 900000 in
/-- The same constant relates the two weights on the original discrete-series orbit. -/
theorem changeCompact_orbitPlancherelWeight (hT : IsSplitTorus T.toGrp) (ω : Oπ) :
    orbitPlancherelWeight j ζ hRefl hCST hH π C hC mu hsq (Pπ.changeCompact L hL hPL hOppL) ω =
      (Pπ.compactDensityScale L hL : ℂ) * orbitPlancherelWeight j ζ hRefl hCST hH π C hC mu hsq Pπ ω := by
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu (leviNormCharacters χ)
    (discreteSeriesClass C hC mu π hsq)).surjective ω
  rw [orbitPlancherelWeight_orbitMap, orbitPlancherelWeight_orbitMap]
  exact changeCompact_weight Pπ L hL hPL hOppL hT (leviCharacterRestrict χ z)

end Orbit

end Langlands.HarishChandraSchwartz.DynamicInducedOrbit.DensityPackage
