import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.Representation.Plancherel.RationalPlancherelConstantFinite
import Langlands.Representation.Plancherel.ActualOppositeCompactScalar

/-! # Evaluating the density factors using actual canonical scalars -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
set_option quotPrecheck false
set_option hygiene false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeCanonicalScalar UnramifiedOperatorFamily RationalDynamicSource
open DynamicOppositeStandardIntertwining hiding centralizerClosedImmersion centralizerAffine

attribute [local instance]
  dynamicOppositeCanonicalScalarIsAffine dynamicOppositeCanonicalScalarTopologicalSpace
  dynamicOppositeCanonicalScalarT2Space dynamicOppositeCanonicalScalarIsTopologicalGroup
  dynamicOppositeCanonicalScalarT2Space2 dynamicOppositeCanonicalScalarLocallyCompactSpace
  dynamicOppositeCanonicalScalarNonarchimedeanGroup dynamicOppositeCanonicalScalarSecondCountableTopology
  dynamicOppositeCanonicalScalarSecondCountableTopology2 centralizerClosedImmersion centralizerAffine
  centralizerFiniteType dynamicOppositeCanonicalScalarTopologicalSpace2
  dynamicOppositeCanonicalScalarNonarchimedeanGroup2

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {j : S.toGrp ⟶ H} {ξ : cocharacterLattice S}
  {hRefl : RelativeRootReflectionExistenceStatement.{u}}
  {hCST : CentralSplitTorusCharacterStatement.{u}} {hH : IsConnectedReductive H}
  {A : SmoothRep.{0, u, uV} ℂ (levi (CommGroupScheme.groupHom ξ ≫ j))}
  (P : DynamicInducedOrbit.DensityPackage j ξ hRefl hCST hH A)

local notation "χ" => CommGroupScheme.groupHom ξ ≫ j
local notation "J" => parameterScheme χ
local notation "hp" => parameterProjection_continuous χ
local notation "hj" => parameterScheme_isConnectedReductive χ hH
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "Frac" => rationalUnramifiedFunctionField J hp hj
local notation "dP" => (RationalPlancherelDensity.plancherelDensityConstant j ξ P.K P.hK : ℂ)

/-- A fraction for the canonical round trip gives the reciprocal fraction
for the actual Plancherel density wherever the numerator of the trip is nonzero. -/
theorem packageDensity_value_of_scalarFraction {a b : R}
    {z : unramifiedCharacters (normCharacters χ)}
    (h : RationalFunctionRegularAt J hp hj (packageDensity P) z)
    (hj' : P.canonicalScalar = algebraMap R Frac a / algebraMap R Frac b)
    (ha : a.val z ≠ 0) : rationalValueAt (packageDensity P) h = dP * (b.val z / a.val z) := by
  let c : R := algebraMap ℂ R dP
  have hd : packageDensity P = algebraMap R Frac (c * b) / algebraMap R Frac a := by
    change algebraMap R Frac c * (P.canonicalScalar)⁻¹ = _
    rw [hj', inv_div, ← mul_div_assoc, ← map_mul]
  exact (rationalValueAt_eq h ha hd).trans (mul_div_assoc _ _ _)

/-- The density constant of a package for a split torus is nonzero. -/
theorem packageDensityConstant_ne_zero (hs : IsSplitTorus S.toGrp) : dP ≠ 0 := by
  let : Smooth H.X.hom := hH.smooth
  let : ConnectedSpace H.X.left := hH.connectedSpace
  apply Complex.ofReal_ne_zero.mpr
  exact (RationalPlancherelDensity.plancherelDensityConstant_pos j ξ P.K P.hK
    (rankOneGammaProduct_ne_top_of_isSplitTorus j ξ P.K P.hK hs)).ne'

/-- If the canonical round trip vanishes identically, the package density
evaluates to zero at every regular parameter. -/
theorem packageDensity_value_of_scalar_zero
    {z : unramifiedCharacters (normCharacters χ)}
    (h : RationalFunctionRegularAt J hp hj (packageDensity P) z)
    (h0 : P.canonicalScalar = 0) : rationalValueAt (packageDensity P) h = 0 := by
  have hf : packageDensity P = algebraMap R Frac 0 / algebraMap R Frac 1 := by
    change RationalPlancherelDensity.fieldConstant j ξ hH dP * (P.canonicalScalar)⁻¹ = _
    simp [h0]
  simpa using rationalValueAt_eq h (by simp : (1 : R).val z ≠ 0) hf

/-- The canonical scalar of a package is a quotient of regular functions,
and at each common regular parameter its two actual compact continuations
compose to the value of that quotient. -/
theorem package_compact_spec :
    ∃ a b : R, b ≠ 0 ∧
      (∀ z : ↥(P.p.regularRegion ∩ P.q.regularRegion), b.val z.val ≠ 0) ∧
      P.canonicalScalar = algebraMap R Frac a / algebraMap R Frac b ∧
      ∀ z : ↥(P.p.regularRegion ∩ P.q.regularRegion),
        P.p.continuedComposite P.q z = (a.val z.val / b.val z.val) • LinearMap.id :=
  conditionalCanonicalRationalScalar_compact_spec χ P.K P.hK hRefl hCST hH A P.hPK P.hOppK
    P.p P.q P.hDForward P.hneForward P.hDForwardΩ P.hDReverse P.hneReverse P.hDReverseΩ
    P.hD P.hne P.hirr

section Complex

/-- The ratio of actual densities cancels the scalar of the outer
round trip after the two positive Haar comparisons are accounted for. -/
theorem weight_mul_roundTrip_of_scalar_product {outer inner j C t : ℂ}
    (ho : outer ≠ 0) (h : j * (t * inner) = C * outer) (ht : t ≠ 0)
    (k : ℂ) : (k * (inner / outer)) * j = k * (C / t) := by
  have h' : inner * j = (C * outer) / t := by
    apply (eq_div_iff ht).2
    linear_combination h
  rw [mul_assoc, div_mul_eq_mul_div, h']
  congr 1
  field_simp

end Complex

end Langlands.HarishChandraSchwartz.WeakExpansion
