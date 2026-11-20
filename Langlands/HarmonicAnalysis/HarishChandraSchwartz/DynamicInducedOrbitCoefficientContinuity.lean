import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicInducedOrbitWavePacket
import Langlands.Representation.Plancherel.ProductInducedOrbitCoefficientSmoothness

/-! # Continuity of the actual dynamic orbit coefficient -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.DynamicInducedOrbit

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar UnramifiedOperatorFamily
open MeasureTheory.Measure

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

/-- The Borel structure on `H(F)`. -/
local instance dynamicCoefficientContinuityMeasurableSpace : MeasurableSpace (RationalPoint F H.X) :=
  borel _

local instance dynamicCoefficientContinuityBorelSpace : BorelSpace (RationalPoint F H.X) := ⟨rfl⟩

local instance dynamicCoefficientContinuityParabolicLocallyCompact
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H) : LocallyCompactSpace (parabolic χ) :=
  (parabolic_isClosed χ).locallyCompactSpace

variable (hH : IsConnectedReductive H) (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H)

variable {K : OpenSubgroup (RationalPoint F H.X)} (hK : IsCompact (K : Set (RationalPoint F H.X)))
  (hPK : ∀ g : RationalPoint F H.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F H.X) * (k : RationalPoint F H.X))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi χ))

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)]
  (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option maxHeartbeats 1400000 in
/-- The actual dynamic induced coefficient is continuous in the orbit
parameter, at every evaluation point. -/
theorem continuous_inducedOrbitCoefficientMap
    (q : inducedSmoothOrbitSections hH χ hK hPK π) (g : RationalPoint F H.X) :
    Continuous (fun ω => inducedOrbitCoefficientMap hH χ hK hPK π C hC mu hsq q ω g) :=
  continuous_unitaryOrbitCoefficient (decomposition χ) (radical_isClosed χ) (parabolic_isClosed χ)
    K hK hPK
    (fun x => RationalPointFamily.rationalReductiveUnimodularity F H hH standardCocharacter x)
    (parabolic_modularCharacter_eq hH χ) (leviNormCharacters χ) π
    (leviNormCharacters_continuous χ) (projection_continuous χ)
    (leviUnitaryCoordinates hH χ).toMulEquiv C hC mu hsq (leviUnitaryCoordinates_hasLaurent hH χ)
    (leviUnitaryCoordinates hH χ).continuous q g

end Langlands.HarishChandraSchwartz.DynamicInducedOrbit
