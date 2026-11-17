import Langlands.Representation.Plancherel.StandardLeviPlancherelWeight
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof

/-! # Orbit sections, coefficients, wave packets and Plancherel weights for dynamic parabolics

For a connected reductive group `H` over a nonarchimedean local field and an arbitrary
cocharacter `χ : 𝔾_m → H`, the actual dynamic parabolic `P(χ)(F) = Z_H(χ)(F) ⋉ U(χ)(F)` is in
general only semistandard. This module instantiates the Library's abstract orbit constructions
(`productInducedSmoothOrbitSections`, `unitaryOrbitCoefficientMap`, `inducedOrbitWavePacket`)
on these actual data, and descends the published Plancherel weight `plancherelWeight` to the
unitary unramified orbit of a discrete series of the literal Levi `Z_H(χ)(F)`, with all its
inputs bundled in an explicit package.
-/

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
local instance dynamicInducedOrbitMeasurableSpace : MeasurableSpace (RationalPoint F H.X) :=
  borel _

local instance dynamicInducedOrbitBorelSpace : BorelSpace (RationalPoint F H.X) := ⟨rfl⟩

local instance dynamicInducedOrbitParabolicLocallyCompact
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H) : LocallyCompactSpace (parabolic χ) :=
  (parabolic_isClosed χ).locallyCompactSpace

variable (hH : IsConnectedReductive H) (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H)

/-! ### Structural inputs -/

/-- **Circle coordinates on `Im X(Z_H(χ))`** for the literal Levi `Z_H(χ)(F) ⊆ H(F)`: the
Library's canonical coordinates of the unitary unramified characters of the centralizer scheme
`parameterScheme χ`, transported along its point homeomorphism `parameterHomeomorph χ`. -/
def leviUnitaryCoordinates :
    unitaryUnramifiedCharacters (leviNormCharacters χ) ≃ₜ*
      (Fin (rationalImageRank (parameterScheme χ)) → Circle) :=
  (unitaryUnramifiedCharactersHomeomorph (parameterHomeomorph χ) (normCharacters χ)).symm.trans
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates (parameterScheme χ)
      (parameterScheme_isConnectedReductive χ hH))

omit [LocallyOfFiniteType H.X.hom] in
include hH in
/-- Evaluation of a unitary unramified character of `Z_H(χ)(F)` at a point is a Laurent monomial
of the coordinates `leviUnitaryCoordinates`. -/
theorem leviUnitaryCoordinates_hasLaurent :
    HasLaurentUnitaryCoordinates (leviNormCharacters χ)
      (leviUnitaryCoordinates hH χ).toMulEquiv :=
  hasLaurentUnitaryCoordinates_transport (parameterHomeomorph χ) (normCharacters χ) _
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent (parameterScheme χ)
      (parameterScheme_isConnectedReductive χ hH))

omit [LocallyOfFiniteType H.X.hom] in
/-- The literal Levi norm characters are continuous. -/
theorem leviNormCharacters_continuous (ψ : rationalCharacters (parameterScheme χ)) :
    Continuous (leviNormCharacters χ ψ) :=
  (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous

include hH in
/-- **The modular character of the actual dynamic parabolic** is the Haar modulus of conjugation
on its radical: `δ_{P(χ)}(p) = δ_{U(χ)}(p)`. Both the Levi `Z_H(χ)(F)` and the radical are
unimodular (`levi_modularCharacter_eq_one`, `radical_unimodular`). -/
theorem parabolic_modularCharacter_eq (p : parabolic χ) :
    modularCharacter p =
      (HaarModulus.closedRestrictCharacter (radical χ) (radical_isClosed χ) (parabolic χ)
        (decomposition χ).le_normalizer p : ℝ≥0) := by
  have : LocallyCompactSpace (radical χ) := (radical_isClosed χ).locallyCompactSpace
  have : LocallyCompactSpace (levi χ) := (levi_isClosed χ).locallyCompactSpace
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    (decomposition χ).modularCharacter_eq_restrictCharacter_of_unimodular
      (projection_continuous χ)
      (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hH)
      (fun u => by simpa using radical_unimodular χ hH u) p

/-! ### Sections, coefficients and wave packets -/

variable {K : OpenSubgroup (RationalPoint F H.X)} (hK : IsCompact (K : Set (RationalPoint F H.X)))
  (hPK : ∀ g : RationalPoint F H.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F H.X) * (k : RationalPoint F H.X))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi χ))

/-- **Waldspurger's `C^∞(O, P)` for the actual dynamic parabolic `P = P(χ)(F)`** (VI.1): the
Library's smooth orbit sections over the unitary unramified twist orbit of the irreducible
admissible representation `π` of the literal Levi `Z_H(χ)(F)`, for the actual decomposition
`P(χ)(F) = Z_H(χ)(F) ⋉ U(χ)(F)`, the compact open `K`, the norm characters `leviNormCharacters χ`
and the circle coordinates `leviUnitaryCoordinates`. -/
abbrev inducedSmoothOrbitSections :=
  productInducedSmoothOrbitSections (G := RationalPoint F H.X) (M := levi χ)
    (leviNormCharacters χ) π (leviUnitaryCoordinates hH χ).toMulEquiv (decomposition χ)
    (radical_isClosed χ) K (parabolic_isClosed χ) hK (leviNormCharacters_continuous χ)
    (projection_continuous χ) hPK

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- **The coefficients `ω ↦ E^H_{P(χ)} ψ_ω` on the orbit** for the actual dynamic parabolic: the
Library's `unitaryOrbitCoefficientMap` on the actual data of `P(χ)(F)`, with the unimodularity
of `H(F)` (`rationalReductiveUnimodularity`) and the modular character of `P(χ)(F)`
(`parabolic_modularCharacter_eq`). -/
abbrev inducedOrbitCoefficientMap :=
  unitaryOrbitCoefficientMap (G := RationalPoint F H.X) (M := levi χ) (decomposition χ)
    (radical_isClosed χ) (parabolic_isClosed χ) K hK hPK
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F H hH standardCocharacter g)
    (parabolic_modularCharacter_eq hH χ) (leviNormCharacters χ) π
    (leviNormCharacters_continuous χ) (projection_continuous χ) C hC mu hsq
    (leviUnitaryCoordinates hH χ).toMulEquiv

variable [Finite (discreteSeriesStabilizer C hC mu (leviNormCharacters χ)
    (discreteSeriesClass C hC mu π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters (leviNormCharacters χ)))
  (w : discreteSeriesOrbit C hC mu (leviNormCharacters χ) (discreteSeriesClass C hC mu π hsq) → ℂ)

/-- **The wave packet for the actual dynamic parabolic** (Waldspurger VI.3, printed p.302): for
`ψ = q ∈ C^∞(O, P(χ))`, `f_ψ(h) = ∫_O w(ω) (E^H_{P(χ)} ψ_ω)(h) dω`, `h ∈ H(F)`, for the orbit
measure attached to a measure `ρ` on `Im X(Z_H(χ))` and a weight `w` on `O`. It is the Library's
`inducedOrbitWavePacket` on the actual data of `P(χ)(F)`. -/
def inducedOrbitWavePacket (q : inducedSmoothOrbitSections hH χ hK hPK π)
    (h : RationalPoint F H.X) : ℂ :=
  HarishChandraSchwartz.inducedOrbitWavePacket (G := RationalPoint F H.X) (M := levi χ)
    (decomposition χ) (radical_isClosed χ) (parabolic_isClosed χ) K hK hPK
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F H hH standardCocharacter g)
    (parabolic_modularCharacter_eq hH χ) (leviNormCharacters χ) π
    (leviNormCharacters_continuous χ) (projection_continuous χ)
    (leviUnitaryCoordinates hH χ).toMulEquiv C hC mu hsq ρ w q h

/-- `f_ψ(h) = ∫_O w(ω) (E^H_{P(χ)} ψ_ω)(h) dω`. -/
theorem inducedOrbitWavePacket_apply (q : inducedSmoothOrbitSections hH χ hK hPK π)
    (h : RationalPoint F H.X) :
    inducedOrbitWavePacket hH χ hK hPK π C hC mu hsq ρ w q h =
      ∫ ω, w ω * inducedOrbitCoefficientMap hH χ hK hPK π C hC mu hsq q ω h
        ∂discreteSeriesOrbitMeasure (leviNormCharacters χ) C hC mu
          (discreteSeriesClass C hC mu π hsq) ρ :=
  rfl

end Langlands.HarishChandraSchwartz.DynamicInducedOrbit
