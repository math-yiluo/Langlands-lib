import Langlands.Representation.Conductor.UnramifiedPrincipalSeries
import Langlands.Representation.Conductor.Essential

/-!
# Ordered spherical cyclicity and the normalized inverse Whittaker realization

These are proposition definitions for subsequent proof tasks, over arbitrary
nonarchimedean local fields and for the actual normalized induced representation.
-/

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF

/-- Jacquet 2012, Lemma 1: the normalized spherical section generates the entire
upper-Borel principal series when the norms of its parameters are nondecreasing. -/
def OrderedUnramifiedSphericalCyclicityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : Fˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n q : ℕ)
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ),
    Monotone (fun i => ‖(z i : ℂ)‖) →
      ∀ S : Subrepresentation (principalSeries hϖ n hq z),
        sphericalSection hϖ n hq z ∈ S → S = ⊤

/-- Jacquet 2012, Lemma 2 and the following spherical-image comparison:
an inverse-character functional gives an injective coefficient map and can be
normalized so that the spherical section has the explicit spherical image. -/
def OrderedUnramifiedWhittakerRealizationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : Fˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n q : ℕ)
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ),
    Monotone (fun i => ‖(z i : ℂ)‖) →
      ∀ ψ : UnitaryAdditiveCharacter F, HasIntegerConductor ψ →
        ∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z),
          ℓ.val ≠ 0 ∧
          Function.Injective (coefficientMap (principalSeries hϖ n hq z) ℓ) ∧
          ∀ g : Langlands.GeneralLinear (n + 1) F,
            (coefficientMap (principalSeries hϖ n hq z) ℓ
              (sphericalSection hϖ n hq z)).val g =
                Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g

/-- The two ordered unramified principal-series assertions used in Jacquet's
corrected essential-vector argument; neither assertion is supplied as a premise. -/
def OrderedUnramifiedWhittakerStatement : Prop :=
  OrderedUnramifiedSphericalCyclicityStatement.{uF} ∧
    OrderedUnramifiedWhittakerRealizationStatement.{uF}

end Langlands.Conductor
