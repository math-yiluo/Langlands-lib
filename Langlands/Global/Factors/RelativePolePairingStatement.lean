import Langlands.Global.Factors.PolePairingDescentStatement
import Langlands.VirtualRepresentation.Global.RelativeImages
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Correspondence.AutomorphicPairFactors

/-!
# Conditional pole comparison for actual witnessed relative pairs

The distinguished functions come from the actual arithmetic tensor L-factor
and a certified automorphic pair L-polynomial. The second input is dualized.
All analytic comparison and pole-identification inputs remain explicit.
-/

noncomputable section

universe uF uW uP

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The class of the full actual local component of a witnessed generator. -/
def witnessedLocalClass (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    Correspondence.AutomorphicClass.{uF, uF} (padicField v) d.rankIndex.succPNat :=
  (d.presentation.localComponent v).padicClass d.local_irreducible d.local_admissible

/-- Evaluation of the actual rational factor in the published variable
`X = q^(-s)`. Values at poles are totalized; orders use punctured germs. -/
def relativeSpectralFunction (R : RatFunc ℂ) : ℂ → ℂ :=
  fun s => RatFunc.eval (RingHom.id ℂ)
    (RankinSelberg.spectralPoint (padicField v).canonicalTopologicalData.residueCardinality s) R

/-- The actual arithmetic factor of the first local representation tensored
with the dual of the second, along their supplied characterized local maps. -/
def witnessedArithmeticPairFunction
    (d e : WitnessedGenerator.{uF, uW, uP} F E c v) : ℂ → ℂ :=
  relativeSpectralFunction F v
    (Correspondence.arithmeticPairLFactor (padicField v)
      (RelativeWeilGroup.localPairClass d.weil d.localMap)
      (RelativeWeilGroup.localPairClass e.weil.dual e.localMap))

/-- Actual dual classes and certified pair polynomials for every pair of
witnessed generators, together with supplied omitted and boundary functions.
The certificate includes factor existence rather than assuming totality. -/
structure RelativePairFactorData
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v)) where
  dualClass : ∀ e : WitnessedGenerator.{uF, uW, uP} F E c v,
    Correspondence.AutomorphicClass.{uF, uF} (padicField v) e.rankIndex.succPNat
  dual_spec : ∀ e, Correspondence.IsSmoothDual (padicField v)
    (witnessedLocalClass F E c v e) (dualClass e)
  polynomial : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → Polynomial ℂ
  polynomial_spec : ∀ d e, Correspondence.IsAutomorphicPairLPolynomial (padicField v) ψ ν
    (witnessedLocalClass F E c v d) (dualClass e) (polynomial d e)
  leftPlaces : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → Finset (FinitePlace F)
  rightPlaces : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → Finset (FinitePlace F)
  leftOmitted : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → FinitePlace F → ℂ → ℂ
  rightOmitted : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → FinitePlace F → ℂ → ℂ
  leftBoundary : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → ℂ → ℂ
  rightBoundary : WitnessedGenerator.{uF, uW, uP} F E c v →
    WitnessedGenerator.{uF, uW, uP} F E c v → ℂ → ℂ

namespace RelativePairFactorData

variable {F E c v}
  {ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)}
  {ν : Correspondence.LocalAdditiveHaarMeasure (padicField v)}

/-- The exact generic comparison datum with actual arithmetic and certified
automorphic distinguished factors. -/
def comparison (d : RelativePairFactorData.{uF, uW, uP} F E c v ψ ν) :
    PairFactorComparisonData (WitnessedGenerator.{uF, uW, uP} F E c v)
      (FinitePlace F) (FinitePlace F) where
  left := witnessedArithmeticPairFunction F E c v
  right := fun j k => relativeSpectralFunction F v
    (Correspondence.automorphicPairLFactor ⟨d.polynomial j k, d.polynomial_spec j k⟩)
  leftPlaces := d.leftPlaces
  rightPlaces := d.rightPlaces
  leftOmitted := d.leftOmitted
  rightOmitted := d.rightOmitted
  leftBoundary := d.leftBoundary
  rightBoundary := d.rightBoundary

end RelativePairFactorData

/-- A self-dual measure exists; every such measure has actual factor witnesses
and explicit meromorphicity, omitted-local-unit, boundary-unit, completed-germ
and signed pole-pairing inputs. Neither factor existence nor measure existence
is replaced by a universal assertion over an empty collection. -/
def RelativeCertifiedPoleComparisons
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)) : Prop :=
  (∃ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
    Correspondence.IsSelfDualMeasure (padicField v) ψ ν) ∧
  ∀ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
    Correspondence.IsSelfDualMeasure (padicField v) ψ ν →
    ∃ d : RelativePairFactorData.{uF, uW, uP} F E c v ψ ν,
      RegularPairComparisonsAt d.comparison 0 ∧
      RealizesPairingAtZero (fun j => j.weilElement) d.comparison.left ∧
      RealizesPairingAtZero (fun j => j.automorphicElement) d.comparison.right

/-- The desired actual generated-span isometry. Generator images, pairings and
degrees use the existing concrete local lattices. Positive norm-one extraction
is asserted only for a vector in the generated source span. -/
def RelativeGeneratedPositiveIsometry
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v) : Prop :=
  (∀ d : WitnessedGenerator.{uF, uW, uP} F E c v,
    T ⟨d.weilElement, witnessed_weil_mem d⟩ =
      ⟨d.automorphicElement, witnessed_automorphic_mem d⟩) ∧
  (∀ x y : weilImage.{uF, uW, uP} F E c v,
    PadicSupercuspidal.unitaryPairing (padicField v) (T x) (T y) =
      LocalWeil.unitaryPairing (padicField v) x y) ∧
  (∀ x : weilImage.{uF, uW, uP} F E c v,
    PadicSupercuspidal.unitaryDegree (padicField v) (T x) =
      LocalWeil.unitaryDegree (padicField v) x) ∧
  (∀ x : weilImage.{uF, uW, uP} F E c v,
    LocalWeil.unitaryPairing (padicField v) x x = 1 →
    0 < LocalWeil.unitaryDegree (padicField v) x →
    ∃! b : PadicSupercuspidal.UnitaryBasis.{uF, uF} (padicField v),
      (T x : PadicSupercuspidal.UnitaryLattice (padicField v)) = generator b)

/-- Conditional concrete pole-to-pairing and generated-isometry adapter.
The arithmetic fundamental class and all representation, presentation, local
map and expansion witnesses remain in the quantified objects. -/
def RelativePolePairingStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
    (∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v,
      LocalWeil.unitaryPairing (padicField v) d.weilElement e.weilElement =
        PadicSupercuspidal.unitaryPairing (padicField v)
          d.automorphicElement e.automorphicElement) ∧
    (relations (fun d : WitnessedGenerator.{uF, uW, uP} F E c v => d.weilElement) =
      relations (fun d : WitnessedGenerator.{uF, uW, uP} F E c v =>
        d.automorphicElement)) ∧
    ∃! T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v,
      RelativeGeneratedPositiveIsometry F E c v T

end Langlands.Global.PoleComparison
