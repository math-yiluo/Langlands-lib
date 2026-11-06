import Langlands.Correspondence.SphericalStandardLComparisonStatement
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Representation.Classification.RankOneLanglandsStandardModule

/-!
# Representation and analytic prerequisites for the spherical standard polynomial

The propositions below are proof obligations, and the final theorem is only a
conditional assembly of them. Neither obligation is assumed as an axiom.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance prerequisiteFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance prerequisiteGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- A spherical representation has a tempered quotient presentation whose
actual standard module is an unramified principal series, in some ordering
with weakly increasing absolute values and with the prescribed spectrum. -/
def SphericalTemperedStandardModuleStatement : Prop :=
  ∀ (r : ℕ) (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (s : Unramified.Eigenvalues (r + 1)),
    Nonempty (J.representation.Equiv A.obj.representation) →
    Unramified.HasSphericalSpectrum F A s →
      ∃ (d : PadicField.TopologicalData.TemperedLanglandsDatum.{uA, uF}
          F.canonicalTopologicalData (r + 1))
        (z : Fin (r + 1) → ℂˣ),
        d.IsLanglandsQuotient J ∧
        Unramified.Eigenvalues.ofTuple z = s ∧
        Monotone (fun i => ‖(z i : ℂ)‖) ∧
        Nonempty (d.standardModule.representation.Equiv
          (Unramified.principalSeriesOfTuple F z))

/-- The supplied JPSS polynomial of an unramified principal series in standard
order, against the trivial rank-one character, is its Euler polynomial. -/
def OrderedUnramifiedPrincipalSeriesLPolynomialStatement : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
      ∀ (r : ℕ) (z : Fin (r + 1) → ℂˣ) (P : Polynomial ℂ),
        Monotone (fun i => ‖(z i : ℂ)‖) →
        RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν
          (Unramified.principalSeriesOfTuple F z)
          (characterRepresentation (determinantQuasiCharacter F 1 1)) P →
        P = Unramified.Eigenvalues.eulerPolynomial (Unramified.Eigenvalues.ofTuple z)

/-- The two remaining, independent prerequisites for the class comparison. -/
def SphericalStandardLPrerequisitesStatement : Prop :=
  SphericalTemperedStandardModuleStatement.{uF, uA} F ∧
    OrderedUnramifiedPrincipalSeriesLPolynomialStatement.{uF} F

/-- The actual representative relations and the rank-one equivalence reduce the
unchanged class comparison to the two stated prerequisites. -/
theorem sphericalStandardLComparison_of_prerequisites
    (hmodule : SphericalTemperedStandardModuleStatement.{uF, uA} F)
    (hpolynomial : OrderedUnramifiedPrincipalSeriesLPolynomialStatement.{uF} F) :
    SphericalStandardLComparisonStatement.{uF, uA} F := by
  intro ψ ν hν r π π0 s P hπ0 hs hP
  obtain ⟨A, A0, J, J0, hA, hA0, ⟨a⟩, ⟨a0⟩, hP⟩ := hP
  have hsA : Unramified.HasSphericalSpectrum F A s :=
    (Unramified.hasSphericalSpectrumClass_classOf F A s).mp
      (by simpa only [hA] using hs)
  obtain ⟨d, z, hd, hz, horder, ⟨ed⟩⟩ := hmodule r A J s ⟨a⟩ hsA
  obtain ⟨B0, hB0, ⟨b0⟩⟩ := hπ0
  obtain ⟨c0⟩ := (automorphicClassOf_eq_iff F B0 A0).mp (hB0.trans hA0.symm)
  obtain ⟨e, he⟩ := hP.2.1
  let e0 := ((e.standardModuleEquivRankOne J0 he).trans a0).trans
    (c0.symm.trans b0.symm)
  have hstandard := hP.2.2 d e hd he
  have hprincipal :=
    (RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv ed e0).mp hstandard
  exact (hpolynomial ψ ν hν r z P horder hprincipal).trans
    (congrArg Unramified.Eigenvalues.eulerPolynomial hz)

end Langlands.Correspondence
