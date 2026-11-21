import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.VirtualRepresentation.Global.RelativeTrivialGenerator
import Langlands.Correspondence.SphericalStandardTwistFactors

/-! # Standard factors of the actual spherical finite components -/

noncomputable section

set_option autoImplicit false

universe u uP

namespace Langlands.Automorphic.ConstantFunctions

open Global Global.CompletionPadic Global.CuspidalPairFunctionalEquation
open RankinSelberg

variable (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]

set_option maxHeartbeats 1600000 in
/-- Each actual component of the rank-one constant presentation is irreducible and admissible. -/
theorem rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents :
    HasIrreducibleAdmissibleComponents (rankOneSpectralPresentation.{u, uP} K) := by
  intro v
  exact ⟨((rankOneSpectralPresentation.{u, uP} K).presentation.localComponent_isIrreducible_iff
      (rankOneSpectralPresentation.{u, uP} K).finiteSlice.nonzero v).mpr
      (tensorLocalModel_isIrreducible.{u, uP} K 1 v),
    ((rankOneSpectralPresentation.{u, uP} K).presentation.localComponent_isAdmissible_iff
      (rankOneSpectralPresentation.{u, uP} K).finiteSlice.nonzero v).mpr
      (tensorLocalModel_isAdmissible.{u, uP} K 1 v)⟩

/-- The trivial character acts on the actual embedded constant rank-one component. -/
theorem rankOneSpectralPresentation_localTrivialEquiv (v : FinitePlace K) :
    Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      ((rankOneSpectralPresentation.{u, uP} K).localComponent v).representation) := by
  let F := padicField v
  let := F.canonicalTopologicalData.topology
  let e : (Correspondence.rankOneSupercuspidalObject.{u, u} F 1).obj.representation.Equiv
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) :=
    FiniteRepresentation.characterLineEquiv (Correspondence.determinantQuasiCharacter F 1 1)
  exact ⟨e.symm.trans (VirtualRepresentation.RelativeGlobal.trivialLocalAutomorphicEquiv.{u, uP} K v)⟩

end Langlands.Automorphic.ConstantFunctions

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Unramified RankinSelberg
open LocalFactor.PadicAbelian (lPolynomial epsilonExponent)

/-- The standard factor formula passes to any representative of the determinant-twisted class. -/
theorem standardFactors_of_characterTwistClass {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) {r : ℕ} (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    (J : AutomorphicObject.{u, u} F r.succPNat) (J₁ : AutomorphicObject.{u, u} F 1)
    (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖)
    (hJ : (unramifiedDatum.{u, u} F z hz).IsLanglandsQuotient J.obj)
    (e₁ : letI := F.canonicalTopologicalData.topology
      Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁.obj.representation))
    (ω : QuasiCharacter F) (c : AutomorphicClass.{u, u} F r.succPNat)
    (ht : IsCharacterTwist F ω (automorphicClassOf F J) c)
    {Q : Polynomial ℂ} {b : ℂˣ × ℤ}
    (hQ : IsAutomorphicPairLPolynomial F ψ ν c (automorphicClassOf F J₁) Q)
    (hb : IsAutomorphicPairEpsilonFactor F ψ ν c (automorphicClassOf F J₁) b) :
    Q = (∏ i, lPolynomial F.canonicalTopologicalData (character F (z i) * ω)) ∧
    b.2 = ∑ i, epsilonExponent F.canonicalTopologicalData (character F (z i) * ω) ψ := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨J₀, Jω, he, rfl, ⟨e⟩⟩ := ht
  obtain ⟨e₀⟩ := (automorphicClassOf_eq_iff F J J₀).mp he.symm
  let eω := (Langlands.twistEquiv (determinantQuasiCharacter F r.succPNat ω) e₀).trans e
  exact sphericalStandardTwistFactors.{u, u, u} p F r ψ ν hν z hz ω
    J.obj Jω.obj J₁.obj hJ ⟨eω⟩ e₁ Q b
    ((isAutomorphicPairLPolynomial_iff F Jω J₁ Jω.obj J₁.obj
      (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hQ)
    ((isAutomorphicPairEpsilonFactor_iff F Jω J₁ Jω.obj J₁.obj
      (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hb)

/-- A single ordered tuple of spherical parameters computes the actual standard Euler
polynomial and epsilon exponent of each determinant twist at the chosen completion. -/
def SphericalStandardFactorsAtCompletionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r) (P : CuspidalSpectralPresentation.{u, uP} T)
    (v : FinitePlace K) (hv : v ∉ P.exceptional) (h : HasIrreducibleAdmissibleComponents P)
    (T₁ : CuspidalOperatorRealization K 0) (P₁ : CuspidalSpectralPresentation.{u, uP} T₁)
    (h₁ : HasIrreducibleAdmissibleComponents P₁),
    Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (P₁.localComponent v).representation) →
    ∃ z : Fin (r + 1) → ℂˣ, Monotone (fun i => ‖(z i : ℂ)‖) ∧
      Eigenvalues.ofTuple z = P.spectralSystem.eigenvalues v hv ∧
      ∀ (χ : HeckeCharacter K) (ψ : NontrivialAdditiveCharacter (padicField v))
        (ν : LocalAdditiveHaarMeasure (padicField v)), IsSelfDualMeasure (padicField v) ψ ν →
      ∀ (Q : Polynomial ℂ) (b : ℂˣ × ℤ),
        let c := localClass (P.heckeDeterminantTwist χ)
          (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h) v
        IsAutomorphicPairLPolynomial (padicField v) ψ ν c (localClass P₁ h₁ v) Q →
        IsAutomorphicPairEpsilonFactor (padicField v) ψ ν c (localClass P₁ h₁ v) b →
        let ω := quasicharacterBase v (χ.finiteComponent v)
        Q = (∏ i, lPolynomial (padicField v).canonicalTopologicalData (character (padicField v) (z i) * ω)) ∧
        b.2 = ∑ i, epsilonExponent (padicField v).canonicalTopologicalData
          (character (padicField v) (z i) * ω) ψ

set_option maxHeartbeats 1800000 in
/-- Apply the standard factor formulas to the actual canonical p-adic objects of the
original and twisted presentations. -/
theorem sphericalStandardFactorsAtCompletion : SphericalStandardFactorsAtCompletionStatement.{u, uP} := by
  intro K _ _ _ r T P v hv h T₁ P₁ h₁ e₁
  let F := padicField v
  let J := (P.localComponent v).padicObject (h v).1 (h v).2
  let J₁ := (P₁.localComponent v).padicObject (h₁ v).1 (h₁ v).2
  let s := P.spectralSystem.eigenvalues v hv
  have hsc := ((P.localComponent v).hasSphericalHeckeSpectrumClass_iff (h v).1 (h v).2 s).mpr
    (P.hasSpectrum v hv)
  have hs := hasSphericalSpectrum_of_hasSphericalHeckeSpectrum F J s
    ((hasSphericalHeckeSpectrumClass_classOf F J s).mp hsc)
  obtain ⟨z, hz, he, hJ⟩ := exists_unramifiedDatum_isLanglandsQuotient.{u, u}
    F J J.obj (Representation.Equiv.refl _) _ hs
  refine ⟨z, hz, he, ?_⟩
  intro χ ψ ν hν Q b c hQ hb
  let hχ := P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h
  have ht := P.isCharacterTwist_heckeDeterminantTwist_padicClass χ v
    (h v).1 (h v).2 (hχ v).1 (hχ v).2
  exact standardFactors_of_characterTwistClass F ψ ν hν J J₁ z hz hJ e₁ _ _ ht hQ hb

end Langlands.BaseChange
