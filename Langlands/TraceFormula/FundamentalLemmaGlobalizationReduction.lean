import Langlands.BaseChange.ConcordanceLocallyConstantOfProfiles
import Langlands.BaseChange.EllipticNonNormVanishingReduction
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.FundamentalLemmaBlockReduction
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Langlands.TraceFormula.RationalNormPairLocalConstancy

/-! # From comparison at rational norm pairs to the regular elliptic fundamental lemma -/

noncomputable section

namespace Langlands.TraceFormula

open BaseChange Correspondence Global HarmonicAnalysis JacquetLanglands
open MeasureTheory _root_.Topology Unramified
open scoped NumberField TensorProduct

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace

local instance {K L : Type} [Field K] [Field L] [NumberField K] [Algebra K L]
    (w : FinitePlace K) :
    Algebra (FiniteCompletion K w) (LocalBaseChangeAlgebra K L (.inr w)) :=
  LocalBaseChangeAlgebra.algebra K L (.inr w)

set_option hygiene false in
local notation "F₀" => FiniteCompletion K v₀

set_option hygiene false in
local notation "E₀" => LocalBaseChangeAlgebra K L (.inr v₀)

set_option hygiene false in
local notation "upperAt" => fun (w : FinitePlace K) (x : GeneralLinear (r + 1) L) =>
  Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L (.inr w)).toRingHom x

set_option hygiene false in
local notation "lowerAt" => fun (w : FinitePlace K) (x : GeneralLinear (r + 1) K) =>
  Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K w)) x

/-- Rational comparison with finitely many open auxiliary conditions.
At the distinguished place the chosen center of the neighborhood is the
given local elliptic associated pair. -/
def RationalSphericalConcordanceNearEllipticStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex →
    ∀ (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
      IsUnramifiedBaseChangeHom F E l r b → ∀ φ : SphericalHeckeAlgebra E r,
    ∀ (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] (σK : L ≃ₐ[K] L),
      IsCyclicAlgebra σK l →
      (∀ w : NumberField.InfinitePlace K, IsCyclicShiftSplit K L w.Completion σK l) →
      (∀ (S : Finset (FinitePlace K)) (N : ℕ),
        ∃ w : FinitePlace K, w ∉ S ∧ N ≤ Ideal.absNorm w.asIdeal ∧
          IsCyclicShiftSplit K L (FiniteCompletion K w) σK l) →
      (∀ (S : Finset (FinitePlace K)) (N : ℕ),
        ∃ w : FinitePlace K, w ∉ S ∧ N ≤ Ideal.absNorm w.asIdeal ∧
          (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal).IsPrime) →
    ∀ (v₀ : FinitePlace K) (eF : F₀ ≃+* F.Carrier) (eE : E₀ ≃+* E.Carrier)
      (heF : Continuous eF) (heF' : Continuous eF.symm)
      (heE : Continuous eE) (heE' : Continuous eE.symm),
      (∀ a : F₀, eE (algebraMap F₀ E₀ a) = algebraMap F.Carrier E.Carrier (eF a)) →
      (∀ a : E₀, eE (localGalois K L σK (.inr v₀) a) = σ (eE a)) →
    ∀ (δ₀ : GeneralLinear (r + 1) E₀) (γ₀ : GeneralLinear (r + 1) F₀),
      IsNormAssociated (localGalois K L σK (.inr v₀)) l δ₀ γ₀ → IsRegularElliptic γ₀ →
    ∃ (S : Finset (FinitePlace K)) (hv₀ : v₀ ∈ S)
      (δs : ∀ w : S, GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr w.val)))
      (γs : ∀ w : S, GeneralLinear (r + 1) (FiniteCompletion K w.val))
      (U : ∀ w : S, Set (GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr w.val))))
      (V : ∀ w : S, Set (GeneralLinear (r + 1) (FiniteCompletion K w.val))),
      δs ⟨v₀, hv₀⟩ = δ₀ ∧ γs ⟨v₀, hv₀⟩ = γ₀ ∧
      (∀ w, IsNormAssociated (localGalois K L σK (.inr w.val)) l (δs w) (γs w)) ∧
      (∀ w, IsRegularSemisimple (γs w)) ∧
      (∀ w, U w ∈ nhds (δs w)) ∧ (∀ w, V w ∈ nhds (γs w)) ∧
      ∀ (δ : GeneralLinear (r + 1) L) (γ : GeneralLinear (r + 1) K),
        IsNormAssociated σK l δ γ → IsRegularSemisimple γ →
        (∀ w : S, upperAt w.val δ ∈ U w ∧ lowerAt w.val γ ∈ V w) →
        ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ)
          (generalLinearRingEquiv eE heE heE' (upperAt v₀ δ))
          (generalLinearRingEquiv eF heF heF' (lowerAt v₀ γ))

/-- The characteristic-zero globalization, exact regular orbital profiles,
rational comparison under open auxiliary conditions, and the elliptic
off-norm inputs imply the regular elliptic fundamental lemma. -/
def FundamentalLemmaGlobalizationReductionStatement : Prop :=
  CyclicFieldGlobalizationStatement.{u,v} →
  RegularTransferProfileExistenceStatement.{u,v} →
  RationalSphericalConcordanceNearEllipticStatement.{u,v} →
  EllipticNormCriterionStatement.{u,v} →
  SatakeCharacterStatement.{u} → SatakeCharacterStatement.{v} →
  RegularEllipticFundamentalLemmaStatement.{u,v}

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 3500 in
theorem fundamentalLemmaGlobalizationReduction :
    FundamentalLemmaGlobalizationReductionStatement.{u,v} := by
  intro hGlobal hProfiles hRational hCriterion hSatakeF hSatakeE
    p _ F E _ _ σ l r hσ hUnram b hb φ γ hEll
  refine ⟨fun hNot μγ _ _ νγ _ =>
    ellipticNonNormVanishingReduction hCriterion hSatakeF hSatakeE p F E σ l r hσ hUnram b hb
      φ γ hEll hNot νγ, ?_⟩
  intro δ hAssoc
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsModuleTopology F.Carrier E.Carrier := isModuleTopology_padic_extension F E
  have hL := concordanceLocallyConstantOfProfiles hProfiles F.Carrier E.Carrier σ l (r + 1) hσ
    (sphericalHaar F r) (sphericalHaar E r) φ.val (b φ).val
  obtain ⟨K, L, fieldK, fieldL, nfK, nfL, algKL, σK, hσK, hInfty,
    ⟨v₀, eF, eEraw, heF, heF', hScalar, hTwist, heEraw, heEraw'⟩, hSplit, hInert⟩ :=
    hGlobal F.Carrier E.Carrier σ l hσ (Field.toIsField E.Carrier)
  let : FiniteDimensional K L := hσK.1
  let n := r + 1
  let eE : LocalBaseChangeAlgebra K L (.inr v₀) ≃+* E.Carrier := eEraw
  have heE : Continuous eE := heEraw
  have heE' : Continuous eE.symm := heEraw'
  let κF := generalLinearRingEquiv (n := n) eF heF heF'
  let κE := generalLinearRingEquiv (n := n) eE heE heE'
  let δ₀ := κE.symm δ
  let γ₀ := κF.symm γ
  have hδ₀γ₀ : IsNormAssociated (localGalois K L σK (.inr v₀)) l δ₀ γ₀ := by
    apply (generalLinearRingEquiv_isNormAssociated_iff eF eE heF heF' heE heE' hScalar hTwist δ₀ γ₀).1
    change IsNormAssociated σ l (κE (κE.symm δ)) (κF (κF.symm γ))
    simpa using hAssoc
  have hEll₀ : IsRegularElliptic γ₀ := by
    apply (generalLinearRingEquiv_isRegularElliptic_iff eF heF heF' γ₀).1
    change IsRegularElliptic (κF (κF.symm γ))
    simpa using hEll
  obtain ⟨S, hv₀, δs, γs, U, V, hδs, hγs, hAssocS, hRegS, hU, hV, hConcord⟩ :=
    hRational p F E σ l r hσ hUnram b hb φ K L σK hσK hInfty hSplit hInert
      v₀ eF eE heF heF' heE heE' hScalar hTwist δ₀ γ₀ hδ₀γ₀ hEll₀
  let P (d : GeneralLinear n E.Carrier) (g : GeneralLinear n F.Carrier) :=
    ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ) d g
  obtain ⟨d, g, hdg, hg, hmem, hIff⟩ :=
    rationalNormPairLocalConstancy K L σK l n hσK S ⟨v₀, hv₀⟩ δs γs hAssocS hRegS
      F.Carrier E.Carrier σ hσ eF eE heF heF' heE heE' hScalar hTwist P hL U V hU hV
  have h := hIff.mp (hConcord d g hdg hg hmem)
  change P (κE (δs ⟨v₀, hv₀⟩)) (κF (γs ⟨v₀, hv₀⟩)) at h
  rw [hδs, hγs] at h
  change P (κE (κE.symm δ)) (κF (κF.symm γ)) at h
  simpa using h

end Langlands.TraceFormula
