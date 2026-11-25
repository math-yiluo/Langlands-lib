import Langlands.BaseChange.SphericalAuxiliaryCompletionComparison
import Langlands.BaseChange.DualSphericalSpectrumAtCompletion
import Langlands.Representation.Unramified.PrincipalSeriesDuality
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # Forward and dual standard factor comparison at spherical auxiliary places -/

noncomputable section

set_option autoImplicit false

universe u uQ uX

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.CompletionPadic Global.AdelicFunctoriality
open Global.CuspidalPairFunctionalEquation Global.FunctionalEquationComparison
open Global.HeckeFunctionalEquation Automorphic.CuspidalWhittaker
open ClassFieldTheory.Global.RelativeWeilGroup RankinSelberg Unramified
open scoped NumberField FiniteExtension

section DualData

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
variable {r t : ℕ} {T Td : CuspidalOperatorRealization K r} {T' Td' : CuspidalOperatorRealization K t}
variable {P : CuspidalSpectralPresentation.{u, uQ} T} {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
variable {P' : CuspidalSpectralPresentation.{u, uQ} T'} {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
variable {h : HasIrreducibleAdmissibleComponents P} {hd : HasIrreducibleAdmissibleComponents Pd}
variable {h' : HasIrreducibleAdmissibleComponents P'} {hd' : HasIrreducibleAdmissibleComponents Pd'}

/-- Use the original polynomial data in reversed order and choose the epsilon factors for the
new forward pair. The additive and Haar data are retained. -/
private def swapFinitePairFactorChoice {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)}
    (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') :
    FinitePairFactorChoice ψ Pd Pd' P P' hd hd' h h' :=
  let e v := exists_isAutomorphicPairEpsilonFactor (padicField v) (c.additive v) (c.measure_spec v)
    (localClass Pd hd v) (localClass Pd' hd' v)
  { additive := c.additive
    additive_spec := c.additive_spec
    measure := c.measure
    measure_spec := c.measure_spec
    lPolynomial := c.dualLPolynomial
    lPolynomial_spec := c.dualLPolynomial_spec
    dualLPolynomial := c.lPolynomial
    dualLPolynomial_spec := c.lPolynomial_spec
    epsilon v := (e v).choose
    epsilon_spec v := (e v).choose_spec }

/-- The actual local smooth dual of a trivial GL₁ component is trivial. -/
theorem trivialRankOne_of_isContragredientOf {T Td : CuspidalOperatorRealization K 0}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
    (v : FinitePlace K)
    (e : Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (P.localComponent v).representation)) :
    Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (Pd.localComponent v).representation) := by
  let F := padicField v
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  let (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
    (padicField v).canonicalGeneralLinearTopology n
  let (n : ℕ) : IsTopologicalGroup (GeneralLinear n (padicField v).Carrier) :=
    (padicField v).canonicalGeneralLinearTopologicalGroup n
  obtain ⟨a⟩ := e
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  have a₀ : (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv A.obj.representation := a
  obtain ⟨b⟩ := cuspidalContragredientLocalCompatibility K 0 T Td hTd P Pd v
    (h v).1 (h v).2 (hd v).1 (hd v).2
  have hinv : (1 : QuasiCharacter F)⁻¹ = 1 := by
    apply ContinuousMonoidHom.ext
    intro x
    exact inv_one
  have hchar : determinantQuasiCharacter F 1 (1 : QuasiCharacter F) =
      (1 : F.Carrierˣ →* ℂˣ).comp GeneralLinear.determinant := by
    ext g
    rfl
  let ec := equivOfRepresentationEq (congrArg characterRepresentation hchar)
  let e₀ := scalarCharacterSmoothDualEquiv F (1 : QuasiCharacter F)
  have e' : (smoothContragredient (characterRepresentation
      (determinantQuasiCharacter F 1 (1 : QuasiCharacter F)))).Equiv
      (characterRepresentation (determinantQuasiCharacter F 1 (1 : QuasiCharacter F))) := by
    simpa only [hinv] using e₀
  have e₁ : (smoothContragredient (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))).Equiv
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) :=
    (smoothContragredientEquiv ec).trans (e'.trans ec)
  exact ⟨e₁.symm.trans (((smoothContragredientEquiv a₀).symm).trans b.symm)⟩

end DualData

private theorem inverseNormCharacterRestriction {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {X : Type uX} (χ : X → HeckeCharacter K)
    (v : FinitePlace K)
    (h : ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ x, ((χ x).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {x // ((χ x).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) :
    ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ x, (((χ x)⁻¹).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {x // (((χ x)⁻¹).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v)) := by
  intro w κ
  let val (x : X) := ((χ x).finiteComponent v).toMonoidHom
  have he (x : X) : (((χ x)⁻¹).finiteComponent v).toMonoidHom = κ ↔
      ((χ x).finiteComponent v).toMonoidHom = κ⁻¹ := by
    change (val x)⁻¹ = κ ↔ val x = κ⁻¹
    constructor <;> intro hx <;> apply MonoidHom.ext <;> intro y
    · exact inv_eq_iff_eq_inv.mp (DFunLike.congr_fun hx y)
    · exact inv_eq_iff_eq_inv.mpr (DFunLike.congr_fun hx y)
  have hinv : (κ⁻¹)⁻¹ = κ := MonoidHom.ext fun y => inv_inv (κ y)
  have hκ : IsNormTrivial (w.1.adicCompletion L) κ ↔ IsNormTrivial (w.1.adicCompletion L) κ⁻¹ :=
    ⟨fun a => a.inv, fun a => hinv ▸ a.inv⟩
  refine ⟨hκ.trans ((h w κ⁻¹).1.trans (exists_congr he).symm), fun h₀ => ?_⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight he)).trans ((h w κ⁻¹).2 (hκ.mp h₀))

/-- Compare both finite Euler products and the positive forward epsilon bases at a place with
actual spherical local base change. The lower dual twists use the inverse Hecke characters. -/
def SphericalAuxiliaryPairComparisonStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] [CompactSpace (AdeleQuotient K)]
    [CompactSpace (AdeleQuotient L)] (r : ℕ) (X : Type uX) [Fintype X]
    (χ : X → HeckeCharacter K) (T Td : CuspidalOperatorRealization K r)
    (_hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (h : HasIrreducibleAdmissibleComponents P)
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td) (hd : HasIrreducibleAdmissibleComponents Pd)
    (U Ud : CuspidalOperatorRealization L r) (_hUd : Ud.realization.IsContragredientOf U.realization)
    (Q : CuspidalSpectralPresentation.{u, uQ} U) (hQ : HasIrreducibleAdmissibleComponents Q)
    (Qd : CuspidalSpectralPresentation.{u, uQ} Ud) (hQd : HasIrreducibleAdmissibleComponents Qd)
    (T₁ Td₁ : CuspidalOperatorRealization K 0) (_hTd₁ : Td₁.realization.IsContragredientOf T₁.realization)
    (P₁ : CuspidalSpectralPresentation.{u, uQ} T₁) (h₁ : HasIrreducibleAdmissibleComponents P₁)
    (Pd₁ : CuspidalSpectralPresentation.{u, uQ} Td₁) (hd₁ : HasIrreducibleAdmissibleComponents Pd₁)
    (U₁ Ud₁ : CuspidalOperatorRealization L 0) (_hUd₁ : Ud₁.realization.IsContragredientOf U₁.realization)
    (Q₁ : CuspidalSpectralPresentation.{u, uQ} U₁) (hQ₁ : HasIrreducibleAdmissibleComponents Q₁)
    (Qd₁ : CuspidalSpectralPresentation.{u, uQ} Ud₁) (hQd₁ : HasIrreducibleAdmissibleComponents Qd₁)
    (cF : ∀ x, FinitePairFactorChoice (standardGlobalAdditiveCharacter K)
      (P.heckeDeterminantTwist (χ x)) P₁ (Pd.heckeDeterminantTwist (χ x)⁻¹) Pd₁
      (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ x) h) h₁
      (Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ x)⁻¹ hd) hd₁)
    (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L) Q Q₁ Qd Qd₁ hQ hQ₁ hQd hQd₁)
    (v : FinitePlace K) (hv : v ∉ P.exceptional) (hw : ∀ w : FinitePlacesAbove L v, w.1 ∉ Q.exceptional),
    (∀ w : FinitePlacesAbove L v, Q.spectralSystem.eigenvalues w.1 (hw w) =
      (P.spectralSystem.eigenvalues v hv).power (w.1.asIdeal.inertiaDeg (𝓞 K))) →
    Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (P₁.localComponent v).representation) →
    (∀ w : FinitePlacesAbove L v,
      Nonempty ((rankOneCharacter (1 : (padicField w.1).Carrierˣ →* ℂˣ)).Equiv
        (Q₁.localComponent w.1).representation)) →
    (∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ x, ((χ x).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {x // ((χ x).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) →
    (∀ z : ℂ, (∏ x, (cF x).finiteL v z) = ∏ w : FinitePlacesAbove L v, cE.finiteL w.1 z) ∧
    (∀ z : ℂ, (∏ x, (cF x).finiteDualL v z) = ∏ w : FinitePlacesAbove L v, cE.finiteDualL w.1 z) ∧
    finiteEpsilonBase Finset.univ (fun _ : X => residueCardinality v) (fun x => (cF x).epsilon v) =
      finiteEpsilonBase Finset.univ (fun w : FinitePlacesAbove L v => residueCardinality w.1)
        (fun w => cE.epsilon w.1)

set_option maxHeartbeats 1800000 in
/-- Apply the same local norm-character comparison to the original and dual choices.
Inversion preserves the local multiplicities and commutes with Satake powers. -/
theorem sphericalAuxiliaryPairComparison : SphericalAuxiliaryPairComparisonStatement.{u, uQ, uX} := by
  classical
  intro K L _ _ _ _ _ _ _ _ _ r X _ χ T Td hTd P h Pd hd U Ud hUd Q hQ Qd hQd
    T₁ Td₁ hTd₁ P₁ h₁ Pd₁ hd₁ U₁ Ud₁ hUd₁ Q₁ hQ₁ Qd₁ hQd₁ cF cE v hv hw he e₁ e'₁ hres
  let s := P.spectralSystem.eigenvalues v hv
  have hs := hasSphericalSpectrum_padicObject P h v hv
  have hs' (w : FinitePlacesAbove L v) := he w ▸ hasSphericalSpectrum_padicObject Q hQ w.1 (hw w)
  have hf := sphericalAuxiliaryCompletionComparison K L r X χ T P h U Q hQ
    T₁ Td₁ P₁ Pd₁ h₁ hd₁ U₁ Ud₁ Q₁ Qd₁ hQ₁ hQd₁ _ _ _ Ud Qd hQd cF cE
    v s hs hs' e₁ e'₁ hres
  let sd : Eigenvalues (r + 1) := s.map fun z => z⁻¹
  have hsd := dualSphericalSpectrumAtCompletion K r T Td hTd P Pd h hd v hv
  have hsd' (w : FinitePlacesAbove L v) :
      HasSphericalSpectrum (padicField w.1) ((Qd.localComponent w.1).padicObject (hQd w.1).1 (hQd w.1).2)
        (sd.power (w.1.asIdeal.inertiaDeg (𝓞 K))) := by
    have h := dualSphericalSpectrumAtCompletion L r U Ud hUd Q Qd hQ hQd w.1 (hw w)
    rw [he w] at h
    simpa only [sd, Eigenvalues.power, Sym.map_map, Function.comp_def, inv_pow] using h
  have hd₀ := sphericalAuxiliaryCompletionComparison K L r X (fun x => (χ x)⁻¹) Td Pd hd Ud Qd hQd
    Td₁ T₁ Pd₁ P₁ hd₁ h₁ Ud₁ U₁ Qd₁ Q₁ hQd₁ hQ₁ _ _ _ U Q hQ
    (fun x => swapFinitePairFactorChoice (cF x)) (swapFinitePairFactorChoice cE)
    v sd hsd hsd'
    (trivialRankOne_of_isContragredientOf hTd₁ P₁ Pd₁ h₁ hd₁ v e₁)
    (fun w => trivialRankOne_of_isContragredientOf hUd₁ Q₁ Qd₁ hQ₁ hQd₁ w.1 (e'₁ w))
    (inverseNormCharacterRestriction χ v hres)
  exact ⟨hf.1, hd₀.1, hf.2⟩

end Langlands.BaseChange
