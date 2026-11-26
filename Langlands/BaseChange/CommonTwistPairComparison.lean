import Langlands.BaseChange.HeckeTwistCompletionEquivalences
import Langlands.BaseChange.WeakBaseChangeAuxiliaryTwist
import Langlands.BaseChange.DualSphericalSpectrumAtCompletion

/-! # Forward and dual factors after a common auxiliary twist -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Automorphic Correspondence GeneralLinear Global Global.AdelicFunctoriality
open Global.CompletionPadic Global.CuspidalPairFunctionalEquation Global.FunctionalEquationComparison
open Global.HeckeFunctionalEquation HarmonicAnalysis LocalClassField RankinSelberg Unramified
open scoped BigOperators NumberField FiniteExtension

universe u uQ uI

local instance commonTwistRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance commonTwistContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance commonTwistSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance commonTwistFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance commonTwistLocalGroup {K : Type u} [Field K] [NumberField K] {n : ℕ} {v : FinitePlace K}
    (D : LocalRealization K n v) : AddCommGroup D.Space := Submodule.addCommGroup _

private theorem invertedNormCharacterRestriction {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {I : Type uI} (χ : I → HeckeCharacter K)
    (v : FinitePlace K)
    (h : ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) :
    ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, (((χ i)⁻¹).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // (((χ i)⁻¹).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v)) := by
  intro w κ
  let val (i : I) := ((χ i).finiteComponent v).toMonoidHom
  have he (i : I) : (((χ i)⁻¹).finiteComponent v).toMonoidHom = κ ↔ val i = κ⁻¹ := by
    change (val i)⁻¹ = κ ↔ val i = κ⁻¹
    constructor <;> intro hx <;> apply MonoidHom.ext <;> intro y
    · exact inv_eq_iff_eq_inv.mp (DFunLike.congr_fun hx y)
    · exact inv_eq_iff_eq_inv.mpr (DFunLike.congr_fun hx y)
  have hinv : (κ⁻¹)⁻¹ = κ := MonoidHom.ext fun y => inv_inv (κ y)
  have hκ : IsNormTrivial (w.1.adicCompletion L) κ ↔ IsNormTrivial (w.1.adicCompletion L) κ⁻¹ :=
    ⟨fun a => a.inv, fun a => hinv ▸ a.inv⟩
  refine ⟨hκ.trans ((h w κ⁻¹).1.trans (exists_congr he).symm), fun h₀ => ?_⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight he)).trans ((h w κ⁻¹).2 (hκ.mp h₀))

section InverseTwists

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T Td Ud : CuspidalOperatorRealization K r}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (Dd : CuspidalSpectralPresentation.{u, uQ} Td)
  (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
  (hD : HasIrreducibleAdmissibleComponents D) (hDd : HasIrreducibleAdmissibleComponents Dd)
  (hQd : HasIrreducibleAdmissibleComponents Qd)
  (v : FinitePlace K) (ν χ : HeckeCharacter K)

include D hD hDd hQd in
private theorem localDualDoubleTwistEquiv
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hUd : Ud.realization.IsContragredientOf (T.heckeDeterminantTwist ν).realization) :
    letI := (padicField v).canonicalTopologicalData.topology
    let η := quasicharacterBase v ((ν⁻¹).finiteComponent v)
    let θ := quasicharacterBase v ((χ⁻¹).finiteComponent v)
    Nonempty ((twist (determinantQuasiCharacter (padicField v) r.succPNat (θ * η))
      (Dd.localComponent v).representation).Equiv
      ((Qd.heckeDeterminantTwist χ⁻¹).localComponent v).representation) := by
  intro η θ
  let := (padicField v).canonicalTopologicalData.topology
  obtain ⟨e⟩ := heckeTwistDualAtCompletionEquiv D Dd Qd hD hDd hQd v ν hTd hUd
  let a := heckeTwistAtCompletionEquiv (Dd.heckeDeterminantTwist ν⁻¹) v χ⁻¹
  let b := heckeTwistAtCompletionEquiv Qd v χ⁻¹
  exact ⟨(heckeDoubleTwistAtCompletionEquiv Dd v ν⁻¹ χ⁻¹).trans
    (a.symm.trans ((twistEquiv (determinantQuasiCharacter (padicField v) r.succPNat θ) e).trans b))⟩

end InverseTwists

section Factors

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {r : ℕ} {T Td Td' : CuspidalOperatorRealization K r} {U Ud Ud' : CuspidalOperatorRealization L r}
  {T₁ : CuspidalOperatorRealization K 0} {U₁ : CuspidalOperatorRealization L 0}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (Dd : CuspidalSpectralPresentation.{u, uQ} Td)
  (Dd' : CuspidalSpectralPresentation.{u, uQ} Td')
  (Q : CuspidalSpectralPresentation.{u, uQ} U) (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
  (Qd' : CuspidalSpectralPresentation.{u, uQ} Ud')
  (C : CuspidalSpectralPresentation.{u, uQ} T₁) (B : CuspidalSpectralPresentation.{u, uQ} U₁)
  (hD : HasIrreducibleAdmissibleComponents D) (hDd : HasIrreducibleAdmissibleComponents Dd)
  (hDd' : HasIrreducibleAdmissibleComponents Dd')
  (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)
  (hQd' : HasIrreducibleAdmissibleComponents Qd')
  (hC : HasIrreducibleAdmissibleComponents C) (hB : HasIrreducibleAdmissibleComponents B)
  (ν : HeckeCharacter K) (I : Type uI) [Fintype I] (χ : I → HeckeCharacter K)
  (cF : ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K)
    ((D.heckeDeterminantTwist ν).heckeDeterminantTwist (χ i)) C (Dd'.heckeDeterminantTwist (χ i)⁻¹) C
    ((D.heckeDeterminantTwist ν).heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)
      (D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ν hD)) hC
    (Dd'.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)⁻¹ hDd') hC)
  (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L)
    (Q.heckeDeterminantTwist (ν.normComp (L := L))) B Qd' B
    (Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (ν.normComp (L := L)) hQ) hB hQd' hB)
  (v : FinitePlace K)

/-- Compare the forward and dual finite factors of actual Hecke-twisted
cuspidal presentations, using the original spherical power relation or the
highly ramified formulas at the specified place. -/
def CommonTwistPairComparisonStatement : Prop :=
  Td.realization.IsContragredientOf T.realization →
  Ud.realization.IsContragredientOf U.realization →
  Td'.realization.IsContragredientOf (T.heckeDeterminantTwist ν).realization →
  Ud'.realization.IsContragredientOf (U.heckeDeterminantTwist (ν.normComp (L := L))).realization →
  Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
    (C.localComponent v).representation) →
  (∀ w : FinitePlacesAbove L v, Nonempty ((rankOneCharacter (1 : (padicField w.1).Carrierˣ →* ℂˣ)).Equiv
    (B.localComponent w.1).representation)) →
  (∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
    (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
    (IsNormTrivial (w.1.adicCompletion L) κ →
      Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) →
  HasCommonTwistAuxiliaryData D Dd Q Qd hD hDd hQ hQd ν v →
  (∀ z : ℂ, (∏ i, (cF i).finiteL v z) = ∏ w : FinitePlacesAbove L v, cE.finiteL w.1 z) ∧
  (∀ z : ℂ, (∏ i, (cF i).finiteDualL v z) = ∏ w : FinitePlacesAbove L v, cE.finiteDualL w.1 z) ∧
  finiteEpsilonBase Finset.univ (fun _ : I => residueCardinality v) (fun i => (cF i).epsilon v) =
    finiteEpsilonBase Finset.univ (fun w : FinitePlacesAbove L v => residueCardinality w.1)
      (fun w => cE.epsilon w.1)

set_option maxHeartbeats 3900000 in
theorem commonTwistPairComparison :
    CommonTwistPairComparisonStatement D Dd Dd' Q Qd Qd' C B hD hDd hDd' hQ hQd hQd' hC hB
      ν I χ cF cE v := by
  classical
  intro hTd hUd hTd' hUd' eC eB hres haux
  let := (padicField v).canonicalTopologicalData.topology
  let κ (i : I) := quasicharacterBase v ((χ i).finiteComponent v)
  let κd (i : I) := quasicharacterBase v (((χ i)⁻¹).finiteComponent v)
  let η := quasicharacterBase v (ν.finiteComponent v)
  let ηd := quasicharacterBase v ((ν⁻¹).finiteComponent v)
  let N := ν.normComp (L := L)
  have hinv : (ν⁻¹).normComp (L := L) = N⁻¹ := by
    apply ContinuousMonoidHom.ext
    intro x
    rfl
  let f (i : I) := forwardStandardTwistFactorChoice D _ _ C hD _ _ hC (cF i) v (κ i * η)
    ⟨heckeDoubleTwistAtCompletionEquiv D v ν (χ i)⟩ eC
  let fd (i : I) := dualStandardTwistFactorChoice Dd _ _ C hDd _ _ hC (cF i) v (κd i * ηd)
    (localDualDoubleTwistEquiv D Dd Dd' hD hDd hDd' v ν (χ i) hTd hTd') eC
  let e (w : FinitePlacesAbove L v) := forwardStandardTwistFactorChoice Q _ _ B hQ _ _ hB cE w.1
    (quasicharacterBase w.1 (N.finiteComponent w.1)) ⟨heckeTwistAtCompletionEquiv Q w.1 N⟩ (eB w)
  have edEquiv (w : FinitePlacesAbove L v) :
      Nonempty ((twist (determinantQuasiCharacter (padicField w.1) r.succPNat
        (quasicharacterBase w.1 (((ν⁻¹).normComp (L := L)).finiteComponent w.1)))
        (Qd.localComponent w.1).representation).Equiv (Qd'.localComponent w.1).representation) := by
    obtain ⟨a⟩ := heckeTwistDualAtCompletionEquiv Q Qd Qd' hQ hQd hQd' w.1 N hUd hUd'
    rw [hinv]
    exact ⟨(heckeTwistAtCompletionEquiv Qd w.1 N⁻¹).trans a⟩
  let ed (w : FinitePlacesAbove L v) := dualStandardTwistFactorChoice Qd _ _ B hQd _ _ hB cE w.1
    (quasicharacterBase w.1 (((ν⁻¹).normComp (L := L)).finiteComponent w.1)) (edEquiv w) (eB w)
  have compare := commonNormTwistAuxiliaryFactors v I κ ν _ _ f e hres
  have compareDual := commonNormTwistAuxiliaryFactors v I κd ν⁻¹ _ _ fd ed
    (invertedNormCharacterRestriction χ v hres)
  rcases haux with ⟨hv, hw, hpower⟩ | ⟨hF, hE⟩
  · let s := D.spectralSystem.eigenvalues v hv
    let sd : Eigenvalues (r + 1) := s.map fun z => z⁻¹
    have hs := hasSphericalSpectrum_padicObject D hD v hv
    have hs' (w : FinitePlacesAbove L v) :=
      hpower w ▸ hasSphericalSpectrum_padicObject Q hQ w.1 (hw w)
    have hsd := dualSphericalSpectrumAtCompletion K r T Td hTd D Dd hD hDd v hv
    have hsd' (w : FinitePlacesAbove L v) :
        HasSphericalSpectrum (padicField w.1) ((Qd.localComponent w.1).padicObject (hQd w.1).1 (hQd w.1).2)
          (sd.power (w.1.asIdeal.inertiaDeg (𝓞 K))) := by
      have h := dualSphericalSpectrumAtCompletion L r U Ud hUd Q Qd hQ hQd w.1 (hw w)
      rw [hpower w] at h
      simpa only [sd, Eigenvalues.power, Sym.map_map, Function.comp_def, inv_pow] using h
    have a := compare (Or.inl ⟨s, hs, hs'⟩)
    have b := compareDual (Or.inl ⟨sd, hsd, hsd'⟩)
    exact ⟨a.1, b.1, a.2⟩
  · let w₀ := placeAbove L v
    have hκ (i : I) : IsNormTrivial (w₀.1.adicCompletion L) (κ i).toMonoidHom :=
      (hres w₀ _).1.mpr ⟨i, rfl⟩
    have a := compare (Or.inr ⟨fun i => (hF w₀ (κ i) (hκ i)).1 (f i),
      fun w => (hE w).1 (e w)⟩)
    have hFd (i : I) : HasHighlyRamifiedStandardFactors Dd hDd v (κd i * ηd) := by
      have he : (κ i * η)⁻¹ = κd i * ηd := by
        apply ContinuousMonoidHom.ext
        intro x
        change (κ i x * η x)⁻¹ = (κ i x)⁻¹ * (η x)⁻¹
        exact mul_inv _ _
      exact he ▸ (hF w₀ (κ i) (hκ i)).2
    have hEd (w : FinitePlacesAbove L v) : HasHighlyRamifiedStandardFactors Qd hQd w.1
        (quasicharacterBase w.1 (((ν⁻¹).normComp (L := L)).finiteComponent w.1)) := by
      rw [hinv]
      exact (hE w).2
    have b := compareDual (Or.inr ⟨fun i => hFd i (fd i), fun w => hEd w (ed w)⟩)
    exact ⟨a.1, b.1, a.2⟩

end Factors

end Langlands.BaseChange
