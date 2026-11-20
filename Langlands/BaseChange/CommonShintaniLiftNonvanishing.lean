import Langlands.BaseChange.TwistedCharacter
import Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison
import Langlands.Representation.Classification.GenericEllipticCharacter
import Langlands.Representation.Smooth.Schur.Proof

/-! # Character nonvanishing in a common Shintani fibre -/

noncomputable section

universe uF uE uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open JacquetLanglands

section Intertwiners

variable {F : Type uF} [CommRing F] {E : Type uE} [CommRing E] [Algebra F E]
  [TopologicalSpace E] {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : E ≃ₐ[F] E} {P : Representation ℂ (GeneralLinear n E) W}

/-- Two sigma-intertwiners of an irreducible admissible representation
differ by a nonzero scalar. -/
theorem SigmaIntertwiner.exists_smul_toLinearMap
    (A A' : SigmaIntertwiner σ n P) (hP : IsAdmissible P) (hI : P.IsIrreducible) :
    ∃ a : ℂ, a ≠ 0 ∧ A'.toLinearMap = a • A.toLinearMap := by
  let C := (A'.trans A.symm).toIntertwiningMap
  obtain ⟨a, ha, _⟩ := admissibleSchur_scalarEndomorphism P hP hI C
  have hEq : A'.toLinearMap = a • A.toLinearMap := by
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f : P.IntertwiningMap P => f x) ha
    change A.symm (A' x) = a • x at hx
    change A' x = a • A x
    calc
      A' x = A (A.symm (A' x)) := (A.toLinearEquiv.apply_symm_apply _).symm
      _ = A (a • x) := congrArg A.toLinearEquiv hx
      _ = a • A x := A.toLinearEquiv.map_smul a x
  refine ⟨a, ?_, hEq⟩
  intro ha0
  let := hI
  let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n E)) P.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  apply hx
  apply A'.toLinearEquiv.injective
  change A'.toLinearMap x = A'.toLinearMap 0
  simp only [hEq, ha0, zero_smul, LinearMap.zero_apply]

end Intertwiners

/-- Nonzero character values at associated regular elements transfer between
two actions with the same irreducible upstairs Shintani lift. -/
def CommonShintaniLiftNonvanishingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (E : Type uE) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    (σ : E ≃ₐ[F] E) (d n : ℕ)
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
    (π' : Representation ℂ (GeneralLinear n F) V') (hπ' : IsAdmissible π')
    (P : Representation ℂ (GeneralLinear n E) W) (hP : IsAdmissible P),
    P.IsIrreducible →
    ∀ (A A' : SigmaIntertwiner σ n P) (c c' : ℂ),
      IsShintaniLift σ d π hπ P hP A c → IsShintaniLift σ d π' hπ' P hP A' c' →
      ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F),
        IsNormAssociated σ d δ γ → IsRegularSemisimple γ →
        (∃ b : ℂ, b ≠ 0 ∧ HasCharacterValue π hπ γ b) →
        ∃ b' : ℂ, b' ≠ 0 ∧ HasCharacterValue π' hπ' γ b'

/-- Compare the two actual local twisted values after the scalar change of
intertwiner supplied by Schur's lemma. -/
theorem commonShintaniLiftNonvanishing : CommonShintaniLiftNonvanishingStatement := by
  intro F _ _ _ E _ _ _ _ σ d n _ _ _ _ _ _ V _ _ V' _ _ W _ _
    π hπ π' hπ' P hP hI A A' c c' hLift hLift' δ γ hAssoc hReg
  rintro ⟨b, hb, hValue⟩
  obtain ⟨a, ha, hValueP⟩ := hLift.2 δ γ hAssoc hReg
  obtain ⟨a', ha', hValueP'⟩ := hLift'.2 δ γ hAssoc hReg
  obtain ⟨s, hs, hA⟩ := A.exists_smul_toLinearMap A' hP hI
  have hScaled := hValueP.smul s
  rw [← hA, ha.unique hValue] at hScaled
  refine ⟨a', ?_, ha'⟩
  intro hzero
  rw [hzero, mul_zero] at hValueP'
  exact (mul_ne_zero hs (mul_ne_zero hLift.1 hb)) (hScaled.unique hValueP')

open HarmonicAnalysis in
/-- A generic p-adic member of a common Shintani fibre is essentially
square-integrable when the reference character is nonzero at an elliptic norm. -/
theorem padicEssentiallySquareIntegrable_of_commonShintaniLift
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {E : Type uE} [CommRing E] [Algebra F.Carrier E] [TopologicalSpace E] [IsTopologicalRing E]
    (σ : E ≃ₐ[F.Carrier] E) (d r : ℕ)
    [T2Space (GeneralLinear (r + 1) E)] [LocallyCompactSpace (GeneralLinear (r + 1) E)]
    [TotallyDisconnectedSpace (GeneralLinear (r + 1) E)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (π' : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (P : Representation ℂ (GeneralLinear (r + 1) E) W) (hP : IsAdmissible P)
    (hI : P.IsIrreducible) :
    let := T.topology
    let := T.valuativeRel
    have := T.localField
    have := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
    have := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
    have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (hπ : IsAdmissible π)
      (hπ' : Whittaker.IsGeneric ψ r π')
      (A A' : SigmaIntertwiner σ (r + 1) P) (c c' : ℂ),
      IsShintaniLift σ d π hπ P hP A c →
      IsShintaniLift σ d π' hπ'.2.1 P hP A' c' →
      ∀ (δ : GeneralLinear (r + 1) E) (γ : GeneralLinear (r + 1) F.Carrier),
        IsNormAssociated σ d δ γ → IsRegularElliptic γ →
        (∃ b : ℂ, b ≠ 0 ∧ HasCharacterValue π hπ γ b) →
        IsEssentiallySquareIntegrable π' := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
  dsimp only
  intro ψ hπ hπ' A A' c c' hLift hLift' δ γ hAssoc hEll hValue
  obtain ⟨b, hb, hValue'⟩ := commonShintaniLiftNonvanishing F.Carrier E σ d (r + 1)
    V V' W π hπ π' hπ'.2.1 P hP hI A A' c c' hLift hLift' δ γ hAssoc hEll.1 hValue
  apply (isEssentiallySquareIntegrable_iff_padic T π').mpr
  by_contra h
  exact hb (hValue'.unique (padicGenericEllipticCharacterVanishing
    p F T r ψ V' π' hπ' h γ hEll))

end Langlands.BaseChange
