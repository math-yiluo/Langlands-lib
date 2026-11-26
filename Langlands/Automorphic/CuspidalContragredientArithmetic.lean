import Langlands.Automorphic.CuspidalInvariantPairingCriterion
import Langlands.Automorphic.OperatorArithmeticTransportClasses

/-! # Arithmetic transport of actual cuspidal contragredients -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uK uL uF

namespace Langlands.Automorphic.CuspidalOperatorRealization

open Langlands.Global

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]


local instance arithmeticDualRationalGroup {H : Type*} [Field H] [NumberField H] (n : ℕ) : AddCommGroup (RationalInvariantFunctions H n) :=
  Submodule.addCommGroup _
local instance arithmeticDualContinuousGroup {H : Type*} [Field H] [NumberField H] (n : ℕ) : AddCommGroup (ContinuousRationalFunctions H n) :=
  Submodule.addCommGroup _
local instance arithmeticDualSmoothGroup {H : Type*} [Field H] [NumberField H] (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions H n) :=
  Submodule.addCommGroup _
local instance arithmeticDualFormsGroup {H : Type*} [Field H] [NumberField H] (n : ℕ) : AddCommGroup (AutomorphicForms H n) :=
  Submodule.addCommGroup _
local instance arithmeticDualStableGroup {H : Type*} [Field H] [NumberField H] (n : ℕ) : AddCommGroup (StableAutomorphicFunctions H n) :=
  Submodule.addCommGroup _
local instance arithmeticDualSpaceGroup {H : Type*} [Field H] [NumberField H] (n : ℕ) (S : OperatorRealization H n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Arithmetic pullback carries a cuspidal contragredient to a contragredient of
the pulled-back cuspidal realization. -/
def CuspidalContragredientArithmeticStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) {r : ℕ} (S T : CuspidalOperatorRealization L r),
    T.realization.IsContragredientOf S.realization →
    (T.arithmeticComap e).realization.IsContragredientOf (S.arithmeticComap e).realization

set_option maxHeartbeats 2500000 in
theorem cuspidalContragredientArithmetic : CuspidalContragredientArithmeticStatement.{uK,uL} := by
  intro K L _ _ _ _ _ _ e r S T ⟨B, hB⟩
  let a := (S.realization.arithmeticComapEquiv e).toLinearEquiv
  let b := (T.realization.arithmeticComapEquiv e).toLinearEquiv
  let C := B.compl₁₂ a.symm.toLinearMap b.symm.toLinearMap
  have hzero : B ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : T.Space)
    apply hx
    apply hB.2.2.1
    apply LinearMap.ext
    intro y
    simp only [LinearMap.flip_apply, h, LinearMap.zero_apply]
  refine isContragredientOf_of_nonzero_invariant (B := C) ⟨?_, ?_, ?_⟩ ?_
  · intro g y x
    change B ((S.realization.arithmeticComapEquiv e).symm
        ((S.realization.arithmeticComap e).finiteRepresentation g y))
      ((T.realization.arithmeticComapEquiv e).symm
        ((T.realization.arithmeticComap e).finiteRepresentation g x)) = B (a.symm y) (b.symm x)
    exact (congrArg₂ (fun y x => B y x)
      (S.realization.arithmeticComapEquiv_symm_finite e g y)
      (T.realization.arithmeticComapEquiv_symm_finite e g x)).trans (hB.1.1 _ _ _)
  · intro k y x
    change B ((S.realization.arithmeticComapEquiv e).symm
        ((S.realization.arithmeticComap e).compactRepresentation k y))
      ((T.realization.arithmeticComapEquiv e).symm
        ((T.realization.arithmeticComap e).compactRepresentation k x)) = B (a.symm y) (b.symm x)
    exact (congrArg₂ (fun y x => B y x)
      (S.realization.arithmeticComapEquiv_symm_compact e k y)
      (T.realization.arithmeticComapEquiv_symm_compact e k x)).trans (hB.1.2.1 _ _ _)
  · intro X y x
    change B ((S.realization.arithmeticComapEquiv e).symm
        ((S.realization.arithmeticComap e).lieAction X y)) (b.symm x) +
      B (a.symm y) ((T.realization.arithmeticComapEquiv e).symm
        ((T.realization.arithmeticComap e).lieAction X x)) = 0
    let Y := ArchimedeanLieTransport.realLieEquiv (r + 1) e X
    let z := ArchimedeanGL.envelopingGenerator K (r + 1)
      (ArchimedeanGL.complexify K (r + 1) X)
    let z' := ArchimedeanGL.envelopingGenerator L (r + 1)
      (ArchimedeanGL.complexify L (r + 1) Y)
    have hz : ArchimedeanLieTransport.envelopingEquiv (r + 1) e z = z' :=
      ArchimedeanLieTransport.envelopingEquiv_generator _ e _
    have hs := (S.realization.arithmeticComapEquiv_symm_differential e z y).trans
      (congrArg (fun q => S.realization.envelopingAction q (a.symm y)) hz)
    have ht := (T.realization.arithmeticComapEquiv_symm_differential e z x).trans
      (congrArg (fun q => T.realization.envelopingAction q (b.symm x)) hz)
    exact (congrArg₂ (fun y' x' => B y' (b.symm x) + B (a.symm y) x') hs ht).trans
      (hB.1.2.2 Y (a.symm y) (b.symm x))
  · intro h
    apply hzero
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    have h₁ := LinearMap.congr_fun (LinearMap.congr_fun h (a y)) (b x)
    change B (a.symm (a y)) (b.symm (b x)) = 0 at h₁
    simpa only [LinearEquiv.symm_apply_apply, LinearMap.zero_apply] using h₁

omit [CompactSpace (AdeleQuotient L)] in
/-- Contragredients of two arithmetic conjugate cuspidal realizations are
conjugate by the same Galois element. -/
theorem IsoClass.isGaloisConjugate_contragredient {F : Type uF} [Field F] [Algebra F K]
    {r : ℕ} {S T Sd Td : CuspidalOperatorRealization K r}
    (σ : K ≃ₐ[F] K) (h : S.isoClass.IsGaloisConjugate σ T.isoClass)
    (hSd : Sd.realization.IsContragredientOf S.realization)
    (hTd : Td.realization.IsContragredientOf T.realization) :
    Sd.isoClass.IsGaloisConjugate σ Td.isoClass := by
  let e := σ.toRingEquiv.symm
  have hclass : T.isoClass = (S.arithmeticComap e).isoClass :=
    (IsoClass.isGaloisConjugate_iff σ _ _).mp h
  obtain ⟨g⟩ := (isoClass_eq_iff (S.arithmeticComap e) T).mp hclass.symm
  have htrans := cuspidalContragredientArithmetic K K e S Sd hSd
  have h' : (Sd.arithmeticComap e).realization.IsContragredientOf T.realization :=
    htrans.of_equivalence_left g
  apply (IsoClass.isGaloisConjugate_iff σ _ _).mpr
  exact (isoClass_eq_iff Td (Sd.arithmeticComap e)).mpr (hTd.nonempty_equivalence h')

end Langlands.Automorphic.CuspidalOperatorRealization
