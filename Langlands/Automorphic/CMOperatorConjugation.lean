import Langlands.Automorphic.SmoothArithmeticActions
import Langlands.Automorphic.CenterFiniteArithmeticTransport
import Langlands.Automorphic.OperatorCore

/-! # CM conjugation of the actual automorphic operator algebra -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions AdelicGLTransport

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] (n : ℕ)

local instance cmOperatorRationalGroup : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance cmOperatorContinuousGroup : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance cmOperatorFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _

@[simp] theorem finiteSmoothComplexConj_symm :
    (finiteSmoothComplexConj (K := K) n).symm = finiteSmoothComplexConj n := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply (finiteSmoothComplexConj n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    finiteSmoothComplexConj_finiteSmoothComplexConj]

theorem finiteSmoothComplexConj_finiteRightAction (d : FiniteAdelicGL K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n
        (finiteSmoothFiniteRightAction K n (CMConjugation.finiteConj K n d) f) =
      finiteSmoothFiniteRightAction K n d (finiteSmoothComplexConj n f) := by
  change finiteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv
      (finiteSmoothRightAction K n
        (AdelicGL.ofFinite K n (CMConjugation.finiteConj K n d)) f) = _
  rw [← finiteEquiv_complexConj, ← adelicEquiv_ofFinite]
  exact finiteSmoothEquiv_rightAction n _ _ f

theorem finiteSmoothComplexConj_compactRightAction (k : standardInfiniteCompact K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n
        (finiteSmoothCompactRightAction K n (CMConjugation.compactConj K n k) f) =
      finiteSmoothCompactRightAction K n k (finiteSmoothComplexConj n f) := by
  change finiteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv
      (finiteSmoothRightAction K n
        (AdelicGL.ofInfinite K n (CMConjugation.infiniteConj K n k.val)) f) = _
  rw [← infiniteEquiv_complexConj, ← adelicEquiv_ofInfinite]
  exact finiteSmoothEquiv_rightAction n _ _ f

theorem finiteSmoothComplexConj_envelopingAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n
        (finiteSmoothEnvelopingAction K n
          (ArchimedeanLieTransport.envelopingEquiv n
            (NumberField.IsCMField.complexConj K).toRingEquiv a) f) =
      finiteSmoothEnvelopingAction K n a (finiteSmoothComplexConj n f) :=
  finiteSmoothEquiv_envelopingAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv a f

/-- Conjugate an actual ambient operator by the involutive CM argument pullback. -/
def finiteSmoothCMConjugation : FiniteSmoothEnd K n ≃ₐ[ℂ] FiniteSmoothEnd K n :=
  (finiteSmoothComplexConj (K := K) n).toLinearEquiv.symm.conjAlgEquiv ℂ

@[simp] theorem finiteSmoothCMConjugation_apply (a : FiniteSmoothEnd K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothCMConjugation n a f =
      (finiteSmoothComplexConj n).symm (a (finiteSmoothComplexConj n f)) := rfl

@[simp] theorem finiteSmoothCMConjugation_finite (d : FiniteAdelicGL K n) :
    finiteSmoothCMConjugation n (finiteSmoothFiniteRightAction K n d) =
      finiteSmoothFiniteRightAction K n (CMConjugation.finiteConj K n d) := by
  apply LinearMap.ext
  intro f
  apply (finiteSmoothComplexConj n).injective
  rw [finiteSmoothCMConjugation_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteSmoothComplexConj_finiteRightAction n d f).symm

@[simp] theorem finiteSmoothCMConjugation_compact (k : standardInfiniteCompact K n) :
    finiteSmoothCMConjugation n (finiteSmoothCompactRightAction K n k) =
      finiteSmoothCompactRightAction K n (CMConjugation.compactConj K n k) := by
  apply LinearMap.ext
  intro f
  apply (finiteSmoothComplexConj n).injective
  rw [finiteSmoothCMConjugation_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteSmoothComplexConj_compactRightAction n k f).symm

@[simp] theorem finiteSmoothCMConjugation_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    finiteSmoothCMConjugation n (finiteSmoothEnvelopingAction K n a) =
      finiteSmoothEnvelopingAction K n
        (ArchimedeanLieTransport.envelopingEquiv n
          (NumberField.IsCMField.complexConj K).toRingEquiv a) := by
  apply LinearMap.ext
  intro f
  apply (finiteSmoothComplexConj n).injective
  rw [finiteSmoothCMConjugation_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteSmoothComplexConj_envelopingAction n a f).symm

@[simp] theorem finiteSmoothCMConjugation_involutive (a : FiniteSmoothEnd K n) :
    finiteSmoothCMConjugation n (finiteSmoothCMConjugation n a) = a := by
  apply LinearMap.ext
  intro f
  simp only [finiteSmoothCMConjugation_apply, finiteSmoothComplexConj_symm,
    finiteSmoothComplexConj_finiteSmoothComplexConj]

private theorem finiteSmoothCMConjugation_mem (a : FiniteSmoothEnd K n)
    (ha : a ∈ automorphicOperatorAlgebra K n) :
    finiteSmoothCMConjugation n a ∈ automorphicOperatorAlgebra K n := by
  refine Algebra.adjoin_induction
    (p := fun a _ => finiteSmoothCMConjugation n a ∈ automorphicOperatorAlgebra K n)
    ?_ ?_ ?_ ?_ ha
  · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · rw [finiteSmoothCMConjugation_finite]
      exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨_, rfl⟩))
    · rw [finiteSmoothCMConjugation_compact]
      exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨_, rfl⟩))
    · rw [finiteSmoothCMConjugation_differential]
      exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · intro c
    rw [AlgEquiv.commutes]
    exact (automorphicOperatorAlgebra K n).algebraMap_mem c
  · intro _ _ _ _ hca hcb
    rw [map_add]
    exact (automorphicOperatorAlgebra K n).add_mem hca hcb
  · intro _ _ _ _ hca hcb
    rw [map_mul]
    exact (automorphicOperatorAlgebra K n).mul_mem hca hcb

/-- The actual concrete operator algebra is preserved, with the same involution as inverse. -/
def cmOperatorConjugation :
    automorphicOperatorAlgebra K n ≃ₐ[ℂ] automorphicOperatorAlgebra K n where
  toFun a := ⟨finiteSmoothCMConjugation n a.val, finiteSmoothCMConjugation_mem n _ a.property⟩
  invFun a := ⟨finiteSmoothCMConjugation n a.val, finiteSmoothCMConjugation_mem n _ a.property⟩
  left_inv a := Subtype.ext (finiteSmoothCMConjugation_involutive n a.val)
  right_inv a := Subtype.ext (finiteSmoothCMConjugation_involutive n a.val)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  commutes' c := Subtype.ext (AlgEquiv.commutes _ c)

@[simp] theorem cmOperatorConjugation_val (a : automorphicOperatorAlgebra K n) :
    (cmOperatorConjugation n a).val = finiteSmoothCMConjugation n a.val := rfl

@[simp] theorem cmOperatorConjugation_finite (d : FiniteAdelicGL K n) :
    cmOperatorConjugation n (finiteOperator K n d) =
      finiteOperator K n (CMConjugation.finiteConj K n d) :=
  Subtype.ext (finiteSmoothCMConjugation_finite n d)

@[simp] theorem cmOperatorConjugation_compact (k : standardInfiniteCompact K n) :
    cmOperatorConjugation n (compactOperator K n k) =
      compactOperator K n (CMConjugation.compactConj K n k) :=
  Subtype.ext (finiteSmoothCMConjugation_compact n k)

@[simp] theorem cmOperatorConjugation_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    cmOperatorConjugation n (differentialOperator K n a) =
      differentialOperator K n
        (ArchimedeanLieTransport.envelopingEquiv n
          (NumberField.IsCMField.complexConj K).toRingEquiv a) :=
  Subtype.ext (finiteSmoothCMConjugation_differential n a)

@[simp] theorem cmOperatorConjugation_involutive (a : automorphicOperatorAlgebra K n) :
    cmOperatorConjugation n (cmOperatorConjugation n a) = a :=
  Subtype.ext (finiteSmoothCMConjugation_involutive n a.val)

@[simp] theorem cmOperatorConjugation_symm :
    (cmOperatorConjugation (K := K) n).symm = cmOperatorConjugation n := rfl

/-- Whole-algebra covariance on actual finite-smooth functions. -/
theorem operatorAction_complexConj (a : automorphicOperatorAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) :
    a.val (finiteSmoothComplexConj n f) =
      finiteSmoothComplexConj n ((cmOperatorConjugation n a).val f) := by
  change a.val (finiteSmoothComplexConj n f) =
    finiteSmoothComplexConj n
      ((finiteSmoothComplexConj n).symm (a.val (finiteSmoothComplexConj n f)))
  rw [ContinuousLinearEquiv.apply_symm_apply]

end Langlands.Automorphic
