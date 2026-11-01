import Langlands.Automorphic.OperatorSubquotientDeterminantAction
import Langlands.Global.HeckeCharacterTransport

/-! # CM conjugation and determinant transport of actual operator quotients -/

noncomputable section
universe uK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K]

/-- CM pullback of the actual determinant character fixes its complex values. -/
theorem adelicDeterminant_complexConj (χ : HeckeCharacter K) (n : ℕ)
    (g : AdelicGL K n) :
    χ.complexConj.adelicDeterminant n g =
      χ.adelicDeterminant n (CMConjugation.adelicConj K n g) := by
  change χ.onIdeles
      (AdelicFunctoriality.ideleEquiv (NumberField.IsCMField.complexConj K).toRingEquiv
        (AdelicGL.determinant K n g)) =
    χ.onIdeles (AdelicGL.determinant K n (CMConjugation.adelicConj K n g))
  have h := AdelicGLTransport.determinant_adelicEquiv n
    (NumberField.IsCMField.complexConj K).toRingEquiv g
  rw [AdelicGLTransport.adelicEquiv_complexConj] at h
  exact congrArg χ.onIdeles h.symm

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance quotientCMDetRationalGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMDetContinuousGroup : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMDetSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMDetFormGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance quotientCMDetStableGroup : AddCommGroup (StableAutomorphicFunctions K n) :=
  Submodule.addCommGroup _
local instance quotientCMDetRealizationGroup (S : OperatorRealization K n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace FiniteSmoothRationalFunctions

/-- Actual CM argument pullback commutes with multiplication by the pulled-back character. -/
theorem finiteOrderDeterminantMultiplier_complexConj
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n (finiteOrderDeterminantMultiplier n χ hχ f) =
      finiteOrderDeterminantMultiplier n χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)
        (finiteSmoothComplexConj n f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change evaluate K n (finiteSmoothComplexConj n
      (finiteOrderDeterminantMultiplier n χ hχ f)).val g =
    evaluate K n (finiteOrderDeterminantMultiplier n χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)
      (finiteSmoothComplexConj n f)).val g
  rw [evaluate_finiteSmoothComplexConj, evaluate_finiteOrderDeterminantMultiplier,
    evaluate_finiteOrderDeterminantMultiplier, evaluate_finiteSmoothComplexConj,
    HeckeCharacter.adelicDeterminant_complexConj]

end FiniteSmoothRationalFunctions

/-- The two mixed conjugations agree on every actual concrete operator. -/
theorem determinantOperatorConjugation_cmOperatorConjugation
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder)
    (a : automorphicOperatorAlgebra K n) :
    determinantOperatorConjugation n χ hχ (cmOperatorConjugation n a) =
      cmOperatorConjugation n (determinantOperatorConjugation n χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ) a) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  let M := FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ
  let J := finiteSmoothComplexConj (K := K) n
  let hχC := (HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ
  let MC := FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ.complexConj hχC
  apply M.injective
  apply J.injective
  calc
    J (M ((determinantOperatorConjugation n χ hχ (cmOperatorConjugation n a)).val f)) =
        J ((cmOperatorConjugation n a).val (M f)) :=
      congrArg J (operatorAction_determinantMultiplier n χ hχ (cmOperatorConjugation n a) f).symm
    _ = a.val (J (M f)) := (operatorAction_complexConj n a (M f)).symm
    _ = a.val (MC (J f)) := congrArg a.val
      (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_complexConj χ hχ f)
    _ = MC ((determinantOperatorConjugation n χ.complexConj hχC a).val (J f)) :=
      operatorAction_determinantMultiplier n χ.complexConj hχC a (J f)
    _ = MC (J ((cmOperatorConjugation n
        (determinantOperatorConjugation n χ.complexConj hχC a)).val f)) :=
      congrArg MC (operatorAction_complexConj n
        (determinantOperatorConjugation n χ.complexConj hχC a) f)
    _ = J (M ((cmOperatorConjugation n
        (determinantOperatorConjugation n χ.complexConj hχC a)).val f)) :=
      (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_complexConj χ hχ _).symm

namespace OperatorSubquotient

/-- Compare the two actual mixed quotients by an equivalence of their entire operator actions. -/
def determinantTwistComplexConjEquiv (Q : OperatorSubquotient K n)
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) :
    (Q.determinantTwist χ hχ).complexConj.Equivalence
      (Q.complexConj.determinantTwist χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)) :=
  sameConjugationQuotientEquiv Q.representation
    (Q.determinantTwist χ hχ).complexConj.representation
    (Q.complexConj.determinantTwist χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)).representation
    (fun a => determinantOperatorConjugation n χ hχ (cmOperatorConjugation n a))
    ((Q.determinantTwistEquiv χ hχ).trans (Q.determinantTwist χ hχ).complexConjEquiv)
    (Q.complexConjEquiv.trans (Q.complexConj.determinantTwistEquiv χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)))
    (composedConjugationQuotientCovariance Q.representation (Q.determinantTwist χ hχ).representation
      (Q.determinantTwist χ hχ).complexConj.representation
      (determinantOperatorConjugation n χ hχ) (cmOperatorConjugation n)
      (fun a => determinantOperatorConjugation n χ hχ (cmOperatorConjugation n a))
      (Q.determinantTwistEquiv χ hχ) (Q.determinantTwist χ hχ).complexConjEquiv
      (Q.determinantTwistEquiv_operatorAction χ hχ)
      (Q.determinantTwist χ hχ).complexConjEquiv_operatorAction (fun _ => rfl))
    (composedConjugationQuotientCovariance Q.representation Q.complexConj.representation
      (Q.complexConj.determinantTwist χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)).representation
      (cmOperatorConjugation n)
      (determinantOperatorConjugation n χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ))
      (fun a => determinantOperatorConjugation n χ hχ (cmOperatorConjugation n a))
      Q.complexConjEquiv
      (Q.complexConj.determinantTwistEquiv χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ))
      Q.complexConjEquiv_operatorAction
      (Q.complexConj.determinantTwistEquiv_operatorAction χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ))
      (determinantOperatorConjugation_cmOperatorConjugation χ hχ))

@[simp] theorem determinantTwistComplexConjEquiv_apply (Q : OperatorSubquotient K n)
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder)
    (f : (Q.determinantTwist χ hχ).complexConj.Space) :
    Q.determinantTwistComplexConjEquiv χ hχ f =
      Q.complexConj.determinantTwistEquiv χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)
        (Q.complexConjEquiv ((Q.determinantTwistEquiv χ hχ).symm
          ((Q.determinantTwist χ hχ).complexConjEquiv.symm f))) := rfl

@[simp] theorem determinantTwistComplexConjEquiv_apply_equiv (Q : OperatorSubquotient K n)
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) (f : Q.Space) :
    Q.determinantTwistComplexConjEquiv χ hχ
        ((Q.determinantTwist χ hχ).complexConjEquiv (Q.determinantTwistEquiv χ hχ f)) =
      Q.complexConj.determinantTwistEquiv χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ) (Q.complexConjEquiv f) := by
  exact (determinantTwistComplexConjEquiv_apply Q χ hχ _).trans
    ((congrArg (fun x => Q.complexConj.determinantTwistEquiv χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)
      (Q.complexConjEquiv ((Q.determinantTwistEquiv χ hχ).symm x)))
      ((Q.determinantTwist χ hχ).complexConjEquiv.symm_apply_apply _)).trans
        (congrArg (fun x => Q.complexConj.determinantTwistEquiv χ.complexConj
          ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ) (Q.complexConjEquiv x))
          ((Q.determinantTwistEquiv χ hχ).symm_apply_apply f)))

namespace Intertwiner

variable {Q T : OperatorSubquotient K n}

/-- The mixed quotient comparison commutes with both transports of every supplied map. -/
theorem determinantTwist_complexConj_naturality (L : Q.Intertwiner T)
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) :
    (L.complexConj.determinantTwist χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)).comp
        (Q.determinantTwistComplexConjEquiv χ hχ).toIntertwiningMap =
      (T.determinantTwistComplexConjEquiv χ hχ).toIntertwiningMap.comp
        (L.determinantTwist χ hχ).complexConj := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  refine (((Q.determinantTwistEquiv χ hχ).trans
    (Q.determinantTwist χ hχ).complexConjEquiv).surjective.forall
    (p := fun f => L.complexConj.determinantTwist χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)
        (Q.determinantTwistComplexConjEquiv χ hχ f) =
      T.determinantTwistComplexConjEquiv χ hχ
        ((L.determinantTwist χ hχ).complexConj f))).mpr ?_
  intro v
  change L.complexConj.determinantTwist χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)
      (Q.determinantTwistComplexConjEquiv χ hχ
        ((Q.determinantTwist χ hχ).complexConjEquiv (Q.determinantTwistEquiv χ hχ v))) =
    T.determinantTwistComplexConjEquiv χ hχ
      ((L.determinantTwist χ hχ).complexConj
        ((Q.determinantTwist χ hχ).complexConjEquiv (Q.determinantTwistEquiv χ hχ v)))
  exact (congrArg
    (fun x => L.complexConj.determinantTwist χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ) x)
    (Q.determinantTwistComplexConjEquiv_apply_equiv χ hχ v)).trans
      ((determinantTwist_apply_equiv L.complexConj χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ) (Q.complexConjEquiv v)).trans
          ((congrArg (T.complexConj.determinantTwistEquiv χ.complexConj
            ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ))
            (complexConj_apply_complexConjEquiv L v)).trans
              ((T.determinantTwistComplexConjEquiv_apply_equiv χ hχ (L v)).symm.trans
                ((congrArg (fun x => T.determinantTwistComplexConjEquiv χ hχ
                  ((T.determinantTwist χ hχ).complexConjEquiv x))
                  (determinantTwist_apply_equiv L χ hχ v).symm).trans
                    (congrArg (T.determinantTwistComplexConjEquiv χ hχ)
                      (complexConj_apply_complexConjEquiv (L.determinantTwist χ hχ)
                        (Q.determinantTwistEquiv χ hχ v)).symm)))))

end Intertwiner

namespace Equivalence

variable {Q T : OperatorSubquotient K n}

/-- The same mixed naturality identity retains genuine representation equivalences. -/
theorem determinantTwist_complexConj_naturality (e : Q.Equivalence T)
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) :
    (Q.determinantTwistComplexConjEquiv χ hχ).trans
        (e.complexConj.determinantTwist χ.complexConj
          ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ)) =
      (e.determinantTwist χ hχ).complexConj.trans
        (T.determinantTwistComplexConjEquiv χ hχ) := by
  apply Representation.Equiv.ext
  funext f
  exact congrArg (fun L => L f)
    (Intertwiner.determinantTwist_complexConj_naturality e.toIntertwiningMap χ hχ)

end Equivalence

namespace IsoClass

/-- Arithmetic CM transport intertwines determinant twists with the CM-pulled-back character. -/
theorem complexConj_determinantTwist (c : IsoClass K n)
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) :
    complexConj (determinantTwist c χ hχ) =
      determinantTwist (complexConj c) χ.complexConj
        ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ) := by
  refine Quotient.inductionOn c ?_
  intro Q
  exact ((Q.determinantTwist χ hχ).complexConj.isoClass_eq_iff
    (Q.complexConj.determinantTwist χ.complexConj
      ((HeckeCharacter.hasFiniteOrder_complexConj_iff χ).mpr hχ))).mpr
        ⟨Q.determinantTwistComplexConjEquiv χ hχ⟩

end IsoClass
end OperatorSubquotient
end Langlands.Automorphic
