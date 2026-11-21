import Langlands.Global.FiniteAdelicGL.SphericalArithmeticTransport
import Langlands.Automorphic.HeckeDeterminantTwistWeakInductionStatement
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.HeckeCharacterUnramifiedNorm

/-! # Direct Euler weak induction of a determinant-twisted presentation -/

noncomputable section

universe uE uV

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction
open scoped NumberField

/-- Twisting the actual presentation preserves direct Euler weak induction, with the inducing
character multiplied by the norm pullback of the twisting character. -/
theorem heckeDeterminantTwistWeakInduction : HeckeDeterminantTwistWeakInductionStatement.{uE, uV} := by
  classical
  intro E E' _ _ _ _ _ _ r S P ξ ν h
  obtain ⟨T, hT⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt E ν
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, T.eventually_cofinite_notMem] with v hv hvT
  intro hv'
  have hgood : v ∉ P.exceptional ∪ ν.finiteHeckeDeterminantTail (r + 1) := hv'
  obtain ⟨hunr, hEuler⟩ := hv (fun hmem => hgood (Finset.mem_union_left _ hmem))
  have hν := hT v hvT
  refine ⟨?_, ?_⟩
  · intro w
    refine ⟨(hunr w).1, ?_⟩
    intro a ha
    change ξ.finiteComponent w.1 a * (HeckeCharacter.normComp (L := E') ν).finiteComponent w.1 a = 1
    rw [(hunr w).2 a ha, HeckeCharacter.normComp_isUnramifiedAt ν v hν w a ha, one_mul]
  · intro ϖ hϖ
    rw [P.heckeDeterminantTwist_eulerPolynomial ν v hgood, hEuler ϖ hϖ]
    simp only [inducedEulerPolynomial, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hn : (HeckeCharacter.normComp (L := E') ν).finiteComponent w.1 (ϖ w) =
        ν.finiteUniformizerValue v ^ w.1.asIdeal.inertiaDeg (𝓞 E) :=
      HeckeCharacter.normComp_finiteComponent_uniformizer ν v w (hunr w).1 hν (ϖ w) (hϖ w)
        _ (Langlands.Global.FiniteAdelicGL.completion_uniformizer_value v)
    simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, HeckeCharacter.finiteComponent_mul,
      ContinuousMonoidHom.mul_apply, hn, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_pow, map_pow, map_mul, mul_assoc]

end Langlands.Automorphic
