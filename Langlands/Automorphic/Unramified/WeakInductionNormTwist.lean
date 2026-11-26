import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.FiniteAdelicGL.SphericalArithmeticTransport
import Langlands.Global.HeckeCharacterUnramifiedNorm

/-! # Determinant twisting of cuspidal weak induction -/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open CuspidalOperatorRealization Polynomial
open scoped NumberField

section Norm

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

/-- The finite component of the pullback by the actual idele-class norm. -/
theorem finiteComponent_comp_ideleClassNorm (χ : HeckeCharacter F) (v : FinitePlace F)
    (w : FinitePlacesAbove E v) (x : (FiniteCompletion E w.1)ˣ) :
    HeckeCharacter.finiteComponent (χ.comp (ideleClassNorm (K := F) (L := E))) w.1 x =
      χ.finiteComponent v (FiniteExtension.localUnitNorm v w.1 x) := by
  change χ (ideleClassNorm (K := F)
    (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 E) E w.1 x)) = _
  rw [ideleClassNorm_ofAdicCompletion]
  rfl

private theorem comp_ideleClassNorm_finiteUniformizerValue
    (χ : HeckeCharacter F) (v : FinitePlace F) (w : FinitePlacesAbove E v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1) (hχ : χ.IsUnramifiedAt v) :
    HeckeCharacter.finiteUniformizerValue (χ.comp (ideleClassNorm (K := F) (L := E))) w.1 =
      χ.finiteUniformizerValue v ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
  let π := (CompletionPadic.padicField w.1).canonicalTopologicalData.uniformizerUnit
  let ϖ := (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
  let ϖ' := Units.map (FiniteExtension.completionMap v w.1).toMonoidHom ϖ
  have hϖ' : Valued.v (ϖ' : FiniteCompletion E w.1) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (FiniteExtension.completionMap v w.1 (ϖ : FiniteCompletion F v)) = _
    rw [FiniteExtension.valuation_completionMap, he, pow_one,
      FiniteAdelicGL.completion_uniformizer_value]
  let ε : (FiniteCompletion E w.1)ˣ := ϖ'⁻¹ * π
  have hε : Valued.v (ε : FiniteCompletion E w.1) = 1 := by
    have h0 : Valued.v (ϖ' : FiniteCompletion E w.1) ≠ 0 := by
      rw [hϖ']
      exact WithZero.coe_ne_zero
    rw [show ε = ϖ'⁻¹ * π from rfl, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
      show Valued.v (π : FiniteCompletion E w.1) = WithZero.exp (-1 : ℤ) from
        FiniteAdelicGL.completion_uniformizer_value w.1,
      ← hϖ', inv_mul_cancel₀ h0]
  have hnorm : FiniteExtension.localUnitNorm v w.1 ϖ' = ϖ ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
    apply Units.ext
    rw [FiniteExtension.localUnitNorm_val]
    change FiniteExtension.localNorm v w.1
      (FiniteExtension.completionMap v w.1 (ϖ : FiniteCompletion F v)) = _
    rw [FiniteExtension.localNorm_algebraMap, localDegree_eq, he, one_mul, Units.val_pow_eq_pow_val]
  have hunit : χ.finiteComponent v (FiniteExtension.localUnitNorm v w.1 ε) = 1 :=
    hχ _ (FiniteExtension.localUnitNorm_integral v w.1 (HeckeCharacter.mem_units_of_valued_eq_one hε))
  change HeckeCharacter.finiteComponent (χ.comp (ideleClassNorm (K := F) (L := E))) w.1 π =
    χ.finiteComponent v ϖ ^ _
  rw [finiteComponent_comp_ideleClassNorm χ v w π, show π = ϖ' * ε from (mul_inv_cancel_left _ _).symm,
    map_mul, map_mul, hnorm, hunit, mul_one, map_pow]

end Norm

/-- A determinant twist downstairs and its idele-norm pullback upstairs
preserve the given cuspidal weak induction. -/
def WeakInductionNormTwistStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    {r m : ℕ} (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E m)
    (χ : HeckeCharacter F),
    S.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass →
    (S.heckeDeterminantTwist χ).isoClass.IsWeakInductionOf.{uF, uE, uV, uW}
      (T.heckeDeterminantTwist (χ.comp (ideleClassNorm (K := F) (L := E)))).isoClass

set_option maxHeartbeats 500000 in
/-- Scaling at the lower place and scaling at each upper place commute
with the substitutions defining the induced Euler polynomial. -/
theorem weakInductionNormTwist : WeakInductionNormTwistStatement.{uF, uE, uV, uW} := by
  classical
  intro F E _ _ _ _ _ _ _ r m S T χ h
  obtain ⟨P, Q, hPQ⟩ := (IsoClass.isWeakInductionOf_isoClass_iff S T).mp h
  let χE : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
  let Pχ := P.heckeDeterminantTwist χ
  let Qχ := Q.heckeDeterminantTwist χE
  apply (IsoClass.isWeakInductionOf_isoClass_iff _ _).mpr
  refine ⟨Pχ, Qχ, hPQ.1, ?_⟩
  obtain ⟨A, hA⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F χ
  filter_upwards [hPQ.2, A.eventually_cofinite_notMem, Pχ.exceptional.eventually_cofinite_notMem,
    SpectralSystem.eventually_avoidsAbove (F := F) Qχ.exceptional] with v hgood hvA hv hAbove
  obtain ⟨hP, hQ, he, hEuler⟩ := hgood
  refine ⟨hv, hAbove, he, ?_⟩
  rw [P.heckeDeterminantTwist_eulerPolynomial χ v hv, hEuler]
  simp only [SpectralSystem.inducedEulerPolynomial, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Q.heckeDeterminantTwist_eulerPolynomial χE w.1 (hAbove w)]
  simp only [Polynomial.comp_assoc, pow_comp, X_comp, mul_comp, C_comp, χE,
    comp_ideleClassNorm_finiteUniformizerValue χ v w (he w) (hA v hvA),
    Units.val_pow_eq_pow_val, map_pow, mul_pow]

end Langlands.Automorphic.Unramified
