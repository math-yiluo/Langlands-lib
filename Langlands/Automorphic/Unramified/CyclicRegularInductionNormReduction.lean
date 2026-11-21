import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Automorphic.CuspidalSpectralDeterminantTwist
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceStatement
import Langlands.Automorphic.Unramified.WeakInductionUniqueness
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-! # Regular cyclic induction from actual existence and Euler recovery -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open NumberField CuspidalOperatorRealization
open scoped NumberField

/-- Actual regular weak induction and Euler constituent recovery give the cyclic
regular induction statement. The norm-kernel hypothesis supplies the local powers
needed for the self-twist through the actual idèle norm. -/
def CyclicRegularInductionNormReductionStatement : Prop :=
  CyclicRegularInductionExistenceStatement.{uF, uE, uV, uW} →
  CuspidalEulerConstituentRecoveryStatement.{uF, uV} →
  CyclicRegularInductionStatement.{uF, uE, uV, uW}

section

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

-- The coordinate proof of `ideleClassNorm_ofAdicCompletion` with independent universes.
private theorem finiteUniformizerValue_pow_inertiaDeg {η : HeckeCharacter F}
    (hη : η.IsTrivialOnNorm E) (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v)
    (hw : w.1.asIdeal.ramificationIdx (𝓞 F) = 1) :
    η.finiteUniformizerValue v ^ w.1.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  let uniformizer := (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
  let upperUnit := Units.map (FiniteExtension.completionMap v w.1).toMonoidHom uniformizer
  have hnorm : FiniteExtension.localUnitNorm v w.1 upperUnit =
      uniformizer ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
    apply Units.ext
    rw [FiniteExtension.localUnitNorm_val]
    change FiniteExtension.localNorm v w.1
      (FiniteExtension.completionMap v w.1 (uniformizer : FiniteCompletion F v)) = _
    rw [FiniteExtension.localNorm_algebraMap, localDegree_eq, hw, one_mul, Units.val_pow_eq_pow_val]
  have h := hη (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w.1 upperUnit)
  rw [Langlands.Global.AdelicFunctoriality.ideleClassNorm_ofAdicCompletion v w, hnorm] at h
  change η.finiteComponent v (uniformizer ^ w.1.asIdeal.inertiaDeg (𝓞 F)) = 1 at h
  rw [map_pow] at h
  exact h

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

private theorem isWeakInductionOf_determinantTwist {r m : ℕ} {c : IsoClass F r}
    {d : IsoClass E m} {η : HeckeCharacter F} (hη : η.IsTrivialOnNorm E)
    (hc : c.IsWeakInductionOf.{uF, uE, uV, uW} d) :
    (c.determinantTwist η (hη.hasFiniteOrder E)).IsWeakInductionOf.{uF, uE, uV, uW} d := by
  obtain ⟨s, t, hs, ht, hind⟩ := hc
  have hscale : (SpectralSystem.scale η.finiteUniformizerValue s).SameEulerPolynomials s := by
    filter_upwards [hind.2] with v hv
    obtain ⟨_, htv, hram, heuler⟩ := hv
    intro hsScaled hvDefined
    calc
      (SpectralSystem.scale η.finiteUniformizerValue s).eulerPolynomial v hsScaled =
          (s.eulerPolynomial v hvDefined).comp
            (Polynomial.C (η.finiteUniformizerValue v : ℂ) * Polynomial.X) :=
        SpectralSystem.scale_eulerPolynomial η.finiteUniformizerValue s v hvDefined
      _ = s.eulerPolynomial v hvDefined := by
        rw [heuler, SpectralSystem.inducedEulerPolynomial, Polynomial.prod_comp]
        refine Finset.prod_congr rfl fun w _ => ?_
        have hpow : (η.finiteUniformizerValue v : ℂ) ^ w.1.asIdeal.inertiaDeg (𝓞 F) = 1 := by
          simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
            congrArg (fun a : ℂˣ => (a : ℂ))
              (finiteUniformizerValue_pow_inertiaDeg hη v w (hram w))
        rw [Polynomial.comp_assoc]
        simp only [Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow,
          hpow, Polynomial.C_1, one_mul]
  refine ⟨_, t, hs.determinantTwist η (hη.hasFiniteOrder E), ht, ?_⟩
  exact hind.of_sameEulerPolynomials
    (hscale.symm.trans (SpectralSystem.sameEulerPolynomials_restrict _ _ _))
    (SpectralSystem.sameEulerPolynomials_refl t)

end

/-- The actual norm-character twist is another weak induction of the given
upper cusp. Euler recovery identifies every cuspidal weak induction with the
witness supplied by existence, including this twist. -/
theorem cyclicRegularInductionNormReduction :
    CyclicRegularInductionNormReductionStatement.{uF, uE, uV, uW} := by
  intro hExistence hRecovery F E _ _ _ _ _ _ _ _ σ hσ η hη m T hunitary hregular
  obtain ⟨r, S, hr, _, hInd⟩ := hExistence F E σ hσ m T hunitary hregular
  have hUnique : ∀ c' : IsoClass F r,
      c'.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass → c' = S.isoClass :=
    fun c' hc' => weakInductionUniqueness_of_cuspidalEulerConstituentRecovery hRecovery
      F E r m c' S.isoClass T.isoClass hc' hInd
  refine ⟨r, S.isoClass, hr, hInd, ?_, hUnique⟩
  have hTwist := isWeakInductionOf_determinantTwist hη.isTrivialOnNorm hInd
  exact (IsoClass.isFiniteOrderDeterminantTwist_iff_eq _ _ η hη.hasFiniteOrder).mpr
    (hUnique _ hTwist).symm

end Langlands.Automorphic.Unramified
