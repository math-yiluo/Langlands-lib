import Langlands.Automorphic.Unramified.CyclicRegularInductionNormReduction
import Langlands.Automorphic.Unramified.CyclicRegularInductionReductionStatement

/-! # Regular cyclic induction from existence, the norm-character order and Euler recovery

Both reductions of `Langlands.Automorphic.Unramified.CyclicRegularInductionReductionStatement`
are proved here. The unrestricted reduction is `cyclicRegularInductionNormReduction`, which
does not use the arithmetic premise `CyclicNormKernelUnramifiedOrderStatement`. The totally
complex reduction repeats its argument over a totally complex base: the existence witness
supplies the rank, the twist of the witness by the norm-kernel character is a second weak
induction of the same upper cusp, and Euler recovery over the totally complex base identifies
every cuspidal weak induction of that rank with the witness. The two auxiliary lemmas on the
twist are private in `Langlands.Automorphic.Unramified.CyclicRegularInductionNormReduction`
and are proved again here by the same argument.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open NumberField CuspidalOperatorRealization
open scoped NumberField

section

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

/-- At a base place where an upper place is unramified, a character trivial on norms takes a
value at the base uniformizer whose power by the residue degree is one: the local norm of the
embedded uniformizer is its power by the residue degree. -/
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

/-- The twist of a weak induction by a character trivial on norms is again a weak induction
of the same upper class: scaling the lower spectrum by the character values fixes each
induced factor, a polynomial in `X ^ f`. -/
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

/-- Over a totally complex base, Euler recovery makes any two cuspidal weak inductions of one
rank from the same upper class equal: their attached spectra have equal Euler denominators at
almost all places, and recovery applies to the two singleton families. -/
theorem isWeakInductionOf_unique_of_cuspidalEulerConstituentRecoveryTC
    [NumberField.IsTotallyComplex F]
    (hRig : CuspidalEulerConstituentRecoveryTCStatement.{uF, uV})
    {r m : ℕ} {c d : IsoClass F r} {t : IsoClass E m}
    (hc : c.IsWeakInductionOf.{uF, uE, uV, uW} t)
    (hd : d.IsWeakInductionOf.{uF, uE, uV, uW} t) : c = d := by
  obtain ⟨s, s', hs, hs', heul⟩ := exists_sameEulerPolynomials_of_isWeakInductionOf hc hd
  let c₁ : Fin 1 → PositiveRankCuspidalClass F := fun _ => PositiveRankCuspidalClass.ofFixedRank c
  let d₁ : Fin 1 → PositiveRankCuspidalClass F := fun _ => PositiveRankCuspidalClass.ofFixedRank d
  let sc : ∀ i, SpectralSystem (Langlands.Global.FinitePlace F) (c₁ i).rank := fun _ => s
  let sd : ∀ i, SpectralSystem (Langlands.Global.FinitePlace F) (d₁ i).rank := fun _ => s'
  have hsum := (IsobaricData.sameEulerPolynomials_finiteSum_one sc).symm.trans
    (heul.trans (IsobaricData.sameEulerPolynomials_finiteSum_one sd))
  obtain ⟨e, he⟩ := hRig F 1 1 c₁ d₁ sc sd (fun _ => hs) (fun _ => hs') hsum
  exact PositiveRankCuspidalClass.ofFixedRank_injective r (he 0)

end

/-- The unrestricted reduction: `cyclicRegularInductionNormReduction` proves the conclusion
from the existence and Euler recovery premises alone. -/
theorem cyclicRegularInductionReduction :
    CyclicRegularInductionReductionStatement.{uF, uE, uV, uW} :=
  fun hExistence _ hRecovery => cyclicRegularInductionNormReduction hExistence hRecovery

/-- The totally complex reduction. The totally complex existence premise supplies the rank and
a unitary lower cusp weakly induced to the upper one. Its twist by the norm-kernel character is
another weak induction of the upper cusp, and totally complex Euler recovery identifies every
cuspidal weak induction of that rank with the witness, the twist included. -/
theorem cyclicRegularInductionReductionTC :
    CyclicRegularInductionReductionTCStatement.{uF, uE, uV, uW} := by
  intro hExistence _ hRecovery F E _ _ _ _ _ _ _ _ _ σ hσ η hη m T hunitary hregular
  obtain ⟨r, S, hr, _, hInd⟩ := hExistence F E σ hσ m T hunitary hregular
  have hUnique : ∀ c' : IsoClass F r,
      c'.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass → c' = S.isoClass :=
    fun c' hc' => isWeakInductionOf_unique_of_cuspidalEulerConstituentRecoveryTC
      hRecovery hc' hInd
  refine ⟨r, S.isoClass, hr, hInd, ?_, hUnique⟩
  have hTwist := isWeakInductionOf_determinantTwist hη.isTrivialOnNorm hInd
  exact (IsoClass.isFiniteOrderDeterminantTwist_iff_eq _ _ η hη.hasFiniteOrder).mpr
    (hUnique _ hTwist).symm

/-- Both reductions at the universe levels `.{0, 0, uV, uV}`. -/
example : CyclicRegularInductionReductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularInductionReductionTCStatement.{0, 0, uV, uV} :=
  ⟨cyclicRegularInductionReduction, cyclicRegularInductionReductionTC⟩

end Langlands.Automorphic.Unramified
