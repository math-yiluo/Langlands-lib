import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.Global.HeckeCharacterTransport

/-! # Arithmetic transport of weak automorphic induction of a Hecke character -/

noncomputable section

universe uK uL uK' uL' uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified.WeakInduction

open NumberField (RingOfIntegers)
open Langlands.Global AdelicFunctoriality IsDedekindDomain Polynomial
open scoped NumberField

variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']

private theorem finitePlaceEquiv_symm_apply {A B : Type*} [Field A] [Field B]
    (g : A ≃+* B) (v : FinitePlace A) :
    finitePlaceEquiv g.symm v = (finitePlaceEquiv g).symm v := by
  apply (finitePlaceEquiv g).injective
  rw [Equiv.apply_symm_apply, ← Equiv.trans_apply, ← finitePlaceEquiv_trans,
    RingEquiv.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]

variable (e : K ≃+* K') (f : L ≃+* L')
  (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x))

include he in
omit [NumberField K] [NumberField L] [NumberField K'] [NumberField L'] in
private theorem symm_square (x : K') :
    f.symm (algebraMap K' L' x) = algebraMap K L (e.symm x) := by
  apply f.injective
  rw [f.apply_symm_apply, he, e.apply_symm_apply]

include he in
omit [NumberField K] [NumberField L] [NumberField K'] [NumberField L'] in
private theorem integers_square (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K') (𝓞 L') (RingOfIntegers.mapRingEquiv e x) :=
  RingOfIntegers.ext (he (x : K))

private def placesAbovePullback (v : FinitePlace K') :
    FinitePlacesAbove L' v ≃ FinitePlacesAbove L (finitePlaceEquiv e v) where
  toFun w := by
    letI := w.2
    exact ⟨finitePlaceEquiv f w.1, Harris.finitePlaceEquiv_liesOver e f he v w.1⟩
  invFun w := by
    letI := w.2
    refine ⟨finitePlaceEquiv f.symm w.1, ?_⟩
    simpa only [finitePlaceEquiv_symm_apply, Equiv.symm_apply_apply] using
      Harris.finitePlaceEquiv_liesOver e.symm f.symm (symm_square e f he)
        (finitePlaceEquiv e v) w.1
  left_inv w := Subtype.ext (by simp only [finitePlaceEquiv_symm_apply, Equiv.symm_apply_apply])
  right_inv w := Subtype.ext (by simp only [finitePlaceEquiv_symm_apply, Equiv.apply_symm_apply])

private theorem map_placeIdeal {A B : Type*} [Field A] [Field B]
    (g : A ≃+* B) (v : FinitePlace B) :
    (finitePlaceEquiv g v).asIdeal.map (RingOfIntegers.mapRingEquiv g).toRingHom = v.asIdeal :=
  Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv g).surjective _

include he in
private theorem inertiaDeg_pullback (v : FinitePlace K') (w : FinitePlacesAbove L' v) :
    (finitePlaceEquiv f w.1).asIdeal.inertiaDeg (𝓞 K) = w.1.asIdeal.inertiaDeg (𝓞 K') := by
  let := w.2
  let := Harris.finitePlaceEquiv_liesOver e f he v w.1
  rw [Ideal.inertiaDeg_eq_of_isMaximal (finitePlaceEquiv e v).asIdeal,
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal]
  let ev := Ideal.quotientEquiv (finitePlaceEquiv e v).asIdeal v.asIdeal
    (RingOfIntegers.mapRingEquiv e) (map_placeIdeal e v).symm
  let fw := Ideal.quotientEquiv (finitePlaceEquiv f w.1).asIdeal w.1.asIdeal
    (RingOfIntegers.mapRingEquiv f) (map_placeIdeal f w.1).symm
  apply Algebra.finrank_eq_of_equiv_equiv ev fw
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk w.1.asIdeal
      (algebraMap (𝓞 K') (𝓞 L') (RingOfIntegers.mapRingEquiv e y)) =
    Ideal.Quotient.mk w.1.asIdeal (RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 K) (𝓞 L) y))
  rw [integers_square e f he]

include he in
omit [NumberField K] in
private theorem ramificationIdx_pullback (v : FinitePlace K') (w : FinitePlacesAbove L' v) :
    (finitePlaceEquiv f w.1).asIdeal.ramificationIdx (𝓞 K) = w.1.asIdeal.ramificationIdx (𝓞 K') := by
  let := w.2
  let := Harris.finitePlaceEquiv_liesOver e f he v w.1
  let g := RingOfIntegers.mapRingEquiv f
  let m : Ideal (𝓞 L) ≃* Ideal (𝓞 L') :=
    { (Ideal.relIsoOfBijective g.toRingHom g.bijective).symm.toEquiv with
      map_mul' := fun I J => Ideal.map_mul _ _ _ }
  have hmap (I : Ideal (𝓞 L)) : m I = I.map g.toRingHom := rfl
  have hc : g.toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) =
      (algebraMap (𝓞 K') (𝓞 L')).comp (RingOfIntegers.mapRingEquiv e).toRingHom :=
    RingHom.ext (integers_square e f he)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (finitePlaceEquiv e v).asIdeal
        _ (Ideal.map_ne_bot_of_ne_bot (finitePlaceEquiv e v).ne_bot),
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal
        _ (Ideal.map_ne_bot_of_ne_bot v.ne_bot), ← multiplicity_map_eq m, hmap, hmap,
      map_placeIdeal f w.1, Ideal.map_map, hc, ← Ideal.map_map, map_placeIdeal e v]

include he in
private theorem isUnramifiedAbove_pullback (χ : HeckeCharacter L') (v : FinitePlace K')
    (h : IsUnramifiedAbove χ v) :
    IsUnramifiedAbove (HeckeCharacter.comap f χ) (finitePlaceEquiv e v) := by
  intro w
  obtain ⟨q, rfl⟩ := (placesAbovePullback e f he v).surjective w
  exact ⟨(ramificationIdx_pullback e f he v q).trans (h q).1,
    (HeckeCharacter.isUnramifiedAt_comap_iff f χ q.1).mpr (h q).2⟩

private def pushUniformizers (v : FinitePlace K')
    (ϖ : ∀ w : FinitePlacesAbove L (finitePlaceEquiv e v), (FiniteCompletion L w.1)ˣ)
    (w : FinitePlacesAbove L' v) : (FiniteCompletion L' w.1)ˣ :=
  Units.mapEquiv (finiteCompletionEquiv f w.1).toMulEquiv (ϖ (placesAbovePullback e f he v w))

include he in
private theorem isUniformizerFamily_push (v : FinitePlace K')
    {ϖ : ∀ w : FinitePlacesAbove L (finitePlaceEquiv e v), (FiniteCompletion L w.1)ˣ}
    (hϖ : IsUniformizerFamily (finitePlaceEquiv e v) ϖ) :
    IsUniformizerFamily v (pushUniformizers e f he v ϖ) := by
  intro w
  exact (finiteCompletionEquiv_valuation f w.1 _).trans (hϖ (placesAbovePullback e f he v w))

include he in
private theorem inducedEulerPolynomial_pullback (χ : HeckeCharacter L') (v : FinitePlace K')
    (ϖ : ∀ w : FinitePlacesAbove L (finitePlaceEquiv e v), (FiniteCompletion L w.1)ˣ) :
    inducedEulerPolynomial (HeckeCharacter.comap f χ) (finitePlaceEquiv e v) ϖ =
      inducedEulerPolynomial χ v (pushUniformizers e f he v ϖ) := by
  unfold inducedEulerPolynomial
  symm
  apply Fintype.prod_equiv (placesAbovePullback e f he v)
  intro w
  let x : (FiniteCompletion L (finitePlaceEquiv f w.1))ˣ := ϖ (placesAbovePullback e f he v w)
  exact congrArg₂ (fun (z : ℂˣ) (n : ℕ) => 1 - C (z : ℂ) * X ^ n)
    (HeckeCharacter.comap_finiteComponent f χ w.1 x).symm (inertiaDeg_pullback e f he v w).symm

end Langlands.Automorphic.Unramified.WeakInduction

namespace Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

open Langlands.Global AdelicFunctoriality Langlands.Unramified
open Langlands.Automorphic.Unramified.WeakInduction

variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient K')]

/-- Pullback along a commuting square of number-field isomorphisms preserves weak
monomial automorphic induction, with no identifications of field universes. -/
theorem IsWeakAutomorphicInductionOf.arithmeticComap
    (e : K ≃+* K') (f : L ≃+* L')
    (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x))
    {r : ℕ} {c : IsoClass K' r} {χ : HeckeCharacter L'}
    (hc : IsWeakAutomorphicInductionOf.{uK', uL', uV} c χ) :
    IsWeakAutomorphicInductionOf.{uK, uL, uV} (arithmeticComap e c) (HeckeCharacter.comap f χ) := by
  obtain ⟨s, hs, hw⟩ := hc
  obtain ⟨t, ht, hEuler⟩ := cuspidalArithmeticSpectralTransport K K' e r c s hs
  refine ⟨t, ht, hw.1.trans (Algebra.finrank_eq_of_equiv_equiv e f (RingHom.ext fun x =>
    (he x).symm)).symm, ?_⟩
  have hj := (finitePlaceEquiv e).symm.injective.tendsto_cofinite
  have hweak := hj.eventually hw.2
  have hgood := hj.eventually s.exceptional.eventually_cofinite_notMem
  filter_upwards [hweak, hgood, hEuler] with v hwv hvs htv
  generalize hw : (finitePlaceEquiv e).symm v = w at hwv hvs htv
  have hvw : v = finitePlaceEquiv e w := (Equiv.symm_apply_eq _).mp hw
  subst v
  intro hv
  obtain ⟨hun, hind⟩ := hwv hvs
  refine ⟨isUnramifiedAbove_pullback e f he χ w hun, fun ϖ hϖ => ?_⟩
  exact (htv hv hvs).trans ((hind _ (isUniformizerFamily_push e f he w hϖ)).trans
    (inducedEulerPolynomial_pullback e f he χ w ϖ).symm)

end Langlands.Automorphic.CuspidalOperatorRealization.IsoClass
