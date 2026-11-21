import Langlands.Global.Arithmetic.HarrisProposition48InductionData
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.Global.HeckeCharacterTransport

/-! # The identity Mackey constituent when `D` is contained in `E'` -/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris

open AdelicFunctoriality NumberField IsDedekindDomain
open scoped NumberField

section DegreeOne

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

set_option maxHeartbeats 600000 in
private theorem adeleInclusion_eq_equiv (j : K ≃+* L) (hj : j.toRingHom = algebraMap K L)
    (x : AdeleRing (𝓞 K) K) : adeleInclusion x = adeleEquiv j x := by
  apply Prod.ext
  · funext p
    rw [adeleInclusion_infinite_apply, adeleEquiv_infinite_apply]
    change infiniteCompletionMap (algebraMap K L) p (x.1 (p.comap (algebraMap K L))) =
      infiniteCompletionMap j.toRingHom p (x.1 (p.comap j.toRingHom))
    rw [hj]
  · apply FiniteAdeleRing.ext
    intro q
    have hq : q.under (𝓞 K) = finitePlaceEquiv j q := by
      apply HeightOneSpectrum.ext
      rw [finitePlaceEquiv_asIdeal]
      have hj' : (RingOfIntegers.mapRingEquiv j).toRingHom = algebraMap (𝓞 K) (𝓞 L) := by
        ext1 a
        apply Subtype.ext
        exact RingHom.congr_fun hj (a : K)
      rw [hj']
      rfl
    let g (p : HeightOneSpectrum (𝓞 K)) (h : q.under (𝓞 K) = p) : q.adicCompletion L :=
      let : q.asIdeal.LiesOver p.asIdeal := h ▸ liesOver_under q
      FiniteExtension.completionMap p q (x.2 p)
    have hg (p : HeightOneSpectrum (𝓞 K)) (h : q.under (𝓞 K) = p) :
        g (q.under (𝓞 K)) rfl = g p h := by
      subst p
      rfl
    let : q.asIdeal.LiesOver (finitePlaceEquiv j q).asIdeal := hq ▸ liesOver_under q
    have heq : (fun z : (finitePlaceEquiv j q).adicCompletion K =>
        FiniteExtension.completionMap (finitePlaceEquiv j q) q z) =
        fun z => finiteCompletionEquiv j q z := by
      apply (HeightOneSpectrum.denseRange_algebraMap K (finitePlaceEquiv j q)).equalizer
        (FiniteExtension.continuous_completionMap (finitePlaceEquiv j q) q)
        (continuous_finiteCompletionEquiv j q)
      funext a
      simp only [Function.comp_apply, FiniteExtension.completionMap_coe, finiteCompletionEquiv_coe]
      exact congrArg (algebraMap L (q.adicCompletion L)) (RingHom.congr_fun hj a).symm
    rw [adeleInclusion_finite_apply, adeleEquiv_finite_apply]
    change g (q.under (𝓞 K)) rfl = _
    rw [hg (finitePlaceEquiv j q) hq]
    exact congrFun heq (x.2 (finitePlaceEquiv j q))

private theorem ideleClassNorm_ideleClassEquiv (j : K ≃+* L) (hj : j.toRingHom = algebraMap K L)
    (x : IdeleClasses K) : ideleClassNorm (K := K) (ideleClassEquiv j x) = x := by
  have hdeg : Module.finrank K L = 1 := Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr (by
    rw [← hj]
    exact j.bijective)
  have hinc : ideleClassInclusion (K := K) (L := L) x = ideleClassEquiv j x := by
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [ideleClassInclusion_mk, ideleClassEquiv_mk]
      apply congrArg QuotientGroup.mk
      apply Units.ext
      rw [ideleInclusion_val, ideleEquiv_val, adeleInclusion_eq_equiv j hj]
  rw [← hinc]
  simpa only [hdeg, pow_one] using ideleClassNormInclusionPower K L x

end DegreeOne

namespace Proposition48Problem

/-- The embedded `E'` is the entire compositum at the identity double coset. -/
def identityMackeyEquiv (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (hD : D ≤ Q.conjugateField 1) : Q.E' ≃ₐ[Q.E] Q.mackeyField D 1 :=
  (Q.conjugateEmbedding 1).equivFieldRange.trans
    (IntermediateField.equivOfEq (sup_eq_right.mpr hD).symm)

/-- The ring identification respects the given inclusions from `E`. -/
theorem identityMackeyEquiv_algebraMap (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (hD : D ≤ Q.conjugateField 1) (x : Q.E) :
    (Q.identityMackeyEquiv D hD).toRingEquiv (algebraMap Q.E Q.E' x) =
      algebraMap Q.E (Q.mackeyField D 1) x :=
  (Q.identityMackeyEquiv D hD).commutes x

/-- Under the identification, the actual Mackey character pulls back to `ξ`. -/
theorem identityMackeyEquiv_comap (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (hD : D ≤ Q.conjugateField 1) :
    HeckeCharacter.comap (Q.identityMackeyEquiv D hD).toRingEquiv (Q.mackeyCharacter D 1) = Q.ξ := by
  let A := Q.conjugateField 1
  let M := Q.mackeyField D 1
  let : Algebra A M := (IntermediateField.inclusion (show A ≤ M from le_sup_right)).toAlgebra
  let f : Q.E' ≃+* A := (Q.conjugateEmbedding 1).equivFieldRange.toRingEquiv
  let j : A ≃+* M := (IntermediateField.equivOfEq (sup_eq_right.mpr hD).symm).toRingEquiv
  have hj : j.toRingHom = algebraMap A M := by
    ext1 a
    apply Subtype.ext
    rfl
  have he : (Q.identityMackeyEquiv D hD).toRingEquiv = f.trans j := rfl
  have hm : Q.mackeyCharacter D 1 =
      (HeckeCharacter.comap f.symm Q.ξ).comp (ideleClassNorm (K := A) (L := M)) := by
    rfl
  rw [he, hm, HeckeCharacter.comap_trans]
  have hcomap : HeckeCharacter.comap j
      ((HeckeCharacter.comap f.symm Q.ξ).comp (ideleClassNorm (K := A) (L := M))) =
      HeckeCharacter.comap f.symm Q.ξ := by
    apply ContinuousMonoidHom.ext
    intro x
    change (HeckeCharacter.comap f.symm Q.ξ)
      (ideleClassNorm (K := A) (ideleClassEquiv j x)) = _
    rw [ideleClassNorm_ideleClassEquiv j hj]
  rw [hcomap, HeckeCharacter.comap_comap_symm]

end Proposition48Problem

end Langlands.Global.Harris
