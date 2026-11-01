import Langlands.Global.AdeleQuotientStatement
import Langlands.Global.AdelicFunctoriality.Isomorphism

/-! # Arithmetic transport of the actual additive adele quotient -/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdeleQuotientTransport

open AdelicFunctoriality

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- The actual arithmetic adele equivalence identifies the principal additive subgroups. -/
theorem map_principalAdeles (e : K ≃+* L) :
    (principalAdeles K).map (adeleEquiv e).toAddMonoidHom = principalAdeles L := by
  ext x
  constructor
  · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
    exact ⟨e k, (adeleEquiv_diagonal e k).symm⟩
  · rintro ⟨l, rfl⟩
    refine ⟨diagonal K (e.symm l), ⟨e.symm l, rfl⟩, ?_⟩
    change adeleEquiv e (diagonal K (e.symm l)) = diagonal L l
    rw [adeleEquiv_diagonal, e.apply_symm_apply]

/-- Arithmetic transport on the actual additive quotient, with its quotient topology. -/
def quotientEquiv (e : K ≃+* L) : AdeleQuotient K ≃ₜ+ AdeleQuotient L where
  __ := QuotientAddGroup.congr (principalAdeles K) (principalAdeles L)
    (adeleEquiv e).toAddEquiv (map_principalAdeles e)
  continuous_toFun := by
    apply (QuotientAddGroup.isQuotientMap_mk (principalAdeles K)).continuous_iff.mpr
    exact (adeleQuotientMap L).continuous.comp (continuous_adeleEquiv e)
  continuous_invFun := by
    apply (QuotientAddGroup.isQuotientMap_mk (principalAdeles L)).continuous_iff.mpr
    exact (adeleQuotientMap K).continuous.comp (continuous_adeleEquiv_symm e)

@[simp] theorem quotientEquiv_mk (e : K ≃+* L) (x : Adeles K) :
    quotientEquiv e (adeleQuotientMap K x) = adeleQuotientMap L (adeleEquiv e x) := rfl

@[simp] theorem quotientEquiv_symm_mk (e : K ≃+* L) (x : Adeles L) :
    (quotientEquiv e).symm (adeleQuotientMap L x) =
      adeleQuotientMap K ((adeleEquiv e).symm x) := rfl

@[simp] theorem quotientEquiv_refl :
    quotientEquiv (RingEquiv.refl K) = ContinuousAddEquiv.refl (AdeleQuotient K) := by
  apply ContinuousAddEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective (s := principalAdeles K) x
  change adeleQuotientMap K (adeleEquiv (RingEquiv.refl K) y) = adeleQuotientMap K y
  rw [adeleEquiv_refl]
  rfl

/-- Quotient transport is covariant under composition of field isomorphisms. -/
theorem quotientEquiv_trans (e : K ≃+* L) (a : L ≃+* M) :
    quotientEquiv (e.trans a) = (quotientEquiv e).trans (quotientEquiv a) := by
  apply ContinuousAddEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective (s := principalAdeles K) x
  change adeleQuotientMap M (adeleEquiv (e.trans a) y) =
    adeleQuotientMap M (adeleEquiv a (adeleEquiv e y))
  rw [adeleEquiv_trans]
  rfl

@[simp] theorem quotientEquiv_symm (e : K ≃+* L) :
    (quotientEquiv e).symm = quotientEquiv e.symm := by
  apply ContinuousAddEquiv.ext
  intro x
  apply (quotientEquiv e).injective
  rw [ContinuousAddEquiv.apply_symm_apply]
  have h := congrArg (fun b : AdeleQuotient L ≃ₜ+ AdeleQuotient L => b x)
    (quotientEquiv_trans e.symm e)
  simpa only [RingEquiv.symm_trans_self, quotientEquiv_refl,
    ContinuousAddEquiv.refl_apply, ContinuousAddEquiv.trans_apply] using h

end Langlands.Global.AdeleQuotientTransport
