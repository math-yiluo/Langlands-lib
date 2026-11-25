import Langlands.MathlibBase

/-! # Transport of integral closures in localizations along ring isomorphisms -/

noncomputable section

universe v

open Polynomial TensorProduct

namespace Langlands.CommutativeAlgebra.IntegralClosureTransfer

variable {R' A' C L₁ L₂ : Type*} [CommRing R'] [CommRing A'] [CommRing C] [CommRing L₁]
  [CommRing L₂] [Algebra R' A'] [Algebra R' C] [Algebra A' L₁] [Algebra C L₂]

/-- Integrality is preserved by a ring isomorphism compatible with base ring isomorphisms. -/
lemma isIntegral_map_of_comm (e : A' ≃+* C) (G : L₁ ≃+* L₂)
    (hG : ∀ a, G (algebraMap A' L₁ a) = algebraMap C L₂ (e a)) {x : L₁}
    (hx : IsIntegral A' x) : IsIntegral C (G x) := by
  obtain ⟨p, hpm, hp⟩ := hx
  refine ⟨p.map e.toRingHom, hpm.map _, ?_⟩
  rw [eval₂_map]
  have : (algebraMap C L₂).comp e.toRingHom = G.toRingHom.comp (algebraMap A' L₁) := by
    ext a; simp [hG]
  rw [this]
  have h := Polynomial.hom_eval₂ p (algebraMap A' L₁) G.toRingHom x
  rw [hp, map_zero] at h
  exact h.symm

/-- The ring isomorphism of integral closures induced by compatible isomorphisms of a base ring
and of its localizations. -/
def integralClosureEquiv (e : A' ≃+* C) (G : L₁ ≃+* L₂)
    (hG : ∀ a, G (algebraMap A' L₁ a) = algebraMap C L₂ (e a)) :
    integralClosure A' L₁ ≃+* integralClosure C L₂ where
  toFun x := ⟨G x, isIntegral_map_of_comm e G hG x.2⟩
  invFun y := ⟨G.symm y, isIntegral_map_of_comm e.symm G.symm (fun c => by
    apply G.injective
    rw [RingEquiv.apply_symm_apply, hG, RingEquiv.apply_symm_apply]) y.2⟩
  left_inv x := Subtype.ext (G.symm_apply_apply x)
  right_inv y := Subtype.ext (G.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul G x.1 y.1)
  map_add' x y := Subtype.ext (map_add G x.1 y.1)

lemma integralClosureEquiv_algebraMap (e : A' ≃+* C) (G : L₁ ≃+* L₂)
    (hG : ∀ a, G (algebraMap A' L₁ a) = algebraMap C L₂ (e a)) (a : A') :
    integralClosureEquiv e G hG (algebraMap A' (integralClosure A' L₁) a) =
      algebraMap C (integralClosure C L₂) (e a) :=
  Subtype.ext (hG a)

/-- Transfer of finiteness and of geometric reducedness of integral closures along an
`R'`-algebra isomorphism of base rings, for localizations away from the same element of `R'`. -/
theorem transfer [Algebra R' L₁] [IsScalarTower R' A' L₁]
    [Algebra R' (integralClosure C L₂)]
    (hcomp : ∀ s : R', algebraMap R' (integralClosure C L₂) s =
      algebraMap C (integralClosure C L₂) (algebraMap R' C s))
    (E : A' ≃ₐ[R'] C) (r : R')
    [IsLocalization.Away (algebraMap R' A' r) L₁] [IsLocalization.Away (algebraMap R' C r) L₂]
    (hfin : Module.Finite A' (integralClosure A' L₁))
    (hred : ∀ (F : Type v) [Field F] [Algebra R' F], IsReduced (F ⊗[R'] integralClosure A' L₁)) :
    Module.Finite C (integralClosure C L₂) ∧
      ∀ (F : Type v) [Field F] [Algebra R' F], IsReduced (F ⊗[R'] integralClosure C L₂) := by
  have H : (Submonoid.powers (algebraMap R' A' r)).map E.toRingEquiv.toMonoidHom =
      Submonoid.powers (algebraMap R' C r) := by
    rw [Submonoid.map_powers]
    congr 1
    exact E.commutes r
  let G : L₁ ≃+* L₂ := IsLocalization.ringEquivOfRingEquiv L₁ L₂ E.toRingEquiv H
  have hG : ∀ a, G (algebraMap A' L₁ a) = algebraMap C L₂ (E.toRingEquiv a) := fun a =>
    IsLocalization.ringEquivOfRingEquiv_eq H a
  let Φ := integralClosureEquiv E.toRingEquiv G hG
  have hΦ := integralClosureEquiv_algebraMap E.toRingEquiv G hG
  refine ⟨?_, ?_⟩
  · have h1 : (algebraMap A' (integralClosure A' L₁)).Finite := RingHom.finite_algebraMap.mpr hfin
    have h2 : (algebraMap C (integralClosure C L₂)) =
        (Φ.toRingHom.comp (algebraMap A' (integralClosure A' L₁))).comp E.symm.toRingEquiv.toRingHom := by
      ext c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hΦ]
      simp
    rw [← RingHom.finite_algebraMap, h2]
    exact (RingHom.Finite.of_surjective _ Φ.surjective).comp h1 |>.comp
      (RingHom.Finite.of_surjective _ E.symm.surjective)
  · intro F _ _
    let Φ' : integralClosure A' L₁ ≃ₐ[R'] integralClosure C L₂ :=
      { Φ with
        commutes' := fun s => by
          rw [hcomp]
          apply Subtype.ext
          change G (algebraMap R' L₁ s) = algebraMap C L₂ (algebraMap R' C s)
          rw [IsScalarTower.algebraMap_apply R' A' L₁, hG]
          congr 1
          exact E.commutes s }
    have := hred F
    let T := Algebra.TensorProduct.congr (AlgEquiv.refl (R := R') (A₁ := F)) Φ'
    exact isReduced_of_injective T.symm.toRingHom T.symm.injective

end Langlands.CommutativeAlgebra.IntegralClosureTransfer
