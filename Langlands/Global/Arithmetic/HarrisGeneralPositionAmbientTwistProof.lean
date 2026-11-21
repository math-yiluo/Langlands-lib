import Langlands.Global.Arithmetic.HarrisParityLocalTransportStatement
import Langlands.Representation.Twist.SubquotientProof
import Langlands.VirtualRepresentation.ExactInductionTwist
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! # Ambient Weil character twists preserve Harris general position -/

noncomputable section

universe uF uG

namespace Langlands.Global.Harris

open FiniteRepresentation GeneralPosition LocalFactor.CommonClosure

/-- Each actual Mackey constituent of the new character is the scalar twist
of the original constituent by the ambient character restricted to `K`. -/
private def mackeyConstituentAmbientTwistEquiv {G : Type uG} [Group G]
    (H K : Subgroup G) [H.FiniteIndex] (g : G) (χ χ' : H →* ℂˣ) (ψ : G →* ℂˣ)
    (h : ∀ w : H, χ' w = χ w * ψ w.val) :
    FiniteRepresentation.Equiv (mackeyConstituent H K (characterLine.{uG, 0} χ') g)
      (FiniteRepresentation.twist (ψ.comp K.subtype)
        (mackeyConstituent H K (characterLine.{uG, 0} χ) g)) := by
  let S := (conjugate H g).subgroupOf K
  let φ := conjugateRestriction H K g
  let η := ψ.comp K.subtype
  have hψ (s : S) : ψ (φ s).val = (η.comp S.subtype) s := by
    change ψ (MulAut.conj g⁻¹ ((s : K) : G)) = ψ ((s : K) : G)
    rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv, mul_right_comm,
      inv_mul_cancel, one_mul]
  have hχ : χ'.comp φ = (η.comp S.subtype) * (χ.comp φ) := by
    apply MonoidHom.ext
    intro s
    change χ' (φ s) = (η.comp S.subtype) s * χ (φ s)
    rw [h, hψ, mul_comm]
  change FiniteRepresentation.Equiv (induce S (characterLine.{uG, 0} (χ'.comp φ)))
    (FiniteRepresentation.twist η (induce S (characterLine.{uG, 0} (χ.comp φ))))
  rw [hχ]
  exact (induceEquiv S (twistCharacterLineEquiv.{uG, 0} (η.comp S.subtype)
    (χ.comp φ)).symm).trans (induceTwistEquiv S η _)

/-- The same tower and every one of its Mackey-constituent irreducibilities
witness general position after an ambient Weil character twist. -/
theorem generalPositionAmbientTwist : GeneralPositionAmbientTwistStatement.{uF} := by
  intro p _ F F' χ χ' ψ h hpos
  obtain ⟨t, tower, htop, hbot, hstep, hirr⟩ := hpos
  refine ⟨t, tower, htop, hbot, hstep, ?_⟩
  intro i g
  let H := weilSubgroup F F'
  let K := weilSubgroup F (tower i)
  let A := mackeyConstituent H K (characterLine.{uF, 0} χ.toMonoidHom) g
  let e := mackeyConstituentAmbientTwistEquiv H K g
    χ.toMonoidHom χ'.toMonoidHom ψ.toMonoidHom h
  exact (Weil.IsomorphismInvariance.irreducible_iff e).mpr
    ((Langlands.isIrreducible_twist_iff (ψ.toMonoidHom.comp K.subtype) A.representation).mpr
      (hirr i g))

end Langlands.Global.Harris
