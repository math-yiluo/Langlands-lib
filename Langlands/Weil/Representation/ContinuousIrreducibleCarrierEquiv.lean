import Langlands.VirtualRepresentation.ExactUniverseTransport
import Langlands.Weil.Representation.TwistClasses
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-!
# Changing the carrier universe of continuous irreducible classes

Finite-dimensional coordinate models give a rank-preserving bijection of
continuous irreducible complex representation classes across carrier universes.
It is characterized by genuine intertwining equivalences and commutes with
twisting by a continuous character.
-/

noncomputable section

set_option autoImplicit false

universe uG uV uW

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

private abbrev ContinuousIrreducibleObject (G : Type uG) [Group G] [TopologicalSpace G] :=
  {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous ∧ A.IsIrreducible}

private def transportContinuousIrreducible (A : ContinuousIrreducibleObject.{uG, uV} G) :
    ContinuousIrreducibleObject.{uG, uW} G :=
  ⟨transport A.val, (isContinuous_iff_of_equiv (coordinatesEquiv A.val)).mpr A.property.1,
    (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (coordinatesEquiv A.val)).mpr
      A.property.2⟩

private def transportContinuousIrreducibleClass :
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous ∧ A.IsIrreducible) →
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uW} ℂ G => A.IsContinuous ∧ A.IsIrreducible) :=
  Quotient.map transportContinuousIrreducible fun A B ⟨e⟩ =>
    ⟨((coordinatesEquiv A.val).trans e).trans (coordinatesEquiv B.val).symm⟩

private theorem transportContinuousIrreducibleClass_rank
    (c : IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous ∧ A.IsIrreducible)) :
    classRank (forgetPropertyClass _ (transportContinuousIrreducibleClass.{uG, uV, uW} c)) =
      classRank (forgetPropertyClass _ c) := by
  induction c using Quotient.inductionOn with
  | h A => exact rank_eq_of_equiv (coordinatesEquiv A.val)

private theorem transportContinuousIrreducibleClass_cancel
    (c : IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous ∧ A.IsIrreducible)) :
    transportContinuousIrreducibleClass.{uG, uW, uV}
      (transportContinuousIrreducibleClass.{uG, uV, uW} c) = c := by
  induction c using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound
      ⟨(coordinatesEquiv (transport.{uG, uV, uW} A.val)).trans (coordinatesEquiv A.val)⟩

/-- Change the carrier universe of the genuine rank-`n` continuous irreducible
classes of one topological group. -/
def continuousIrreducibleCarrierEquiv (G : Type uG) [Group G] [TopologicalSpace G] (n : ℕ) :
    ContinuousIrreducibleClasses.{uG, uV} G n ≃ ContinuousIrreducibleClasses.{uG, uW} G n where
  toFun c := ⟨transportContinuousIrreducibleClass c.val,
    (transportContinuousIrreducibleClass_rank c.val).trans c.property⟩
  invFun c := ⟨transportContinuousIrreducibleClass c.val,
    (transportContinuousIrreducibleClass_rank c.val).trans c.property⟩
  left_inv c := Subtype.ext (transportContinuousIrreducibleClass_cancel.{uG, uV, uW} c.val)
  right_inv c := Subtype.ext (transportContinuousIrreducibleClass_cancel.{uG, uW, uV} c.val)

/-- A representative of the source class and a representative of its image
are related by an actual complex-linear intertwining equivalence. -/
theorem continuousIrreducibleCarrierEquiv_rep_iff {n : ℕ}
    (c : ContinuousIrreducibleClasses.{uG, uV} G n)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (B : FiniteRepresentation.{0, uG, uW} ℂ G)
    (hA : forgetPropertyClass _ c.val = classOf A) :
    forgetPropertyClass _ (continuousIrreducibleCarrierEquiv G n c).val = classOf B ↔
      Nonempty (Equiv A B) := by
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h C =>
    change classOf C.val = classOf A at hA
    obtain ⟨a⟩ := (classOf_eq_iff C.val A).mp hA
    change classOf (transport.{uG, uV, uW} C.val) = classOf B ↔ _
    rw [classOf_eq_iff]
    let e := (coordinatesEquiv.{uG, uV, uW} C.val).trans a
    exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Change of carrier commutes with the action of a continuous character. -/
theorem continuousIrreducibleCarrierEquiv_twist (χ : G →ₜ* ℂˣ) {n : ℕ}
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    continuousIrreducibleCarrierEquiv.{uG, uV, uW} G n (continuousIrreducibleTwistEquiv χ n c) =
      continuousIrreducibleTwistEquiv χ n (continuousIrreducibleCarrierEquiv G n c) := by
  let d := continuousIrreducibleCarrierEquiv.{uG, uV, uW} G n c
  obtain ⟨A, hA⟩ := Quotient.exists_rep (forgetPropertyClass _ c.val)
  obtain ⟨B, hB⟩ := Quotient.exists_rep (forgetPropertyClass _ d.val)
  change classOf A = _ at hA
  change classOf B = _ at hB
  obtain ⟨e⟩ := (continuousIrreducibleCarrierEquiv_rep_iff c A B hA.symm).mp hB.symm
  apply Subtype.ext
  apply forgetPropertyClass_injective _
  rw [forget_continuousIrreducibleTwistEquiv]
  change _ = twistClass χ.toMonoidHom (forgetPropertyClass _ d.val)
  rw [← hB, twistClass_classOf]
  exact (continuousIrreducibleCarrierEquiv_rep_iff (continuousIrreducibleTwistEquiv χ n c)
    (twist χ.toMonoidHom A) (twist χ.toMonoidHom B) (by
      rw [forget_continuousIrreducibleTwistEquiv, ← hA, twistClass_classOf])).mpr
        ⟨twistEquiv χ.toMonoidHom e⟩

end Langlands.FiniteRepresentation
