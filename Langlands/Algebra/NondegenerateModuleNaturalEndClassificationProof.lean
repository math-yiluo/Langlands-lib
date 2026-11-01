import Langlands.Algebra.NondegenerateModuleNaturalEndClassificationStatement

/-!
# Proof of the actual forgetful natural-endomorphism classification

Renard I.1.6, printed pp.11–12/PDF17–18.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace NondegenerateModuleNaturalEndClassificationProof

open CategoryTheory
open NondegenerateModuleNaturalEndClassificationStatement

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- The orbit intertwiner from the lifted regular object, `a ↦ a • m`. -/
def orbitMap (hA : IsIdempotented A) (M : NondegenerateModuleCat.{uA, max uA uM} A)
    (m : M.obj) :
    NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA ⟶ M :=
  ObjectProperty.homMk
    { toFun a := a.down • m
      map_zero' := NonUnitalModule.zero_smul m
      map_add' a b := NonUnitalModule.add_smul a.down b.down m
      map_smul' a b := mul_smul a b.down m }

@[simp] theorem orbitMap_apply (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj)
    (a : (NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA).obj) :
    (orbitMap hA M m).hom.toAddMonoidHom a = a.down • m := rfl

/-- Naturality for the orbit intertwiner at an idempotent fixing `m`. -/
theorem app_eq_evaluation_smul (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj) (e : Idempotent A)
    (he : (e : A) • m = m) :
    θ.app M m =
      (θ.app (NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA)
        (ULift.up (e : A))).down • m := by
  have h := congrArg (fun f => f (ULift.up (e : A))) (θ.naturality (orbitMap hA M m))
  change θ.app M ((e : A) • m) = _ at h
  rw [he] at h
  exact h

theorem coordinateRecovery (hA : IsIdempotented A) :
    CoordinateRecovery.{uA, uM} hA := by
  intro x e
  have he : (e : A) • (ULift.up (e : A) :
      (NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA).obj) =
      ULift.up (e : A) :=
    congrArg ULift.up e.property
  have key := IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq hA x
    (NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA)
    (ULift.up (e : A)) e he
  exact (congrArg ULift.down key).trans (x.property.1 e)

theorem familyRecovery (hA : IsIdempotented A) : FamilyRecovery.{uA, uM} hA := by
  intro x
  apply Subtype.ext
  funext e
  exact coordinateRecovery hA x e

theorem componentPointRecovery (hA : IsIdempotented A) :
    ComponentPointRecovery.{uA, uM} hA := by
  intro θ M m
  obtain ⟨e, he⟩ := M.property m
  rw [IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq hA _ M m e he,
    app_eq_evaluation_smul hA θ M m e he]
  rfl

theorem componentRecovery (hA : IsIdempotented A) : ComponentRecovery.{uA, uM} hA := by
  intro θ M
  apply AddMonoidHom.ext
  exact componentPointRecovery hA θ M

theorem naturalEndRecovery (hA : IsIdempotented A) : NaturalEndRecovery.{uA, uM} hA := by
  intro θ
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  exact componentRecovery hA θ M

theorem familyCompositeIdentity (hA : IsIdempotented A) :
    FamilyCompositeIdentity.{uA, uM} hA := by
  let _ := IdempotentedRingRightLimit.ring hA
  let _ := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  exact RingHom.ext (familyRecovery hA)

theorem naturalEndCompositeIdentity (hA : IsIdempotented A) :
    NaturalEndCompositeIdentity.{uA, uM} hA := by
  let _ := IdempotentedRingRightLimit.ring hA
  let _ := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  exact RingHom.ext (naturalEndRecovery hA)

theorem specifiedRingEquivalence (hA : IsIdempotented A) :
    SpecifiedRingEquivalence.{uA, uM} hA := by
  let _ := IdempotentedRingRightLimit.ring hA
  let _ := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  exact ⟨RingEquiv.ofRingHom
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA)
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA)
      (naturalEndCompositeIdentity hA) (familyCompositeIdentity hA), rfl, rfl⟩

theorem classification : Classification.{uA, uM} := by
  intro A _ hA
  exact ⟨familyCompositeIdentity hA, naturalEndCompositeIdentity hA, familyRecovery hA,
    naturalEndRecovery hA, componentRecovery hA, componentPointRecovery hA,
    coordinateRecovery hA, specifiedRingEquivalence hA⟩

end NondegenerateModuleNaturalEndClassificationProof
end Langlands.Algebra
