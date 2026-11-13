import Langlands.Algebra.NondegenerateModuleCenterStatements
import Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof

/-!
# Proof of the centre of the category of nondegenerate modules (Renard I.1.7)

Renard (9 July 2026), I.1.7, printed pp.12–13/PDF18–19. Proof of
`NondegenerateModuleCenterTheoremStatement`, through the published I.1.6
classification of the natural endomorphisms of the forgetful functor. The unital Remark is
proved in `Langlands.Algebra.UnitalNondegenerateModuleCenterProof`.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace NondegenerateModuleCenterProof

open CategoryTheory

universe uA uM

section Idempotented

variable {A : Type uA} [NonUnitalRing A]

/-- A compatible right family is determined by its action on the nondegenerate modules
with carriers in `Type (max uA uM)`: its coordinate at `e` is its action on `e` in the
lifted regular object (the published I.1.6 coordinate recovery). -/
theorem eq_of_act_eq (hA : IsIdempotented A) {x y : IdempotentedRingRightLimit A}
    (h : ∀ (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
      IdempotentedRingRightLimitAction.act M.property x m =
        IdempotentedRingRightLimitAction.act M.property y m) : x = y := by
  apply Subtype.ext
  funext e
  have hx := NondegenerateModuleNaturalEndClassificationProof.coordinateRecovery.{uA, uM} hA x e
  have hy := NondegenerateModuleNaturalEndClassificationProof.coordinateRecovery.{uA, uM} hA y e
  have hR := congrArg ULift.down
    (h (NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA)
      (ULift.up (e : A)))
  exact hx.symm.trans (hR.trans hy)

/-- Injectivity: two commutant elements with the same central action on every module act
equally on the lifted regular object, hence are equal. -/
theorem fromCommutantRingHom_injective (hA : IsIdempotented A) :
    Function.Injective (NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA) := by
  intro x y h
  apply Subtype.ext
  apply eq_of_act_eq.{uA, uM} hA
  intro M m
  exact congrArg
    (fun θ : NondegenerateModuleCenter.{uA, max uA uM} A => (θ.app M).hom.toAddMonoidHom m) h

/-- Surjectivity: the family `θ_A` recovered from a central `θ` by the I.1.6 evaluation
commutes with `A`, because the components of `θ` are original module maps, and it acts
by `θ` on every module. -/
theorem fromCommutantRingHom_surjective (hA : IsIdempotented A) :
    Function.Surjective (NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA) := by
  intro θ
  let φ : IdempotentedRingRightLimit A :=
    NondegenerateModuleNaturalEndEvaluation.familyAddHom.{uA, uM} hA
      (NondegenerateModuleCenter.forget θ)
  have hφ : ∀ (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
      IdempotentedRingRightLimitAction.act M.property φ m = (θ.app M).hom.toAddMonoidHom m :=
    NondegenerateModuleNaturalEndClassificationProof.componentPointRecovery.{uA, uM} hA
      (NondegenerateModuleCenter.forget θ)
  have hmem : φ ∈ NondegenerateModuleCenter.commutantSubring hA := by
    refine (NondegenerateModuleCenter.mem_commutantSubring_iff hA φ).mpr fun a => ?_
    apply eq_of_act_eq.{uA, uM} hA
    intro M m
    change IdempotentedRingRightLimitAction.act M.property
        (IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) φ) m =
      IdempotentedRingRightLimitAction.act M.property
        (IdempotentedRingRightLimit.product hA φ (IdempotentedRingRightLimit.canonical a)) m
    rw [IdempotentedRingRightLimitAction.product_act hA M.property,
      IdempotentedRingRightLimitAction.product_act hA M.property,
      IdempotentedRingRightLimitAction.canonical_act hA M.property,
      IdempotentedRingRightLimitAction.canonical_act hA M.property, hφ, hφ]
    exact ((θ.app M).hom.map_smul a m).symm
  refine ⟨⟨φ, hmem⟩, ?_⟩
  apply CatCenter.ext
  intro M
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro m
  exact hφ M m

/-- The centre of `Â` lies in the commutant of the image of `A`. -/
theorem mem_commutantSubring_of_mem_centerSubring (hA : IsIdempotented A)
    {x : IdempotentedRingRightLimit A} (hx : x ∈ IdempotentedRingRightLimit.centerSubring hA) :
    x ∈ NondegenerateModuleCenter.commutantSubring hA :=
  (NondegenerateModuleCenter.mem_commutantSubring_iff hA x).mpr fun _ =>
    (IdempotentedRingRightLimit.mem_centerSubring_iff_mul hA x).mp hx _

/-- The commutant lies in the centre: the action of a commutant element on a nondegenerate
module is an original module map, and the action of every family commutes with original
module maps; the products are then equal by `eq_of_act_eq`. -/
theorem mem_centerSubring_of_mem_commutantSubring (hA : IsIdempotented A)
    {x : IdempotentedRingRightLimit A} (hx : x ∈ NondegenerateModuleCenter.commutantSubring hA) :
    x ∈ IdempotentedRingRightLimit.centerSubring hA := by
  refine (IdempotentedRingRightLimit.mem_centerSubring_iff hA x).mpr fun y => ?_
  apply eq_of_act_eq.{uA, 0} hA
  intro M m
  rw [IdempotentedRingRightLimitAction.product_act hA M.property,
    IdempotentedRingRightLimitAction.product_act hA M.property]
  exact (IdempotentedRingRightLimitAction.map_act hA M.property M.property
    (NondegenerateModuleCenter.component hA ⟨x, hx⟩ M) y m).symm

theorem commutantSubring_eq_centerSubring (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    NondegenerateModuleCenter.commutantSubring hA = IdempotentedRingRightLimit.centerSubring hA :=
  letI := IdempotentedRingRightLimit.ring hA
  Subring.ext fun _ =>
    ⟨mem_centerSubring_of_mem_commutantSubring hA, mem_commutantSubring_of_mem_centerSubring hA⟩

/-- `toCenter ∘ toFamily = id`: both maps keep every coordinate `z(e)`. -/
theorem toCenter_toFamily (hA : IsIdempotented A) (z : IdempotentedRingRightLimit.Center hA) :
    IdempotentedRingCornerCenter.Family.toCenter hA
      (IdempotentedRingRightLimit.Center.toFamily hA z) = z :=
  IdempotentedRingRightLimit.Center.ext fun _ => rfl

/-- `toFamily ∘ toCenter = id`: both maps keep every coordinate. -/
theorem toFamily_toCenter (hA : IsIdempotented A) (x : IdempotentedRingCornerCenter.Family A) :
    IdempotentedRingRightLimit.Center.toFamily hA
      (IdempotentedRingCornerCenter.Family.toCenter hA x) = x :=
  Subtype.ext (funext fun _ => Subtype.ext (Subtype.ext rfl))

end Idempotented

/-- Renard I.1.7, the Theorem and the paragraph before it. -/
theorem nondegenerateModuleCenterTheorem :
    NondegenerateModuleCenterTheoremStatement.{uA, uM} := by
  intro A _ hA
  exact ⟨⟨fromCommutantRingHom_injective.{uA, uM} hA, fromCommutantRingHom_surjective.{uA, uM} hA⟩,
    commutantSubring_eq_centerSubring hA, toCenter_toFamily hA, toFamily_toCenter hA⟩

end NondegenerateModuleCenterProof
end Langlands.Algebra
