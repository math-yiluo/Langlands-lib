import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Base change of a map induced from an actual affinoid pushout -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout.LiftBaseChange

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D E : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
  (k : BoundedAlgHom K A D) (h : BoundedAlgHom K C D)
  (hk : h.comp g = k)
  (p : BoundedAlgHom K B E) (q : BoundedAlgHom K C E)
  (hpq : p.comp f = q.comp g)

/-- The actual map induced from the first bounded pushout. -/
def sourceMap : BoundedAlgHom K (algebra f g) E := lift f g E p q hpq

/-- Restriction to the second coefficient algebra, retaining both original legs. -/
def restriction : BoundedAlgHom K (algebra f g) (algebra f k) :=
  lift f g _ (leftMap f k) ((rightMap f k).comp h)
    (by rw [BoundedAlgHom.comp_assoc, hk, condition])

@[simp] theorem restriction_left :
    (restriction f g k h hk).comp (leftMap f g) = leftMap f k :=
  lift_comp_leftMap _ _ _ _ _ _

@[simp] theorem restriction_right :
    (restriction f g k h hk).comp (rightMap f g) = (rightMap f k).comp h :=
  lift_comp_rightMap _ _ _ _ _ _

include hk hpq in
omit [CompleteSpace K] in
private theorem target_condition :
    ((leftMap q h).comp p).comp f = (rightMap q h).comp k := by
  rw [BoundedAlgHom.comp_assoc, hpq, ← BoundedAlgHom.comp_assoc, condition,
    BoundedAlgHom.comp_assoc, hk]

/-- The direct map on the further coefficient change. -/
def targetMap : BoundedAlgHom K (algebra f k) (algebra q h) :=
  lift f k _ ((leftMap q h).comp p) (rightMap q h)
    (target_condition f g k h hk p q hpq)

@[simp] theorem targetMap_left :
    (targetMap f g k h hk p q hpq).comp (leftMap f k) = (leftMap q h).comp p :=
  lift_comp_leftMap _ _ _ _ _ _

@[simp] theorem targetMap_right :
    (targetMap f g k h hk p q hpq).comp (rightMap f k) = rightMap q h :=
  lift_comp_rightMap _ _ _ _ _ _

private theorem forward_condition :
    (leftMap q h).comp (sourceMap f g p q hpq) =
      (targetMap f g k h hk p q hpq).comp (restriction f g k h hk) := by
  apply hom_ext f g
  · rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc,
      restriction_left, targetMap_left]
    rw [sourceMap, lift_comp_leftMap]
  · rw [BoundedAlgHom.comp_assoc, sourceMap, lift_comp_rightMap,
      BoundedAlgHom.comp_assoc, restriction_right,
      ← BoundedAlgHom.comp_assoc (targetMap f g k h hk p q hpq) (rightMap f k) h,
      targetMap_right, condition]

def forward : BoundedAlgHom K
    (algebra (sourceMap f g p q hpq) (restriction f g k h hk)) (algebra q h) :=
  lift _ _ _ (leftMap q h) (targetMap f g k h hk p q hpq)
    (forward_condition f g k h hk p q hpq)

@[simp] theorem forward_left :
    (forward f g k h hk p q hpq).comp
      (leftMap (sourceMap f g p q hpq) (restriction f g k h hk)) = leftMap q h :=
  lift_comp_leftMap _ _ _ _ _ _

@[simp] theorem forward_right :
    (forward f g k h hk p q hpq).comp
      (rightMap (sourceMap f g p q hpq) (restriction f g k h hk)) =
        targetMap f g k h hk p q hpq :=
  lift_comp_rightMap _ _ _ _ _ _

private theorem inverse_condition :
    (leftMap (sourceMap f g p q hpq) (restriction f g k h hk)).comp q =
      ((rightMap (sourceMap f g p q hpq) (restriction f g k h hk)).comp
        (rightMap f k)).comp h := by
  have H := congrArg (fun v => v.comp (rightMap f g))
    (condition (sourceMap f g p q hpq) (restriction f g k h hk))
  rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc, restriction_right,
    sourceMap, lift_comp_rightMap, ← BoundedAlgHom.comp_assoc] at H
  exact H

def inverse : BoundedAlgHom K (algebra q h)
    (algebra (sourceMap f g p q hpq) (restriction f g k h hk)) :=
  lift q h _ (leftMap (sourceMap f g p q hpq) (restriction f g k h hk))
    ((rightMap (sourceMap f g p q hpq) (restriction f g k h hk)).comp (rightMap f k))
    (inverse_condition f g k h hk p q hpq)

@[simp] theorem inverse_left :
    (inverse f g k h hk p q hpq).comp (leftMap q h) =
      leftMap (sourceMap f g p q hpq) (restriction f g k h hk) :=
  lift_comp_leftMap _ _ _ _ _ _

@[simp] theorem inverse_right :
    (inverse f g k h hk p q hpq).comp (rightMap q h) =
      (rightMap (sourceMap f g p q hpq) (restriction f g k h hk)).comp (rightMap f k) :=
  lift_comp_rightMap _ _ _ _ _ _

theorem forward_inverse :
    (forward f g k h hk p q hpq).comp (inverse f g k h hk p q hpq) =
      BoundedAlgHom.id K (algebra q h) := by
  apply hom_ext q h
  · rw [BoundedAlgHom.comp_assoc, inverse_left, forward_left, BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, inverse_right, ← BoundedAlgHom.comp_assoc,
      forward_right, targetMap_right, BoundedAlgHom.id_comp]

theorem inverse_forward :
    (inverse f g k h hk p q hpq).comp (forward f g k h hk p q hpq) =
      BoundedAlgHom.id K (algebra (sourceMap f g p q hpq) (restriction f g k h hk)) := by
  apply hom_ext (sourceMap f g p q hpq) (restriction f g k h hk)
  · rw [BoundedAlgHom.comp_assoc, forward_left, inverse_left, BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, forward_right, BoundedAlgHom.id_comp]
    apply hom_ext f k
    · rw [BoundedAlgHom.comp_assoc, targetMap_left, ← BoundedAlgHom.comp_assoc,
        inverse_left]
      have H := congrArg (fun v => v.comp (leftMap f g))
        (condition (sourceMap f g p q hpq) (restriction f g k h hk))
      rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc, restriction_left,
        sourceMap, lift_comp_leftMap] at H
      exact H
    · rw [BoundedAlgHom.comp_assoc, targetMap_right, inverse_right]

/-- The entire further base change of the induced map is the original
coefficient-algebra pushout, with both bounded inverse maps constructed. -/
def equiv : BoundedAlgEquiv K
    (algebra (sourceMap f g p q hpq) (restriction f g k h hk)) (algebra q h) :=
  BoundedAlgEquiv.ofHomInv (forward f g k h hk p q hpq) (inverse f g k h hk p q hpq)
    (fun a => congrArg (fun v => v a) (inverse_forward f g k h hk p q hpq))
    (fun b => congrArg (fun v => v b) (forward_inverse f g k h hk p q hpq))

theorem equiv_comp_right :
    (equiv f g k h hk p q hpq).toBoundedAlgHom.comp
      (rightMap (sourceMap f g p q hpq) (restriction f g k h hk)) =
        targetMap f g k h hk p q hpq := forward_right f g k h hk p q hpq

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout.LiftBaseChange
