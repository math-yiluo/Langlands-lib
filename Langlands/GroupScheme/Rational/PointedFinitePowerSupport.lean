import Langlands.GroupScheme.Rational.PointedProductSupport
import Langlands.GroupScheme.ImageGenerationActions

/-! # Actual pointed finite powers and augmentation support -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {B : Scheme.{u}}

/-- The empty actual finite power is the terminal object over the base. -/
def finitePowerZeroIso (V : Over B) :
    finitePower V 0 ≅ 𝟙_ (Over B) where
  hom := toUnit _
  inv := Pi.lift fun i : Fin 0 => i.elim0
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    exact i.elim0
  inv_hom_id := toUnit_unique _ _

/-- Separate the first coordinate of the existing actual finite power. -/
def finitePowerSuccIso (V : Over B) (n : ℕ) :
    finitePower V (n + 1) ≅ V ⊗ finitePower V n where
  hom := lift (Pi.π (fun _ : Fin (n + 1) => V) 0)
    (Pi.lift fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => V) i.succ)
  inv := Pi.lift (Fin.cases (fst V (finitePower V n))
    (fun i : Fin n => snd V (finitePower V n) ≫ Pi.π (fun _ : Fin n => V) i))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply Pi.hom_ext
      intro i
      simp

namespace PointedCoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V : Over (Spec (CommRingCat.of k))}

instance finitePower_isAffineHom [IsAffineHom V.hom] (n : ℕ) :
    IsAffineHom (finitePower V n).hom := by
  induction n with
  | zero =>
      let e := finitePowerZeroIso V
      let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
      rw [← e.hom.w]
      change IsAffineHom (e.hom.left ≫ 𝟙 _)
      infer_instance
  | succ n ih =>
      let : IsAffineHom (finitePower V n).hom := ih
      let e := finitePowerSuccIso V n
      let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
      rw [← e.hom.w]
      infer_instance

namespace PointedAction

/-- Forget the distinguished fixed point, retaining the same action morphism. -/
def toPointwiseSchemeAction (a : PointedAction S V) : PointwiseSchemeAction S.toGrp V where
  hom := a.hom
  one_left := a.one_left
  mul_left := a.mul_left

@[simp] theorem toPointwiseSchemeAction_act (a : PointedAction S V)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (v : T ⟶ V) :
    a.toPointwiseSchemeAction.act s v = a.act s v := rfl

/-- The pointed diagonal action on the existing actual finite power. -/
def finitePower (a : PointedAction S V) (n : ℕ) :
    PointedAction S (GroupScheme.finitePower V n) where
  hom := (a.toPointwiseSchemeAction.finitePower n).hom
  origin := Pi.lift fun _ : Fin n => a.origin
  one_left := (a.toPointwiseSchemeAction.finitePower n).one_left
  mul_left := (a.toPointwiseSchemeAction.finitePower n).mul_left
  origin_fixed s := by
    apply Pi.hom_ext
    intro i
    change (a.toPointwiseSchemeAction.finitePower n).act s _ ≫ _ = _
    rw [a.toPointwiseSchemeAction.finitePower_act_π]
    simp only [Category.assoc, Pi.lift_comp_π, toPointwiseSchemeAction_act, act_origin]

@[simp] theorem finitePower_toPointwiseSchemeAction (a : PointedAction S V) (n : ℕ) :
    (a.finitePower n).toPointwiseSchemeAction = a.toPointwiseSchemeAction.finitePower n := rfl

theorem finitePower_act_π (a : PointedAction S V) (n : ℕ)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X)
    (v : T ⟶ GroupScheme.finitePower V n) (i : Fin n) :
    (a.finitePower n).act s v ≫ Pi.π (fun _ : Fin n => V) i =
      a.act s (v ≫ Pi.π (fun _ : Fin n => V) i) :=
  a.toPointwiseSchemeAction.finitePower_act_π n s v i

@[simp] theorem finitePower_origin_π (a : PointedAction S V) (n : ℕ) (i : Fin n) :
    (a.finitePower n).origin ≫ Pi.π (fun _ : Fin n => V) i = a.origin :=
  Pi.lift_comp_π _ i

end PointedAction

theorem finitePowerSuccIso_isPointedEquivariant (a : PointedAction S V) (n : ℕ) :
    IsPointedEquivariant (a.finitePower (n + 1)) (a.prod (a.finitePower n))
      (finitePowerSuccIso V n).hom := by
  constructor
  · intro T s v
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, finitePowerSuccIso, lift_fst, PointedAction.prod_act_fst]
      exact a.finitePower_act_π (n + 1) s v 0
    · apply Pi.hom_ext
      intro i
      simp only [Category.assoc, finitePowerSuccIso, lift_snd, Pi.lift_comp_π,
        PointedAction.prod_act_snd, PointedAction.finitePower_act_π]
  · apply CartesianMonoidalCategory.hom_ext
    · simp [finitePowerSuccIso, PointedAction.prod]
    · apply Pi.hom_ext
      intro i
      simp [finitePowerSuccIso, PointedAction.prod]

variable [IsAffineHom V.hom]

/-- The augmentation of an empty actual finite power is zero. -/
theorem finitePower_zero_augmentation_eq_zero (a : PointedAction S V)
    (z : augmentation (a.finitePower 0)) : z = 0 := by
  have he : universalPoint (GroupScheme.finitePower V 0) =
      toUnit _ ≫ (a.finitePower 0).origin := by
    apply Pi.hom_ext
    intro i
    exact i.elim0
  have hc := congrArg (fun p : Points (GroupScheme.finitePower V 0)
      (Coord (GroupScheme.finitePower V 0)) =>
    (pointCoordinates p) (z : Coord (GroupScheme.finitePower V 0))) he
  rw [coordinates_universalPoint, pointCoordinates_origin] at hc
  apply Subtype.ext
  change (z : Coord (GroupScheme.finitePower V 0)) = 0
  change (z : Coord (GroupScheme.finitePower V 0)) =
    algebraMap k (Coord (GroupScheme.finitePower V 0))
      (coordinateOrigin (a.finitePower 0) z) at hc
  have hz : coordinateOrigin (a.finitePower 0) (z : Coord (GroupScheme.finitePower V 0)) = 0 :=
    z.property
  rw [hz, map_zero] at hc
  exact hc

@[simp] theorem finitePower_zero_support (a : PointedAction S V) :
    support (a.finitePower 0) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro χ ⟨z, hz, _⟩
  exact hz (finitePower_zero_augmentation_eq_zero a z)

/-- Actual finite powers preserve augmentation support inside any additive
subsemigroup, including one that does not contain zero. -/
theorem finitePower_support_subset_semigroup_of_split
    (hS : IsSplitTorus S.toGrp) (a : PointedAction S V)
    (P : AddSubsemigroup (characterLattice S)) (hP : support a ⊆ P) (n : ℕ) :
    support (a.finitePower n) ⊆ P := by
  induction n with
  | zero => simp only [finitePower_zero_support, Set.empty_subset]
  | succ n ih =>
      rw [support_eq_of_iso (a.finitePower (n + 1)) (a.prod (a.finitePower n))
        (finitePowerSuccIso V n) (finitePowerSuccIso_isPointedEquivariant a n)]
      exact product_support_subset_semigroup_of_split hS a (a.finitePower n) P hP ih

end PointedCoordinateWeights

end Langlands.GroupScheme
