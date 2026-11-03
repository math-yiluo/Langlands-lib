import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackProofs
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Products of actual scheme point spaces -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

/-- The actual relative product has the product topology on its points. -/
def schemeProductPointHomeomorph (X Y : Over (Spec (CommRingCat.of R))) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R (X ⊗ Y) S) :=
      schemePointTopology R (X ⊗ Y) S
    RingPoint R (X ⊗ Y) S ≃ₜ (RingPoint R X S × RingPoint R Y S) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R (X ⊗ Y) S) :=
    schemePointTopology R (X ⊗ Y) S
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let t : IsTerminal Z := Over.mkIdTerminal
  let f : X ⟶ Z := t.from X
  let g : Y ⟶ Z := t.from Y
  have hpb : IsPullback (fst X Y) (snd X Y) f g :=
    IsPullback.of_is_product (tensorProductIsBinaryProduct X Y) t
  let c : PullbackCone f g := PullbackCone.mk (fst X Y) (snd X Y) hpb.w
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  let H := schemePullbackPointHomeomorph R S c hpb.isLimit
  let K :
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} ≃ₜ
        (RingPoint R X S × RingPoint R Y S) :=
    { toFun := Subtype.val
      invFun := fun q => ⟨q, t.hom_ext _ _⟩
      left_inv := fun q => Subtype.ext rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  exact H.trans K

@[simp] theorem schemeProductPointHomeomorph_apply
    (X Y : Over (Spec (CommRingCat.of R))) (p : RingPoint R (X ⊗ Y) S) :
    schemeProductPointHomeomorph R S X Y p = (p ≫ fst X Y, p ≫ snd X Y) := rfl

@[simp] theorem schemeProductPointHomeomorph_symm_apply
    (X Y : Over (Spec (CommRingCat.of R))) (q : RingPoint R X S × RingPoint R Y S) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R (X ⊗ Y) S) :=
      schemePointTopology R (X ⊗ Y) S
    (schemeProductPointHomeomorph R S X Y).symm q = lift q.1 q.2 := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R (X ⊗ Y) S) :=
    schemePointTopology R (X ⊗ Y) S
  apply (schemeProductPointHomeomorph R S X Y).injective
  rw [Homeomorph.apply_symm_apply]
  change q = (lift q.1 q.2 ≫ fst X Y, lift q.1 q.2 ≫ snd X Y)
  exact (Prod.ext (lift_fst _ _) (lift_snd _ _)).symm

/-- Pairing actual points is continuous for the canonical scheme point topologies. -/
theorem continuous_schemePointPair (X Y : Over (Spec (CommRingCat.of R))) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R (X ⊗ Y) S) :=
      schemePointTopology R (X ⊗ Y) S
    Continuous (X := RingPoint R X S × RingPoint R Y S)
      (Y := RingPoint R (X ⊗ Y) S) (fun q => lift q.1 q.2) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R (X ⊗ Y) S) :=
    schemePointTopology R (X ⊗ Y) S
  have h : ⇑(schemeProductPointHomeomorph R S X Y).symm =
      (fun q : RingPoint R X S × RingPoint R Y S => lift q.1 q.2) :=
    funext (schemeProductPointHomeomorph_symm_apply R S X Y)
  exact h ▸ (schemeProductPointHomeomorph R S X Y).symm.continuous

end Langlands.AlgebraicGeometry.PointTopology
