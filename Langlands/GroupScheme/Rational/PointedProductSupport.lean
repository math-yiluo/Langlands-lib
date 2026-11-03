import Langlands.GroupScheme.Rational.AffineCommutatorImageSupport
import Langlands.GroupScheme.Rational.CoordinateTensorSupport
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof

/-! # Augmentation support of actual pointed products -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Classical
open scoped TensorProduct

namespace Langlands.GroupScheme.PointedCoordinateWeights

open RelativeRoot.AugmentedTensor

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W : Over (Spec (CommRingCat.of k))}

namespace PointedAction

/-- The actual slice with the first coordinate at its distinguished point. -/
def leftSlice (a : PointedAction S V) : W ⟶ V ⊗ W :=
  lift (toUnit W ≫ a.origin) (𝟙 W)

/-- The actual slice with the second coordinate at its distinguished point. -/
def rightSlice (b : PointedAction S W) : V ⟶ V ⊗ W :=
  lift (𝟙 V) (toUnit V ≫ b.origin)

end PointedAction

theorem leftSlice_isPointedEquivariant (a : PointedAction S V) (b : PointedAction S W) :
    IsPointedEquivariant b (a.prod b) a.leftSlice := by
  constructor
  · intro T s w
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [PointedAction.leftSlice]
  · simp [PointedAction.leftSlice, PointedAction.prod, comp_lift]

theorem rightSlice_isPointedEquivariant (a : PointedAction S V) (b : PointedAction S W) :
    IsPointedEquivariant a (a.prod b) b.rightSlice := by
  constructor
  · intro T s v
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [PointedAction.rightSlice]
  · simp [PointedAction.rightSlice, PointedAction.prod, comp_lift]

variable [IsAffineHom V.hom] [IsAffineHom W.hom]

/-- A product augmentation weight comes from one factor or the sum of one
augmentation weight from each factor. No zero character is adjoined. -/
theorem product_support_subset
    (a : PointedAction S V) (b : PointedAction S W)
    (ha : DirectSum.IsInternal (augmentationWeightSpace a))
    (hb : DirectSum.IsInternal (augmentationWeightSpace b))
    (hprod : DirectSum.IsInternal (weightSpace (a.prod b))) :
    support (a.prod b) ⊆
      support a ∪ support b ∪ Set.image2 (· + ·) (support a) (support b) := by
  rintro χ ⟨z, hz, hχ⟩
  let zl := augmentationPullback b (a.prod b) a.leftSlice
    (leftSlice_isPointedEquivariant a b) z
  let zr := augmentationPullback a (a.prod b) b.rightSlice
    (rightSlice_isPointedEquivariant a b) z
  by_cases hl : zl = 0
  · by_cases hr : zr = 0
    · apply Or.inr
      apply weight_mem_sum_of_identity_slices a b ha hb hprod
        (z := (tensorCoordinates (V := V) (W := W)) z)
      · intro he
        apply hz
        apply Subtype.ext
        exact (tensorCoordinates (V := V) (W := W)).injective
          (he.trans (map_zero _).symm)
      · exact ⟨z, hχ, rfl⟩
      · have he := DFunLike.congr_fun
          (tensorCoordinates_leftIdentitySlice (W := W) a) (z : Coord (V ⊗ W))
        change leftIdentitySlice (coordinateOrigin a) (Coord W)
          ((tensorCoordinates (V := V) (W := W)) z) = 0
        exact he.trans (congrArg (fun q : augmentation b => (q : Coord W)) hl)
      · have he := DFunLike.congr_fun
          (tensorCoordinates_rightIdentitySlice (V := V) b) (z : Coord (V ⊗ W))
        change rightIdentitySlice (Coord V) (coordinateOrigin b)
          ((tensorCoordinates (V := V) (W := W)) z) = 0
        exact he.trans (congrArg (fun q : augmentation a => (q : Coord V)) hr)
    · exact Or.inl (Or.inl ⟨zr, hr,
        augmentationPullback_mem a (a.prod b) b.rightSlice
          (rightSlice_isPointedEquivariant a b) χ hχ⟩)
  · exact Or.inl (Or.inr ⟨zl, hl,
      augmentationPullback_mem b (a.prod b) a.leftSlice
        (leftSlice_isPointedEquivariant a b) χ hχ⟩)

/-- An additive subsemigroup containing both factor supports contains the
augmentation support of their actual product. -/
theorem product_support_subset_semigroup
    (a : PointedAction S V) (b : PointedAction S W)
    (ha : DirectSum.IsInternal (augmentationWeightSpace a))
    (hb : DirectSum.IsInternal (augmentationWeightSpace b))
    (hprod : DirectSum.IsInternal (weightSpace (a.prod b)))
    (P : AddSubsemigroup (characterLattice S))
    (hPa : support a ⊆ P) (hPb : support b ⊆ P) :
    support (a.prod b) ⊆ P := by
  intro χ hχ
  rcases product_support_subset a b ha hb hprod hχ with (h | h) | h
  · exact hPa h
  · exact hPb h
  · obtain ⟨α, hα, β, hβ, rfl⟩ := h
    exact P.add_mem (hPa hα) (hPb hβ)

/-- The product support bound for actual split tori needs no decomposition
premises and preserves an arbitrary additive subsemigroup. -/
theorem product_support_subset_semigroup_of_split
    (hS : IsSplitTorus S.toGrp) (a : PointedAction S V) (b : PointedAction S W)
    (P : AddSubsemigroup (characterLattice S))
    (hPa : support a ⊆ P) (hPb : support b ⊆ P) :
    support (a.prod b) ⊆ P := by
  exact product_support_subset_semigroup a b
    (pointedCoordinateDecomposition k S hS V a).2
    (pointedCoordinateDecomposition k S hS W b).2
    (pointedCoordinateDecomposition k S hS (V ⊗ W) (a.prod b)).1 P hPa hPb

end Langlands.GroupScheme.PointedCoordinateWeights
