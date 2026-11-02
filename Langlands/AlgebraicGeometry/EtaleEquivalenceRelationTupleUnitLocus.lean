import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleReducedLocus
import Langlands.AlgebraicGeometry.FiniteEtaleSourceUnramified

/-! # Open units in symmetric tuple cross-correspondences -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- A section of a morphism with open diagonal is an open immersion. -/
theorem isOpenImmersion_section_of_open_diagonal {X S : Scheme.{u}}
    (p : X ⟶ S) (s : S ⟶ X) (hs : s ≫ p = 𝟙 S)
    [IsOpenImmersion (pullback.diagonal p)] : IsOpenImmersion s := by
  let g : X ⟶ pullback p p :=
    pullback.lift (𝟙 X) (p ≫ s) (by simp [Category.assoc, hs])
  have hp : IsPullback s s (pullback.diagonal p) g := by
    refine IsPullback.mk' ?_ ?_ ?_
    · apply pullback.hom_ext
      · simp [g, Category.assoc]
      · dsimp only [g]
        simp only [Category.assoc, pullback.diagonal_snd, pullback.lift_snd, Category.comp_id]
        rw [← Category.assoc, hs, Category.id_comp]
    · intro T a b hab _
      have h := congrArg (· ≫ p) hab
      simpa [Category.assoc, hs] using h
    · intro T a b hab
      have hf : a = b := by
        simpa [g] using congrArg (· ≫ pullback.fst p p) hab
      have he : a = (b ≫ p) ≫ s := by
        simpa [g, Category.assoc] using congrArg (· ≫ pullback.snd p p) hab
      exact ⟨b ≫ p, he.symm, he.symm.trans hf⟩
  exact MorphismProperty.of_isPullback hp inferInstance

namespace EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R]

instance tupleSymmetricCrossLeft_diagonal_isOpenImmersion (m n : ℕ) :
    IsOpenImmersion (pullback.diagonal (E.tupleSymmetricCrossLeft m n)) := by
  have : Etale (E.tupleSymmetricCrossMap m n ≫
      E.tupleSymmetricCrossLeft m n) := by
    rw [E.tupleSymmetricCrossMap_left]
    infer_instance
  exact isOpenImmersion_diagonal_of_surjective_etale_comp
    (E.tupleSymmetricCrossMap m n) (E.tupleSymmetricCrossLeft m n)

instance tupleSymmetricCrossRight_diagonal_isOpenImmersion (m n : ℕ) :
    IsOpenImmersion (pullback.diagonal (E.tupleSymmetricCrossRight m n)) := by
  have : Etale (E.tupleSymmetricCrossMap m n ≫
      E.tupleSymmetricCrossRight m n) := by
    rw [E.tupleSymmetricCrossMap_right]
    infer_instance
  exact isOpenImmersion_diagonal_of_surjective_etale_comp
    (E.tupleSymmetricCrossMap m n) (E.tupleSymmetricCrossRight m n)

instance tupleSymmetricCrossLeft_formallyUnramified (m n : ℕ) :
    FormallyUnramified (E.tupleSymmetricCrossLeft m n) := inferInstance

instance tupleSymmetricCrossRight_formallyUnramified (m n : ℕ) :
    FormallyUnramified (E.tupleSymmetricCrossRight m n) := inferInstance

variable [IsClosedImmersion (prod.lift E.t E.s)]

instance tupleSymmetricCrossUnit_isOpenImmersion (n : ℕ) :
    IsOpenImmersion (E.tupleSymmetricCrossUnit n) :=
  isOpenImmersion_section_of_open_diagonal (E.tupleSymmetricCrossLeft n n)
    (E.tupleSymmetricCrossUnit n) (E.tupleSymmetricCrossUnit_left n)

instance tupleSymmetricCrossUnit_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (E.tupleSymmetricCrossUnit n) := by
  have h : E.tupleSymmetricCrossUnit n ≫
      prod.lift (E.tupleSymmetricCrossLeft n n) (E.tupleSymmetricCrossRight n n) =
      prod.lift (𝟙 _) (𝟙 _) := by
    apply prod.hom_ext <;> simp
  have : IsClosedImmersion (E.tupleSymmetricCrossUnit n ≫
      prod.lift (E.tupleSymmetricCrossLeft n n) (E.tupleSymmetricCrossRight n n)) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (E.tupleSymmetricCrossUnit n)
    (prod.lift (E.tupleSymmetricCrossLeft n n) (E.tupleSymmetricCrossRight n n))

/-- The open image of the unit in the symmetric self-correspondence. -/
def tupleSymmetricUnitOpen (n : ℕ) : (E.tupleSymmetricCrossScheme n n).Opens :=
  ⟨Set.range (E.tupleSymmetricCrossUnit n),
    (E.tupleSymmetricCrossUnit n).isOpenEmbedding.isOpen_range⟩

theorem tupleSymmetricUnitOpen_isClopen (n : ℕ) :
    IsClopen (E.tupleSymmetricUnitOpen n : Set (E.tupleSymmetricCrossScheme n n)) :=
  ⟨(E.tupleSymmetricCrossUnit n).isClosedEmbedding.isClosed_range,
    (E.tupleSymmetricUnitOpen n).isOpen⟩

/-- The open complement of the unit, consisting of nonidentity cross arrows. -/
def tupleSymmetricOffDiagonalOpen (n : ℕ) :
    (E.tupleSymmetricCrossScheme n n).Opens :=
  ⟨(E.tupleSymmetricUnitOpen n : Set (E.tupleSymmetricCrossScheme n n))ᶜ,
    (E.tupleSymmetricUnitOpen_isClopen n).isClosed.isOpen_compl⟩

theorem tupleSymmetricOffDiagonalOpen_isClopen (n : ℕ) :
    IsClopen (E.tupleSymmetricOffDiagonalOpen n :
      Set (E.tupleSymmetricCrossScheme n n)) :=
  (E.tupleSymmetricUnitOpen_isClopen n).compl

theorem tupleSymmetricOffDiagonalOpen_isCompact (n : ℕ) :
    IsCompact (E.tupleSymmetricOffDiagonalOpen n :
      Set (E.tupleSymmetricCrossScheme n n)) :=
  (E.tupleSymmetricOffDiagonalOpen_isClopen n).isClosed.isCompact

/-- Every nonidentity self-correspondence lies over the next degree threshold. -/
theorem tupleSymmetricOffDiagonalOpen_left_mem_threshold (n : ℕ)
    (x : E.tupleSymmetricCrossScheme n n)
    (hx : x ∈ E.tupleSymmetricOffDiagonalOpen n) :
    E.tupleSymmetricCrossLeft n n x ∈ E.tupleSymmetricThresholdOpen n (n + 1) := by
  by_contra h
  exact hx (E.tupleSymmetricCross_point_mem_unit_range n x h)

end EtaleEquivalenceRelation
end Langlands.AlgebraicGeometry
