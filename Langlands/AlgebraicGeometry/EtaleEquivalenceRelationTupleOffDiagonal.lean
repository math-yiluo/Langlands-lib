import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleUnitLocus

/-! # The affine complement of symmetric tuple units -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R]
  [IsClosedImmersion (prod.lift E.t E.s)]

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossUnit_swap (n : ℕ) :
    E.tupleSymmetricCrossUnit n ≫ E.tupleSymmetricCrossSwap n n =
      E.tupleSymmetricCrossUnit n := by
  apply E.tupleSymmetricCross_hom_ext n n <;> simp

theorem tupleSymmetricCrossSwap_mem_offDiagonal (n : ℕ)
    (x : E.tupleSymmetricCrossScheme n n)
    (hx : x ∈ E.tupleSymmetricOffDiagonalOpen n) :
    E.tupleSymmetricCrossSwap n n x ∈ E.tupleSymmetricOffDiagonalOpen n := by
  rintro ⟨y, hy⟩
  apply hx
  refine ⟨y, ?_⟩
  calc
    E.tupleSymmetricCrossUnit n y =
        E.tupleSymmetricCrossSwap n n (E.tupleSymmetricCrossUnit n y) :=
      (congrArg (fun f => f y) (E.tupleSymmetricCrossUnit_swap n)).symm
    _ = E.tupleSymmetricCrossSwap n n (E.tupleSymmetricCrossSwap n n x) := by rw [hy]
    _ = x := congrArg (fun f => f x) (E.tupleSymmetricCrossSwap_swap n n)

theorem tupleSymmetricOffDiagonalOpen_right_mem_threshold (n : ℕ)
    (x : E.tupleSymmetricCrossScheme n n)
    (hx : x ∈ E.tupleSymmetricOffDiagonalOpen n) :
    E.tupleSymmetricCrossRight n n x ∈ E.tupleSymmetricThresholdOpen n (n + 1) := by
  have h := E.tupleSymmetricOffDiagonalOpen_left_mem_threshold n
    (E.tupleSymmetricCrossSwap n n x) (E.tupleSymmetricCrossSwap_mem_offDiagonal n x hx)
  change (E.tupleSymmetricCrossSwap n n ≫ E.tupleSymmetricCrossLeft n n) x ∈
    E.tupleSymmetricThresholdOpen n (n + 1) at h
  rwa [E.tupleSymmetricCrossSwap_left] at h

/-- The affine scheme of nonidentity symmetric self-correspondences. -/
abbrev tupleSymmetricOffDiagonalScheme (n : ℕ) : Scheme.{u} :=
  (E.tupleSymmetricOffDiagonalOpen n).toScheme

/-- Inclusion of the open and closed complement of the unit. -/
abbrev tupleSymmetricOffDiagonalι (n : ℕ) :
    E.tupleSymmetricOffDiagonalScheme n ⟶ E.tupleSymmetricCrossScheme n n :=
  (E.tupleSymmetricOffDiagonalOpen n).ι

instance tupleSymmetricOffDiagonalι_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (E.tupleSymmetricOffDiagonalι n) :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (E.tupleSymmetricOffDiagonalOpen_isClopen n).isClosed)

instance tupleSymmetricOffDiagonalScheme_isAffine (n : ℕ) :
    IsAffine (E.tupleSymmetricOffDiagonalScheme n) :=
  isAffine_of_isAffineHom (E.tupleSymmetricOffDiagonalι n)

/-- Restriction of endpoint exchange to the complement of the unit. -/
def tupleSymmetricOffDiagonalSwap (n : ℕ) :
    E.tupleSymmetricOffDiagonalScheme n ⟶ E.tupleSymmetricOffDiagonalScheme n :=
  IsOpenImmersion.lift (E.tupleSymmetricOffDiagonalι n)
    (E.tupleSymmetricOffDiagonalι n ≫ E.tupleSymmetricCrossSwap n n) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact E.tupleSymmetricCrossSwap_mem_offDiagonal n x.1 x.2)

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalSwap_ι (n : ℕ) :
    E.tupleSymmetricOffDiagonalSwap n ≫ E.tupleSymmetricOffDiagonalι n =
      E.tupleSymmetricOffDiagonalι n ≫ E.tupleSymmetricCrossSwap n n :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalSwap_swap (n : ℕ) :
    E.tupleSymmetricOffDiagonalSwap n ≫ E.tupleSymmetricOffDiagonalSwap n = 𝟙 _ := by
  apply (cancel_mono (E.tupleSymmetricOffDiagonalι n)).mp
  simp

/-- The left endpoint of a nonidentity self-correspondence, factored through
the next symmetric threshold open. -/
def tupleSymmetricOffDiagonalLeft (n : ℕ) :
    E.tupleSymmetricOffDiagonalScheme n ⟶
      (E.tupleSymmetricThresholdOpen n (n + 1)).toScheme :=
  IsOpenImmersion.lift (E.tupleSymmetricThresholdOpen n (n + 1)).ι
    (E.tupleSymmetricOffDiagonalι n ≫ E.tupleSymmetricCrossLeft n n) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact E.tupleSymmetricOffDiagonalOpen_left_mem_threshold n x.1 x.2)

/-- The right endpoint of a nonidentity self-correspondence, factored through
the next symmetric threshold open. -/
def tupleSymmetricOffDiagonalRight (n : ℕ) :
    E.tupleSymmetricOffDiagonalScheme n ⟶
      (E.tupleSymmetricThresholdOpen n (n + 1)).toScheme :=
  IsOpenImmersion.lift (E.tupleSymmetricThresholdOpen n (n + 1)).ι
    (E.tupleSymmetricOffDiagonalι n ≫ E.tupleSymmetricCrossRight n n) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact E.tupleSymmetricOffDiagonalOpen_right_mem_threshold n x.1 x.2)

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalLeft_ι (n : ℕ) :
    E.tupleSymmetricOffDiagonalLeft n ≫ (E.tupleSymmetricThresholdOpen n (n + 1)).ι =
      E.tupleSymmetricOffDiagonalι n ≫ E.tupleSymmetricCrossLeft n n :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalRight_ι (n : ℕ) :
    E.tupleSymmetricOffDiagonalRight n ≫ (E.tupleSymmetricThresholdOpen n (n + 1)).ι =
      E.tupleSymmetricOffDiagonalι n ≫ E.tupleSymmetricCrossRight n n :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalSwap_left (n : ℕ) :
    E.tupleSymmetricOffDiagonalSwap n ≫ E.tupleSymmetricOffDiagonalLeft n =
      E.tupleSymmetricOffDiagonalRight n := by
  apply (cancel_mono (E.tupleSymmetricThresholdOpen n (n + 1)).ι).mp
  simp

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalSwap_right (n : ℕ) :
    E.tupleSymmetricOffDiagonalSwap n ≫ E.tupleSymmetricOffDiagonalRight n =
      E.tupleSymmetricOffDiagonalLeft n := by
  apply (cancel_mono (E.tupleSymmetricThresholdOpen n (n + 1)).ι).mp
  simp

/-- The unit and its affine open complement present the whole
self-correspondence as their disjoint union. -/
def tupleSymmetricUnitOffDiagonalIsColimit (n : ℕ) :
    IsColimit (BinaryCofan.mk (E.tupleSymmetricCrossUnit n)
      (E.tupleSymmetricOffDiagonalι n)) :=
  (nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (by
    rw [Scheme.Opens.opensRange_ι, isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor <;> ext x <;> simp [tupleSymmetricOffDiagonalOpen,
      tupleSymmetricUnitOpen])).some

/-- The resulting canonical decomposition into units and nonidentity arrows. -/
def tupleSymmetricUnitOffDiagonalIso (n : ℕ) :
    E.tupleSymmetricScheme n ⨿ E.tupleSymmetricOffDiagonalScheme n ≅
      E.tupleSymmetricCrossScheme n n :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (E.tupleSymmetricUnitOffDiagonalIsColimit n)

@[reassoc (attr := simp)]
theorem tupleSymmetricUnitOffDiagonalIso_inl (n : ℕ) :
    coprod.inl ≫ (E.tupleSymmetricUnitOffDiagonalIso n).hom =
      E.tupleSymmetricCrossUnit n := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod _ _)
    (E.tupleSymmetricUnitOffDiagonalIsColimit n) (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)]
theorem tupleSymmetricUnitOffDiagonalIso_inr (n : ℕ) :
    coprod.inr ≫ (E.tupleSymmetricUnitOffDiagonalIso n).hom =
      E.tupleSymmetricOffDiagonalι n := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod _ _)
    (E.tupleSymmetricUnitOffDiagonalIsColimit n) (Discrete.mk WalkingPair.right)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
