import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionPieces
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-! # Actual field sections of the arbitrary smooth dimension pieces -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces

variable {K : Type u} [Field K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  (hX : SmoothOverBase X)
  {L : Type u} [Field L] [Algebra K L]

/-- The intrinsic dimension selected by an actual field-valued section. -/
def fieldPointDimension (x : RingPoints K X L) : ℕ :=
  pointDimension hX (chartPointMap (uliftYonedaEquiv.symm x)
    (IsLocalRing.closedPoint L))

/-- The original section as a section of its genuine open dimension piece. -/
def fieldPointFactor (x : RingPoints K X L) :
    RingPoints K (space hX (fieldPointDimension hX x)) L := by
  refine ⟨x, ?_⟩
  intro t
  change pointDimension hX (chartPointMap (uliftYonedaEquiv.symm x) t) =
    pointDimension hX (chartPointMap (uliftYonedaEquiv.symm x)
      (IsLocalRing.closedPoint L))
  rw [Subsingleton.elim t (IsLocalRing.closedPoint L)]

@[simp]
theorem fieldPointFactor_map (x : RingPoints K X L) :
    RingPoints.map (inclusion hX (fieldPointDimension hX x))
      (fieldPointFactor hX x) = x := rfl

/-- The actual inclusion reads the dimension of its piece at every field section. -/
@[simp]
theorem fieldPointDimension_map_inclusion (n : ℕ)
    (y : RingPoints K (space hX n) L) :
    fieldPointDimension hX (RingPoints.map (inclusion hX n) y) = n :=
  y.property (IsLocalRing.closedPoint L)

/-- Inclusion is injective on actual sections, including sections of empty pieces. -/
theorem fieldPointInclusion_injective (n : ℕ) :
    Function.Injective
      (RingPoints.map (inclusion hX n) :
        RingPoints K (space hX n) L → RingPoints K X L) := by
  intro y z h
  exact Subtype.ext h

/-- Any actual factorization has the intrinsic dimension selected by the section. -/
theorem fieldPointDimension_eq_of_factor {n : ℕ}
    (y : RingPoints K (space hX n) L) (x : RingPoints K X L)
    (hy : RingPoints.map (inclusion hX n) y = x) :
    n = fieldPointDimension hX x := by
  rw [← hy, fieldPointDimension_map_inclusion]

/-- Every field section factors through exactly one natural-number dimension. -/
theorem existsUnique_fieldPointFactor (x : RingPoints K X L) :
    ∃! n : ℕ, ∃ y : RingPoints K (space hX n) L,
      RingPoints.map (inclusion hX n) y = x := by
  refine ⟨fieldPointDimension hX x, ⟨fieldPointFactor hX x, rfl⟩, ?_⟩
  rintro n ⟨y, hy⟩
  exact fieldPointDimension_eq_of_factor hX y x hy

/-- Reassemble a section using the actual inclusion of its dimension piece. -/
def fieldPointAssembly :
    (Σ n : ℕ, RingPoints K (space hX n) L) → RingPoints K X L :=
  fun y => RingPoints.map (inclusion hX y.1) y.2

@[simp]
theorem fieldPointAssembly_mk (n : ℕ) (y : RingPoints K (space hX n) L) :
    fieldPointAssembly hX ⟨n, y⟩ = RingPoints.map (inclusion hX n) y := rfl

theorem fieldPointAssembly_injective :
    Function.Injective (fieldPointAssembly hX :
      (Σ n : ℕ, RingPoints K (space hX n) L) → RingPoints K X L) := by
  rintro ⟨n, y⟩ ⟨m, z⟩ h
  have hn : n = m := by
    rw [← fieldPointDimension_map_inclusion hX n y,
      ← fieldPointDimension_map_inclusion hX m z]
    exact congrArg (fieldPointDimension hX) h
  subst m
  have hy : y = z := fieldPointInclusion_injective hX n h
  cases hy
  rfl

/-- Actual field sections are the dependent sum of sections of all dimension pieces. -/
def fieldPointEquiv :
    RingPoints K X L ≃ Σ n : ℕ, RingPoints K (space hX n) L where
  toFun x := ⟨fieldPointDimension hX x, fieldPointFactor hX x⟩
  invFun := fieldPointAssembly hX
  left_inv _ := rfl
  right_inv y := by
    apply fieldPointAssembly_injective hX
    rfl

@[simp]
theorem fieldPointEquiv_apply (x : RingPoints K X L) :
    fieldPointEquiv hX x = ⟨fieldPointDimension hX x, fieldPointFactor hX x⟩ := rfl

/-- The inverse equivalence is precisely the actual inclusion-induced section map. -/
@[simp]
theorem fieldPointEquiv_symm_apply (n : ℕ)
    (y : RingPoints K (space hX n) L) :
    (fieldPointEquiv hX).symm ⟨n, y⟩ = RingPoints.map (inclusion hX n) y := rfl

theorem fieldPointEquiv_left_inv (x : RingPoints K X L) :
    (fieldPointEquiv hX).symm (fieldPointEquiv hX x) = x :=
  (fieldPointEquiv hX).symm_apply_apply x

theorem fieldPointEquiv_right_inv (y : Σ n : ℕ, RingPoints K (space hX n) L) :
    fieldPointEquiv hX ((fieldPointEquiv hX).symm y) = y :=
  (fieldPointEquiv hX).apply_symm_apply y

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces
