import Langlands.ClassField.Global.InfinitePlaceLattice
import Langlands.ClassField.Global.FullLogGaloisAction

/-! # The canonical infinite-place lattice inside full real coordinates -/

noncomputable section

open NumberField
open scoped Classical

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [NumberField E]

/-- The integer coordinate lattice in the full real logarithmic coordinate space. -/
def infinitePlaceCoordinateLattice : Submodule ℤ (InfinitePlace E → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (InfinitePlace E)))

instance : DiscreteTopology (infinitePlaceCoordinateLattice E) := by
  unfold infinitePlaceCoordinateLattice
  infer_instance

instance : IsZLattice ℝ (infinitePlaceCoordinateLattice E) := by
  unfold infinitePlaceCoordinateLattice
  infer_instance

/-- Membership means that every real coordinate is an integer. -/
theorem mem_infinitePlaceCoordinateLattice_iff (x : InfinitePlace E → ℝ) :
    x ∈ infinitePlaceCoordinateLattice E ↔ ∀ w, ∃ z : ℤ, (z : ℝ) = x w := by
  simpa [infinitePlaceCoordinateLattice] using
    (Pi.basisFun ℝ (InfinitePlace E)).mem_span_iff_repr_mem ℤ x

theorem infinitePlaceCoordinateLattice_span :
    Submodule.span ℝ (infinitePlaceCoordinateLattice E : Set (InfinitePlace E → ℝ)) = ⊤ :=
  IsZLattice.span_top

/-- Integer coordinates identify the embedded lattice with ordinary integer functions. -/
def infinitePlaceCoordinateIntegerEquiv :
    infinitePlaceCoordinateLattice E ≃ₗ[ℤ] (InfinitePlace E → ℤ) :=
  ((Pi.basisFun ℝ (InfinitePlace E)).restrictScalars ℤ).repr.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (InfinitePlace E))

@[simp] theorem infinitePlaceCoordinateIntegerEquiv_cast
    (x : infinitePlaceCoordinateLattice E) (w : InfinitePlace E) :
    (infinitePlaceCoordinateIntegerEquiv E x w : ℝ) = (x : InfinitePlace E → ℝ) w := by
  change ((((Pi.basisFun ℝ (InfinitePlace E)).restrictScalars ℤ).repr x w : ℤ) : ℝ) = _
  simpa using
    (Pi.basisFun ℝ (InfinitePlace E)).restrictScalars_repr_apply ℤ x w

@[simp] theorem infinitePlaceCoordinateIntegerEquiv_symm_apply
    (x : InfinitePlace E → ℤ) (w : InfinitePlace E) :
    ((infinitePlaceCoordinateIntegerEquiv E).symm x : InfinitePlace E → ℝ) w =
      (x w : ℝ) := by
  rw [← infinitePlaceCoordinateIntegerEquiv_cast]
  simp

variable [Algebra F E]

/-- The existing canonical permutation module, realized as a full real-coordinate lattice. -/
def infinitePlaceLatticeRealization :
    (infinitePlaceLatticeRepresentation F E).V ≃ₗ[ℤ] infinitePlaceCoordinateLattice E :=
  ((infinitePlaceLatticeFunctionEquiv F E).restrictScalars ℤ).trans
    ((LinearEquiv.piCongrRight (fun _ : InfinitePlace E =>
      (ULift.moduleEquiv : NormalizedTwoCocycle.CoefficientScalars.{v} ≃ₗ[ℤ] ℤ))).trans
        (infinitePlaceCoordinateIntegerEquiv E).symm)

@[simp] theorem infinitePlaceLatticeRealization_apply
    (x : (infinitePlaceLatticeRepresentation F E).V) (w : InfinitePlace E) :
    (infinitePlaceLatticeRealization F E x : InfinitePlace E → ℝ) w =
      ((x.coeff w).down : ℝ) := by
  simp only [infinitePlaceLatticeRealization, LinearEquiv.trans_apply,
    infinitePlaceCoordinateIntegerEquiv_symm_apply, LinearEquiv.piCongrRight_apply,
    ULift.moduleEquiv_apply, LinearEquiv.restrictScalars_apply]
  rfl

/-- The real permutation action preserves the embedded integer lattice. -/
theorem infinitePlaceCoordinateLattice_invariant (g : E ≃ₐ[F] E)
    (x : InfinitePlace E → ℝ) (hx : x ∈ infinitePlaceCoordinateLattice E) :
    fullLogPermutation F E g x ∈ infinitePlaceCoordinateLattice E := by
  rw [mem_infinitePlaceCoordinateLattice_iff] at hx ⊢
  intro w
  exact hx (g⁻¹ • w)

/-- Restrict the actual arithmetic action to the coordinate lattice. -/
def infinitePlaceCoordinateLatticeAut : (E ≃ₐ[F] E) →*
    (infinitePlaceCoordinateLattice E ≃ₗ[ℤ] infinitePlaceCoordinateLattice E) where
  toFun g :=
    { toFun := fun x => ⟨fullLogPermutation F E g x,
        infinitePlaceCoordinateLattice_invariant F E g x x.2⟩
      invFun := fun x => ⟨fullLogPermutation F E g⁻¹ x,
        infinitePlaceCoordinateLattice_invariant F E g⁻¹ x x.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_zsmul _ _ _ }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem infinitePlaceCoordinateLatticeAut_apply (g : E ≃ₐ[F] E)
    (x : infinitePlaceCoordinateLattice E) :
    (infinitePlaceCoordinateLatticeAut F E g x : InfinitePlace E → ℝ) =
      fullLogPermutation F E g x := rfl

/-- The realization intertwines the canonical representation and the restricted real action. -/
theorem infinitePlaceLatticeRealization_equivariant (g : E ≃ₐ[F] E)
    (x : (infinitePlaceLatticeRepresentation F E).V) :
    infinitePlaceLatticeRealization F E ((infinitePlaceLatticeRepresentation F E).ρ g x) =
      infinitePlaceCoordinateLatticeAut F E g (infinitePlaceLatticeRealization F E x) := by
  apply Subtype.ext
  funext w
  calc
    _ = ((((infinitePlaceLatticeRepresentation F E).ρ g x).coeff w).down : ℝ) :=
      infinitePlaceLatticeRealization_apply F E _ w
    _ = ((x.coeff (g⁻¹ • w)).down : ℝ) :=
      congrArg (fun z : NormalizedTwoCocycle.CoefficientScalars.{v} => (z.down : ℝ))
        (infinitePlaceLatticeRepresentation_coeff F E g x w)
    _ = _ := (infinitePlaceLatticeRealization_apply F E x (g⁻¹ • w)).symm

end Langlands.ClassField.Global
