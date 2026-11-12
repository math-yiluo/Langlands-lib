import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointProof
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Completing finite extensions of normed fields

The completion of a finite normed extension is finite over the completion of the base.
No separability, henselianity or module-topology hypothesis is needed.
-/

noncomputable section

universe u v

open Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology.FiniteExtensionCompletion

variable (K : Type u) (L : Type v)
variable [NontriviallyNormedField K] [NontriviallyNormedField L] [NormedAlgebra K L]

local notation "K̂" => UniformSpace.Completion K
local notation "L̂" => UniformSpace.Completion L

/-- The inclusion of a normed field extension is an isometry. -/
theorem isometry_algebraMap : Isometry (algebraMap K L) :=
  AddMonoidHomClass.isometry_of_norm (algebraMap K L) (norm_algebraMap' L)

/-- The continuous field embedding between the completions. -/
def map : K̂ →+* L̂ :=
  UniformSpace.Completion.mapRingHom (algebraMap K L) (isometry_algebraMap K L).continuous

/-- The completed field embedding restricts to the original embedding. -/
@[simp]
theorem map_coe (x : K) :
    map K L (x : K̂) = ((algebraMap K L x : L) : L̂) :=
  UniformSpace.Completion.mapRingHom_coe _ x

/-- The completed extension is still isometric. -/
theorem isometry_map : Isometry (map K L) :=
  UniformSpace.Completion.isometry_mapRingHom (isometry_algebraMap K L)

/-- The canonical algebra structure of the completed extension. -/
@[instance_reducible]
def algebra : Algebra K̂ L̂ :=
  (map K L).toAlgebra

attribute [local instance] algebra

/-- Compatibility with the original base-field algebra structure. -/
instance scalarTower : IsScalarTower K K̂ L̂ :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change ((algebraMap K L x : L) : L̂) = map K L (x : K̂)
    exact (map_coe K L x).symm

/-- The canonical algebra on completions is normed. -/
@[instance_reducible]
def normedAlgebra : NormedAlgebra K̂ L̂ where
  norm_smul_le c x := by
    rw [Algebra.smul_def, norm_mul]
    exact le_of_eq (congrArg (· * ‖x‖)
      ((isometry_map K L).norm_map_of_map_zero (map_zero _) c))

attribute [local instance] normedAlgebra

/-- The original extension embeds as a base-field algebra into its completion. -/
def coeAlgHom : L →ₐ[K] L̂ where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl

/-- The canonical map from the tensor product into the completed extension. -/
def tensorMap : K̂ ⊗[K] L →ₐ[K̂] L̂ :=
  Algebra.TensorProduct.lift (Algebra.ofId K̂ L̂) (coeAlgHom K L)
    (fun _ _ => Commute.all _ _)

/-- The tensor-product map contains the original extension in its image. -/
@[simp]
theorem tensorMap_one_tmul (x : L) :
    tensorMap K L (1 ⊗ₜ[K] x) = (x : L̂) := by
  simp only [tensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

variable [FiniteDimensional K L]

/-- The tensor map onto the completion is surjective: its finite-dimensional image is
closed and contains the dense image of `L`. -/
theorem tensorMap_surjective : Function.Surjective (tensorMap K L) := by
  let := completionNontriviallyNormedField K
  let R := LinearMap.range (tensorMap K L).toLinearMap
  have hclosed : IsClosed (R : Set L̂) := Submodule.closed_of_finiteDimensional R
  have hsub : Set.range ((↑) : L → L̂) ⊆ (R : Set L̂) := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_range.mpr ⟨1 ⊗ₜ[K] x, tensorMap_one_tmul K L x⟩
  intro z
  exact LinearMap.mem_range.mp
    (closure_minimal hsub hclosed (UniformSpace.Completion.denseRange_coe z))

/-- Completing a finite normed field extension again gives a finite field extension. -/
theorem finiteDimensional : FiniteDimensional K̂ L̂ :=
  FiniteDimensional.of_surjective (tensorMap K L).toLinearMap (tensorMap_surjective K L)

end Langlands.AlgebraicGeometry.PointTopology.FiniteExtensionCompletion
