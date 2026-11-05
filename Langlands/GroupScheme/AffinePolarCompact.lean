import Langlands.Global.InfinitePlaceMatrixRealization
import Langlands.Group.InternalPolarFactors
import Langlands.GroupScheme.MatrixRepresentationPolynomialImage

/-! # Polar compact subgroups on actual affine points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix ComplexOrder

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false

open Langlands.Group.MatrixPolarCompact
open Langlands.Group.InternalPolarFactors

variable {k S : Type u} [Field k] [RCLike S] [Algebra k S]
  {G : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
  (ρ : MatrixRepresentation G (Fin d))

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of k S)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k S)

/-- The unitary inverse image in the actual affine-point group. -/
def affineUnitarySubgroup : Subgroup (G.affinePoints (CommAlgCat.of k S)) :=
  unitarySubgroup (ρ.affineMatrix (CommAlgCat.of k S))

@[simp] theorem mem_affineUnitarySubgroup (g : G.affinePoints (CommAlgCat.of k S)) :
    g ∈ ρ.affineUnitarySubgroup (S := S) ↔
      (ρ.affineMatrix (CommAlgCat.of k S) g).val ∈ Matrix.unitaryGroup (Fin d) S :=
  mem_unitarySubgroup _ g

variable [IsAffine G.X.left]

/-- A closed actual representation has compact unitary inverse image in the
regular-function evaluation topology. -/
theorem isCompact_affineUnitarySubgroup (hρ : IsClosedSubgroup ρ) :
    IsCompact (ρ.affineUnitarySubgroup (S := S) :
      Set (G.affinePoints (CommAlgCat.of k S))) :=
  isCompact_unitarySubgroup (ρ.affineMatrix (CommAlgCat.of k S))
    (ρ.isClosedEmbedding_affineMatrix (CommAlgCat.of k S) hρ)

/-- Polynomial equations of the actual image supply the internal polar factors;
only adjoint stability remains an additional condition on the image. -/
theorem exists_affineUnitary_right_quotient_posDef (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range)
    (g : G.affinePoints (CommAlgCat.of k S)) :
    ∃ a : G.affinePoints (CommAlgCat.of k S),
      a ∈ ρ.affineUnitarySubgroup (S := S) ∧
        (ρ.affineMatrix (CommAlgCat.of k S) (g * a⁻¹)).val.PosDef := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  exact exists_unitary_right_quotient_posDef (ρ.affineMatrix (CommAlgCat.of k S))
    (ρ.isClosedEmbedding_affineMatrix (CommAlgCat.of k S) hρ).injective
    (ρ.affineMatrix_range_isPolynomiallyDefined S) hstar g

/-- Construct a maximal compact subgroup in the existing actual-point topology
from a closed representation whose actual image is stable under adjoints. -/
def affineMaximalCompact (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) :
    {K : Subgroup (G.affinePoints (CommAlgCat.of k S)) //
      IsCompact (K : Set (G.affinePoints (CommAlgCat.of k S))) ∧
      ∀ L : Subgroup (G.affinePoints (CommAlgCat.of k S)),
        IsCompact (L : Set (G.affinePoints (CommAlgCat.of k S))) → K ≤ L → L = K} := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  exact maximalCompactOfPolynomialStarClosed (ρ.affineMatrix (CommAlgCat.of k S))
    (ρ.isClosedEmbedding_affineMatrix (CommAlgCat.of k S) hρ)
    (ρ.affineMatrix_range_isPolynomiallyDefined S) hstar

@[simp] theorem affineMaximalCompact_val (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) :
    (ρ.affineMaximalCompact hρ hstar).val = ρ.affineUnitarySubgroup (S := S) := rfl

end Langlands.GroupScheme.MatrixRepresentation
