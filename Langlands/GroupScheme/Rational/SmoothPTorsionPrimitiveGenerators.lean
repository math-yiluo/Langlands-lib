import Langlands.GroupScheme.Rational.PTorsionHopfCoordinates
import Langlands.GroupScheme.Rational.SmoothHopfCoordinates
import Langlands.Algebra.PTorsionHopf.PrimitiveGenerationDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Primitive generators for smooth commutative groups of prime exponent -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [Smooth G.X.hom] [IsCommMonObj G.X]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Smooth commutative affine groups killed by `p` have primitive algebra generators
over the original field, including when the group is disconnected. -/
theorem adjoin_primitive_eq_top_of_smooth_uniformExponent
    (hG : HasUniformPowerExponent G p) :
    Algebra.adjoin k {a : hopfAlgebra G | Bialgebra.IsPrimitiveElem k a} = ⊤ := by
  have : Algebra.Smooth k (hopfAlgebra G) := hopfAlgebraSmooth G
  have : IsReduced (AlgebraicClosure k ⊗[k] hopfAlgebra G) :=
    hopfAlgebraBaseChangeReduced G (AlgebraicClosure k)
  have : Coalgebra.IsCocomm k (hopfAlgebra G) := hopfAlgebra_isCocomm G
  exact Langlands.Algebra.PTorsionHopf.adjoin_primitive_eq_top_of_geometric_points
    (AlgebraicClosure k) p fun φ =>
      convPow_baseChange_linearMap_eq_one_of_uniformExponent G hG (AlgebraicClosure k) φ

/-- The original-field coordinate algebra has finitely many primitive generators. -/
theorem exists_finite_primitive_generators_of_smooth_uniformExponent
    (hG : HasUniformPowerExponent G p) :
    ∃ T : Finset {a : hopfAlgebra G // Bialgebra.IsPrimitiveElem k a},
      Algebra.adjoin k (Subtype.val '' (T : Set {a : hopfAlgebra G //
        Bialgebra.IsPrimitiveElem k a})) = ⊤ := by
  have : Algebra.Smooth k (hopfAlgebra G) := hopfAlgebraSmooth G
  exact Langlands.Algebra.PTorsionHopf.exists_finite_primitive_generators
    (adjoin_primitive_eq_top_of_smooth_uniformExponent G p hG)

/-- A chosen finite family of original-field primitive algebra generators. -/
def finitePrimitiveGeneratorsOfSmoothUniformExponent
    (hG : HasUniformPowerExponent G p) :
    {T : Finset {a : hopfAlgebra G // Bialgebra.IsPrimitiveElem k a} //
      Algebra.adjoin k (Subtype.val '' (T : Set {a : hopfAlgebra G //
        Bialgebra.IsPrimitiveElem k a})) = ⊤} :=
  ⟨(exists_finite_primitive_generators_of_smooth_uniformExponent G p hG).choose,
    (exists_finite_primitive_generators_of_smooth_uniformExponent G p hG).choose_spec⟩

end Langlands.GroupScheme.AffineCoordinates
