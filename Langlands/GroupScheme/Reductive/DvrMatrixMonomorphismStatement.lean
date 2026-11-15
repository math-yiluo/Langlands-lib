import Langlands.GroupScheme.DvrAffineClosureReduction
import Langlands.GroupScheme.DedekindLinearEmbeddingStatement

/-! # Reduction of reductive DVR monomorphisms to matrix representations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The remaining matrix case over a DVR: a scheme-monic representation of a
reductive group in a general linear group is a closed immersion. -/
def ReductiveDvrMatrixMonomorphismStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (M : GroupScheme (Spec (CommRingCat.of R))), IsReductive M →
    ∀ (N : ℕ) (ρ : MatrixRepresentation M (Fin N)),
      Mono ρ.hom.hom.left → IsClosedSubgroup ρ

namespace DvrMatrixReduction

/-- A closed linear embedding of the flat affine target reduces the assertion
to monic representations, with the embedding theorem supplied explicitly. -/
theorem flatAffineCase_of_matrixCase
    (embedding : DedekindLinearEmbeddingStatement.{u})
    (matrix : ReductiveDvrMatrixMonomorphismStatement.{u}) :
    DvrAffineClosureReduction.FlatAffineCase.{u} := by
  intro R _ _ _ M G hM hflat ha hft _ f hf
  obtain ⟨N, ρ, hρ⟩ := embedding R G hflat ha hft
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hmono : Mono (ρ.restrict f).hom.hom.left := by
    change Mono (f.hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  have hcomp : IsClosedImmersion (f.hom.hom.left ≫ ρ.hom.hom.left) :=
    matrix R M hM N (ρ.restrict f) hmono
  exact IsClosedImmersion.of_comp f.hom.hom.left ρ.hom.hom.left

/-- Raynaud affineness, Dedekind linear embedding and the matrix case together
imply the full published DVR assertion. All three inputs remain explicit. -/
theorem dvrCase_of_matrixCase
    (raynaud : DvrGenericAffinenessStatement.{u})
    (embedding : DedekindLinearEmbeddingStatement.{u})
    (matrix : ReductiveDvrMatrixMonomorphismStatement.{u}) :
    ReductiveMonomorphismValuativeReduction.DvrCase.{u} :=
  DvrAffineClosureReduction.dvrCase_of_flatAffineCase raynaud
    (flatAffineCase_of_matrixCase embedding matrix)

end DvrMatrixReduction
end Langlands.GroupScheme
