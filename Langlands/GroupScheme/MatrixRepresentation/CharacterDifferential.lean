import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.Lie.RepresentationDifferential

/-! # Differentials on actual character spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The epsilon coefficient of a rational character evaluated at an actual tangent point. -/
def characterTangentScalar (chi : rationalCharacters G) (X : lieKernel G k) : k :=
  (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (DualNumber k))
    (X.val ≫ chi.toMul.hom.hom) : DualNumber k).snd

/-- A tangent vector acts on an actual character space by the epsilon coefficient of
that character's value on the tangent point. -/
theorem tangentMatrix_mulVec_of_mem_characterSpace
    (r : MatrixRepresentation G n) (chi : rationalCharacters G)
    {v : n → k} (hv : v ∈ r.characterSpace chi) (X : lieKernel G k) :
    r.tangentMatrix k X *ᵥ v = characterTangentScalar chi X • v := by
  have h := characterSpace_affine hv (CommAlgCat.of k (DualNumber k)) X.val
  funext i
  have hi := congrArg (fun w : n → DualNumber k => (w i).snd) h
  have ht (a b : n) : r.tangentMatrix k X a b =
      ((r.affineMatrix (CommAlgCat.of k (DualNumber k)) X.val : Matrix n n (DualNumber k))
        a b).snd := rfl
  change (∑ j, (r.tangentMatrix k X i j) * v j) = _
  simp_rw [ht]
  simpa [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.algebraMap_eq_inl, characterTangentScalar] using hi

/-- Every actual character space is stable under all tangent matrices. -/
theorem tangentMatrix_mulVec_mem_characterSpace
    (r : MatrixRepresentation G n) (chi : rationalCharacters G)
    {v : n → k} (hv : v ∈ r.characterSpace chi) (X : lieKernel G k) :
    r.tangentMatrix k X *ᵥ v ∈ r.characterSpace chi := by
  rw [tangentMatrix_mulVec_of_mem_characterSpace r chi hv X]
  exact Submodule.smul_mem _ _ hv

end Langlands.GroupScheme.MatrixRepresentation
