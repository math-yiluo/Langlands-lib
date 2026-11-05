import Langlands.GroupScheme.AffineCoordinateEvaluation
import Langlands.GroupScheme.Reductive.InducedRegular
import Langlands.GroupScheme.Reductive.AffineFixedVectorRegular

/-! # Covariant coordinates for actual affine group morphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem productMap_rTensor {K B C A : Type*} [CommSemiring K]
    [CommSemiring B] [CommSemiring C] [CommSemiring A]
    [Algebra K B] [Algebra K C] [Algebra K A]
    (r : B →ₐ[K] C) (f : C →ₐ[K] A) (g : B →ₐ[K] A) (z : B ⊗[K] B) :
    Algebra.TensorProduct.productMap f g (r.toLinearMap.rTensor B z) =
      Algebra.TensorProduct.productMap (f.comp r) g z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Coordinates covariant for left multiplication through an actual affine group morphism.
The supplied coordinate need not be a character. -/
def leftCovariantSubspace (i : H ⟶ G) (χ : algebra H) : Submodule k (algebra G) :=
  letI : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  Chevalley.leftCovariantSubspace (K := k) (B := algebra G) (C := algebra H)
    (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom.toLinearMap χ

set_option backward.isDefEq.respectTransparency false in
theorem mem_leftCovariantSubspace (i : H ⟶ G) (χ : algebra H) (b : algebra G) :
    b ∈ leftCovariantSubspace i χ ↔
      letI : Coalgebra k (algebra G) :=
        (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
      (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom.toLinearMap.rTensor
          (algebra G) (comul (R := k) (A := algebra G) b) = χ ⊗ₜ[k] b := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  exact Chevalley.mem_leftCovariantSubspace
    (K := k) (B := algebra G) (C := algebra H) _ χ b

/-- Tensor covariance implies covariance on every scheme test, without a density assumption. -/
theorem pointAlgebraHom_leftCovariant (i : H ⟶ G) (χ : algebra H) {b : algebra G}
    (hb : b ∈ leftCovariantSubspace i χ)
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X) :
    pointAlgebraHom G T ((h ≫ i.hom.hom) * g) b =
      pointAlgebraHom H T h χ * pointAlgebraHom G T g b := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  let r : algebra G →ₐ[k] algebra H := (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
  have he := congrArg (Algebra.TensorProduct.productMap
    (pointAlgebraHom H T h) (pointAlgebraHom G T g))
      ((mem_leftCovariantSubspace i χ b).mp hb)
  change Algebra.TensorProduct.productMap (pointAlgebraHom H T h)
    (pointAlgebraHom G T g) (r.toLinearMap.rTensor (algebra G) (comul b)) = _ at he
  rw [productMap_rTensor (K := k) r
    (pointAlgebraHom H T h) (pointAlgebraHom G T g)] at he
  rw [pointAlgebraHom_mul, AffineHomImageHopfAdapter.pointAlgebraHom_pullback]
  exact he

/-- Every finite family of covariant coordinates lies in a finite regular subspace. -/
theorem exists_finite_leftCovariant_regularSubspace (i : H ⟶ G) (χ : algebra H)
    (S : Finset (algebra G)) (hS : (S : Set (algebra G)) ⊆ leftCovariantSubspace i χ) :
    ∃ V : Submodule k (algebra G), Module.Finite k V ∧ (S : Set (algebra G)) ⊆ V ∧
      V ≤ leftCovariantSubspace i χ ∧
      (letI : Coalgebra k (algebra G) :=
        (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
        ∀ (ψ : Module.Dual k (algebra G)) (b : algebra G),
          b ∈ V → AffineLinearEmbedding.rightAct ψ b ∈ V) := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  exact Chevalley.exists_finite_leftCovariant_regularSubspace
    (K := k) (B := algebra G) (C := algebra H) _ χ S hS

end AffineCoordinates

namespace Chevalley

open AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  (V : Submodule k (AffineCoordinates.algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
      w ∈ V → rightAct f w ∈ V)

/-- The finite regular representation on an actual affine group evaluates its coordinate matrix. -/
theorem affineRegularRepresentation_pointMatrix
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (i j : Fin d) :
    letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    (affineRegularRepresentation G V b hV).pointMatrix T g i j =
      AffineCoordinates.pointAlgebraHom G T g (subspaceMatrix V b i j) := by
  rw [affineRegularRepresentation, pointMatrix_restrict]
  exact regularRepresentation_pointMatrix _ _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Right multiplication acts by the finite regular representation on every test scheme. -/
theorem affineRegularRepresentation_mul_basis
    (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X) (j : Fin d) :
    let M : Matrix (Fin d) (Fin d) ((algΓ (CommRingCat.of k)).obj T).unop :=
      ((affineRegularRepresentation G V b hV).pointMatrix T h :
        Matrix (Fin d) (Fin d) Γ(T.left, ⊤))
    AffineCoordinates.pointAlgebraHom G T (g * h) (b j : AffineCoordinates.algebra G) =
      ∑ i, AffineCoordinates.pointAlgebraHom G T g
          (b i : AffineCoordinates.algebra G) * M i j := by
  let : Coalgebra k (AffineCoordinates.algebra G) :=
    (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
  dsimp only
  rw [AffineCoordinates.pointAlgebraHom_mul]
  change Algebra.TensorProduct.productMap _ _ (comul (b j : AffineCoordinates.algebra G)) = _
  rw [comul_basis V b hV, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.TensorProduct.productMap_apply_tmul,
    affineRegularRepresentation_pointMatrix]

end Chevalley

end Langlands.GroupScheme
