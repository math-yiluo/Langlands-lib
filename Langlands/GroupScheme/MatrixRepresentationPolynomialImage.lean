import Langlands.Group.AlgebraicMatrixPowers
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding

/-! # Polynomial equations for the image of an actual affine-point representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Matrix
open _root_.Langlands.GroupScheme.GeneralLinear
open Langlands.Group.AlgebraicMatrixPowers

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

local instance sectionsAlgebra (T : Over (Spec (CommRingCat.of k))) :
    Algebra k Γ(T.left, ⊤) :=
  ((algΓ (CommRingCat.of k)).obj T).unop.algebra

/-- Equations of the image, with coefficients extended from the base field. -/
def affineImageEquations (S : Type u) [CommRing S] [Algebra k S] :
    Set (MvPolynomial (Coordinate n) S) :=
  MvPolynomial.map (algebraMap k S) '' (Dynamic.embeddingIdeal ρ : Set _)

/-- The range of the actual affine-point coefficient map is exactly the zero
locus of the closed representation's embedding ideal. -/
theorem mem_affineMatrix_range_iff_zeroLocus [IsClosedImmersion ρ.hom.hom.left]
    (S : Type u) [CommRing S] [Algebra k S] (g : GL n S) :
    g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range ↔
      g ∈ zeroLocus S (Dynamic.embeddingIdeal ρ) := by
  have hcompare (x : Dynamic.affineTest k S ⟶ G.X) :
      pointsEquiv n _ _ (x ≫ ρ.hom.hom) =
        Matrix.GeneralLinearGroup.map (Dynamic.affineTestEquiv k S).toRingHom
          (ρ.affineMatrix (CommAlgCat.of k S) x) :=
    ρ.pointMatrix_eq_affineMatrix _ x
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := n) (Dynamic.affineTestEquiv k S).toRingHom) := by
    intro a b hab
    apply Units.ext
    ext i j
    apply (Dynamic.affineTestEquiv k S).injective
    exact congrArg (fun z : GL n Γ((Dynamic.affineTest k S).left, ⊤) => z i j) hab
  rw [Dynamic.mem_zeroLocus_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, hcompare x⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hinj ((hcompare x).symm.trans hx)⟩

/-- Membership in the actual point-map range is given by polynomial equations
in matrix and inverse-matrix entries over the test algebra. -/
theorem mem_affineMatrix_range_iff_equations [IsClosedImmersion ρ.hom.hom.left]
    (S : Type u) [CommRing S] [Algebra k S] (g : GL n S) :
    g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range ↔
      ∀ p ∈ ρ.affineImageEquations S, MvPolynomial.eval (values g) p = 0 := by
  rw [mem_affineMatrix_range_iff_zeroLocus]
  constructor
  · intro hg p hp
    obtain ⟨q, hq, rfl⟩ := hp
    simpa only [MvPolynomial.eval_map, ← MvPolynomial.aeval_def] using hg q hq
  · intro hg q hq
    have h := hg _ ⟨q, hq, rfl⟩
    simpa only [MvPolynomial.eval_map, ← MvPolynomial.aeval_def] using h

/-- For an `RCLike` test algebra, the actual representation range satisfies the
polynomial hypothesis used for internal positive powers and polar factors. -/
theorem affineMatrix_range_isPolynomiallyDefined [IsClosedImmersion ρ.hom.hom.left]
    (S : Type u) [RCLike S] [Algebra k S] :
    IsPolynomiallyDefined (ρ.affineMatrix (CommAlgCat.of k S)).range :=
  ⟨ρ.affineImageEquations S, ρ.mem_affineMatrix_range_iff_equations S⟩

end Langlands.GroupScheme.MatrixRepresentation
