import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactness

/-!
# Finitely many affine étale charts carrying all field-valued points

An intermediate statement for the closedness part of Conrad's Corollary 5.7, derived from
the construction in the proof of Stacks Project, Lemma 68.8.3 (Tag 0BBN). Let `C` be a
commutative ring and `X` a separated, quasi-compact algebraic space over `Spec C`. There are
finitely many affine schemes over `Spec C` with étale maps to `X` such that, for every field
`k` with a `C`-algebra structure, every `k`-valued point of `X` is the image of a `k`-valued
point of one of them.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Uniform affine étale charts for field-valued points: let `C` be a commutative ring and
let `X` be a separated, quasi-compact algebraic space over `Spec C`. Then there are finitely
many affine schemes `U₀, …, U_{n-1}` over `Spec C` with étale morphisms `fᵢ : Uᵢ → X` such
that for every field `k` with a `C`-algebra structure and every `k`-valued point `x` of `X`,
some `fᵢ` maps a `k`-valued point of `Uᵢ` to `x`. -/
def UniformFieldPointChartsStatement : Prop :=
  ∀ (C : Type u) [CommRing C] (X : AlgebraicSpace (Spec (CommRingCat.of C))),
    IsSeparated X → IsQuasiCompact X →
      ∃ (n : ℕ) (U : Fin n → Over (Spec (CommRingCat.of C)))
        (f : ∀ i, (schemeToSpace _).obj (U i) ⟶ X),
        (∀ i, IsAffine (U i).left ∧ IsEtale (hom (f i))) ∧
          ∀ (k : Type u) [Field k] [Algebra C k] (x : RingPoints C X k),
            ∃ (i : Fin n) (u : RingPoint C (U i) k),
              RingPoints.map (f i) ((schemeRingPointsEquiv C (U i) k).symm u) = x

end Langlands.AlgebraicGeometry.AlgebraicSpace
