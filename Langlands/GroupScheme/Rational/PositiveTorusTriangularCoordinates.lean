import Langlands.GroupScheme.TriangularCoordinates
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-!
# Torus-weighted triangular coordinates on the standard unipotent subgroup

For a connected reductive group `G` over a field of characteristic zero, a maximal split torus
`i : T ⟶ G` and a generic cocharacter `ν`, `PositiveTorusTriangularCoordinatesStatement`
asserts that the standard unipotent subgroup `N = U(ν)` has triangular polynomial coordinates
(as in `HasTriangularCoordinates`) that are weight vectors for conjugation by `T`. Each
coordinate has a positive relative root as weight, and each positive relative root `β` is the
weight of exactly `dim 𝔤_β` coordinates. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Torus-weighted triangular coordinates on the standard unipotent subgroup.** Let `F` be a
field of characteristic zero, `G` a connected reductive group over `F`, `i : T ⟶ G` a maximal
split torus and `ν` a generic cocharacter, and let `ι : N ⟶ G` be the standard unipotent
subgroup `Standard.unipotentHom i ν ∅`. Then there are global functions `t₀, …, t_{d-1}` on `N`
and characters `w₀, …, w_{d-1}` of `T` such that:
* `t` identifies the coordinate ring of `N` with the polynomial ring `F[X₀, …, X_{d-1}]`;
* the group law is triangular: `(x * y)_k = x_k + y_k + P_k(x_j, y_j : j < k)`;
* for every `F`-algebra `A`, `s ∈ T(A)` and `x, y ∈ N(A)` with `ι(y) = i(s) ι(x) i(s)⁻¹`,
  one has `y_k = w_k(s) x_k`;
* every `w_k` is a positive relative root, and every positive relative root `β` equals `w_k`
  for exactly `dim_F 𝔤_β` indices `k`, where `𝔤_β` is the `β`-weight space of `T` in the Lie
  algebra of `G`. -/
def PositiveTorusTriangularCoordinatesStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T),
        IsMaximalSplitTorus i → IsGenericCocharacter i ν →
          haveI : IsAffineHom (Standard.unipotentScheme i ν ∅).X.hom :=
            (Standard.isClosedSubgroup_unipotentHom i ν ∅).isAffineHom
          haveI : IsAffine (Standard.unipotentScheme i ν ∅).X.left :=
            isAffine_of_isAffineHom (Standard.unipotentScheme i ν ∅).X.hom
          ∃ (d : ℕ) (t : Fin d → AffineCoordinateRing F (Standard.unipotentScheme i ν ∅).X)
            (P : Fin d → MvPolynomial (Fin d ⊕ Fin d) F) (w : Fin d → characterLattice T),
            Function.Bijective
                (MvPolynomial.aeval t :
                  MvPolynomial (Fin d) F →ₐ[F]
                    AffineCoordinateRing F (Standard.unipotentScheme i ν ∅).X) ∧
              (∀ k, ∀ v ∈ (P k).vars, Sum.elim id id v < k) ∧
              (∀ (A : CommAlgCat.{u} F) (x y : (Standard.unipotentScheme i ν ∅).affinePoints A)
                  (k : Fin d),
                (Standard.unipotentScheme i ν ∅).affinePointEvaluation A (x * y) (t k) =
                  (Standard.unipotentScheme i ν ∅).affinePointEvaluation A x (t k) +
                    (Standard.unipotentScheme i ν ∅).affinePointEvaluation A y (t k) +
                      MvPolynomial.aeval
                        (Sum.elim
                          (fun j => (Standard.unipotentScheme i ν ∅).affinePointEvaluation A x
                            (t j))
                          (fun j => (Standard.unipotentScheme i ν ∅).affinePointEvaluation A y
                            (t j))) (P k)) ∧
              (∀ (A : CommAlgCat.{u} F) (s : GroupScheme.affinePoints T.toGrp A)
                  (x y : (Standard.unipotentScheme i ν ∅).affinePoints A),
                (Standard.unipotentScheme i ν ∅).affinePointsTarget
                    (Standard.unipotentHom i ν ∅) A y =
                  GroupScheme.affinePointsTarget T.toGrp i A s *
                    (Standard.unipotentScheme i ν ∅).affinePointsTarget
                      (Standard.unipotentHom i ν ∅) A x *
                    (GroupScheme.affinePointsTarget T.toGrp i A s)⁻¹ →
                  ∀ k, (Standard.unipotentScheme i ν ∅).affinePointEvaluation A y (t k) =
                    (Lie.characterValue (w k) s : A) *
                      (Standard.unipotentScheme i ν ∅).affinePointEvaluation A x (t k)) ∧
              (∀ k, w k ∈ positiveRelativeRoots i ν) ∧
              ∀ β ∈ positiveRelativeRoots i ν,
                Nat.card {k // w k = β} = Module.finrank F (weightSpace i β)

end Langlands.GroupScheme
