import Langlands.GroupScheme.Reductive.CovariantProductInjective
import Langlands.GroupScheme.Reductive.AffineReynoldsRegular
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Covariant exhaustion by Steinberg-type products -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineLinearEmbedding MatrixRepresentation

local instance steinbergCovariantExhaustionInst {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- For a simply connected semisimple group over an algebraically closed field of
positive characteristic there are an actual diagonalizable subgroup `j`, two actual
subgroup maps `i : H → G` and `i' : H' → G` with coordinates `χ` and `ψ` such that:
the comorphism of `(p, q) ↦ i(p) i'(q)⁻¹` is injective; `1` is a sum of products of a
left `i`-covariant coordinate of weight `χ` and a left `i'`-covariant coordinate of
weight `ψ`; every left `j`-invariant coordinate is such a sum of products for the weights
`χ ^ e` and `ψ ^ e`, for some `e`; and for cofinally many `e` the two covariant spaces of
weights `χ ^ e` and `ψ ^ e` have the same finite dimension, the first being rationally
irreducible under right translation. This is a proposition to be proved, not an assumed
theorem. -/
def SteinbergCovariantExhaustionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∃ (Λ : Type u) (_ : AddCommGroup Λ)
      (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
      (H H' : GroupScheme (Spec (CommRingCat.of k)))
      (_ : IsAffineHom H.X.hom) (_ : IsAffineHom H'.X.hom)
      (i : H ⟶ G) (i' : H' ⟶ G)
      (χ : AffineCoordinates.algebra H) (ψ : AffineCoordinates.algebra H'),
      Function.Injective (Chevalley.differenceComorphism
        (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
        (AffineHomImageHopfAdapter.pullback i').hom.toAlgHom) ∧
      (1 : AffineCoordinates.algebra G) ∈ AffineCoordinates.leftCovariantSubspace i χ *
        AffineCoordinates.leftCovariantSubspace i' ψ ∧
      (∀ w : AffineCoordinates.algebra G,
        (∀ (T : Over (Spec (CommRingCat.of k)))
          (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X)
          (g : T ⟶ G.X),
          AffineCoordinates.pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w =
            AffineCoordinates.pointAlgebraHom G T g w) →
        ∃ e : ℕ, w ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
          AffineCoordinates.leftCovariantSubspace i' (ψ ^ e)) ∧
      (∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
        (bX : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e')))
        (_ : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i' (ψ ^ e')))
        (hX : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
          ∀ (f : Module.Dual k (AffineCoordinates.algebra G))
            (v : AffineCoordinates.algebra G),
            v ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e') →
              rightAct f v ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e')),
        (Chevalley.affineRegularRepresentation G _ bX hX).rationalRepresentation.IsIrreducible)

end Langlands.GroupScheme
