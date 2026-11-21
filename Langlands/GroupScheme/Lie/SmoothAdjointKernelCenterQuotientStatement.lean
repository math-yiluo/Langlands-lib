import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # The adjoint kernel modulo the centre (Milne 14.23, smooth case) -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

/-- For a smooth connected affine algebraic group over a field, the full
kernel of the adjoint representation modulo the full centre is unipotent.
The quotient is represented by an affine algebraic group in the fppf topology. -/
def SmoothAdjointKernelCenterQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (d : ℕ) (c : FiniteCoordinates G d),
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : kernel (adjointRepresentation c) ⟶ Q),
      IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom ∧
        RelativeRoot.IsFppfQuotient ((center G).comap (kernelι (adjointRepresentation c))) q ∧
        IsUnipotent Q

end Langlands.GroupScheme.Lie
