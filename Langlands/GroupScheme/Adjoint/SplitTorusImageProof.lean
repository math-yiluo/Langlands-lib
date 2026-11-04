import Langlands.GroupScheme.Adjoint.SplitTorusImageStatement
import Langlands.GroupScheme.Rational.CentralSurjectionMaximalSplitTorusImageProof
import Langlands.GroupScheme.Rational.SplitTorusFppfImage

/-! # Maximal split image tori in adjoint quotients: proof -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The adjoint split-torus image existence statement follows from maximality of
supplied fppf split-torus images under central fppf surjections. -/
theorem adjointSplitTorusImageExistenceStatement_of_centralSurjectionMaximality
    (hmax : CentralSurjectionMaximalSplitTorusImageStatement.{u}) :
    AdjointSplitTorusImageExistenceStatement.{u} := by
  intro k _ G A T q i hq hi
  have : IsAffineHom A.X.hom := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let E := hi.1.1.fppfImage (i ≫ q)
  have hmaxj : IsMaximalSplitTorus E.inclusion :=
    hmax k G A q hq.isConnectedReductive
      hq.isAdjoint.isSemisimple.isConnectedReductive hq.flat hq.surjective
      hq.locallyOfFinitePresentation hq.kernelCenter.isCentral
      T E.torus i E.inclusion E.projection hi E.isSplitSubtorus E.flat E.surjective
      E.locallyOfFinitePresentation E.factorization
  exact ⟨E.torus, E.inclusion, E.projection, hq, hi, hmaxj, E.factorization, E.flat,
    E.surjective, E.locallyOfFinitePresentation⟩

/-- **Maximal split image tori in adjoint quotients.** Over every field, the image of a
maximal split torus in an adjoint quotient is a maximal split torus, reached by an fppf
torus homomorphism completing the commutative square. -/
theorem adjointSplitTorusImageExistenceStatement :
    AdjointSplitTorusImageExistenceStatement.{u} :=
  adjointSplitTorusImageExistenceStatement_of_centralSurjectionMaximality
    centralSurjectionMaximalSplitTorusImage

end Langlands.GroupScheme
