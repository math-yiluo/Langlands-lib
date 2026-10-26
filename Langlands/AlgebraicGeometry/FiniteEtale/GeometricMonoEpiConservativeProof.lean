import Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricMonomorphismComplementsProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricEpimorphismPreservationProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberConservativeProof

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Monomorphisms of finite étale covers are direct summands, and the actual geometric
fibre functor preserves epimorphisms and reflects isomorphisms. -/
theorem geometricMonoEpiConservative {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricMonoEpiConservative s hfin := by
  unfold GeometricMonoEpiConservative
  exact ⟨geometricMonomorphismComplements s hfin, geometricEpimorphismPreservation s hfin,
    geometricFiberConservative s hfin⟩

end Langlands.AlgebraicGeometry.FiniteEtale
