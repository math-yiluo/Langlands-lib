import Langlands.AlgebraicGeometry.FiniteEtale.Statements
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Mathlib.CategoryTheory.Galois.Equivalence

open CategoryTheory

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The actual geometric continuous-action functor is an equivalence. -/
theorem geometricContinuousActionEquivalence
    {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricContinuousActionEquivalence s hfin := by
  obtain ⟨hG, hF⟩ := geometricGaloisFiberFunctor s hfin
  let : GaloisCategory (Cover S) := hG
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hfin) := hF
  change (PreGaloisCategory.functorToContAction (fiberFunctor s hfin)).IsEquivalence
  infer_instance

end Langlands.AlgebraicGeometry.FiniteEtale
