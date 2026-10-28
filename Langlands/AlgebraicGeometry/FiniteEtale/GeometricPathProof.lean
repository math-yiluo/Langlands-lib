import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathStatement
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Langlands.CategoryTheory.Galois.FiberFunctorIsoProof

open CategoryTheory

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The actual finite fibre functors at two geometric points admit a natural
isomorphism, even when their algebraically closed coefficient fields differ. -/
theorem geometricPathExists
    {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
    {Ωs Ωt : Type u} [Field Ωs] [IsAlgClosed Ωs] [Field Ωt] [IsAlgClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y)) :
    GeometricPathExists s t hs ht := by
  rcases geometricGaloisFiberFunctor s hs with ⟨hCs, hFs⟩
  rcases geometricGaloisFiberFunctor t ht with ⟨hCt, hFt⟩
  let : GaloisCategory (Cover S) := hCs
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hs) := hFs
  let : PreGaloisCategory.FiberFunctor (fiberFunctor t ht) := hFt
  exact Langlands.CategoryTheory.Galois.fiberFunctorIsoExists
    (fiberFunctor s hs) (fiberFunctor t ht)

end Langlands.AlgebraicGeometry.FiniteEtale
