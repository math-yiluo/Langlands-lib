import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

open CategoryTheory

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Geometric point finiteness, without an assumed finite packaging. -/
def GeometricFiberFinite {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Prop :=
  ∀ Y : Cover S, Finite (Fiber s Y)

/-- The actual finite étale category is Galois and the actual geometric point
functor is a fibre functor for that structure. The structure is a conclusion. -/
def GeometricGaloisFiberFunctor {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  ∃ hG : GaloisCategory (Cover S),
    letI : GaloisCategory (Cover S) := hG
    PreGaloisCategory.FiberFunctor (fiberFunctor s hfin)

/-- The existing functor to finite continuous actions is an equivalence. -/
def GeometricContinuousActionEquivalence {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  (continuousActionFunctor s hfin).IsEquivalence

end Langlands.AlgebraicGeometry.FiniteEtale
