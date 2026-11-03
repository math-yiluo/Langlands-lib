import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Simple connectedness forces integral coroot generation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The necessity direction of the integral coroot criterion, for a supplied
finite reduced root datum of an actual split maximal torus. -/
def SplitSimplyConnectedCorootSpanStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSimplyConnected G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isSemisimple.isConnectedReductive.isAffineHom
      ∀ (J : Type u) [Finite J]
        (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → P.IsReduced → P.corootSpan ℤ = ⊤

end Langlands.GroupScheme
