import Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements
import Langlands.AlgebraicGeometry.FiniteEtale.QuotientCoconeTools
import Langlands.AlgebraicGeometry.FiniteEtale.QuotientCoconeGluingProof

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Finite-group quotients of finite étale covers exist and are preserved by
the actual geometric fibre functor. -/
theorem geometricFiniteGroupQuotients
    {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricFiniteGroupQuotients s hfin := by
  intro G _ _
  have : HasColimitsOfShape (SingleObj G) (Cover S) :=
    ⟨fun D => by
      obtain ⟨c, hc, _⟩ := finiteGroupQuotientCocones S G D
      exact HasColimit.mk ⟨c, hc.some⟩⟩
  have : PreservesColimitsOfShape (SingleObj G) (pointFunctor s) :=
    ⟨fun {D} => by
      obtain ⟨c, hc, hpoints⟩ := finiteGroupQuotientCocones S G D
      obtain ⟨hsurj, horbit⟩ := hpoints Ω s
      exact preservesColimit_of_preserves_colimit_cocone hc.some
        (groupOrbitCoconeIsColimit ((pointFunctor s).mapCocone c) hsurj
          (fun x y h => (horbit x y).mp h))⟩
  exact ⟨inferInstance, fiberFunctor_preservesColimitsOfShape_large s hfin (SingleObj G)⟩

end Langlands.AlgebraicGeometry.FiniteEtale
