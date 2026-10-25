import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# The flattened-to-iterated normalized Jacquet quotient

The existing quotient map is required to be a surjective intertwiner for the
actual flattened standard action and the transported iterated action.
-/

namespace Langlands.Parabolic

universe uF uV

/-- The actual flattened Jacquet quotient map is an equivariant surjection
onto the iterated normalized Jacquet module, pulled back along the constructed
flattened Levi equivalence. This includes rank zero and arbitrary carriers. -/
def FlattenedJacquetQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    ∃ f : (T.normalizedJacquet (B.flatten S) ρ).IntertwiningMap
      ((T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)).comp
        (Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom),
      f.toLinearMap = CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ ∧
        Function.Surjective f

end Langlands.Parabolic
