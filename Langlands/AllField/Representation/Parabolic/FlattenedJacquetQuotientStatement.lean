import Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement
import Langlands.AllField.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.AllField.Representation.Geometric.RefinementFunctors
/-!
# The flattened-to-iterated normalized Jacquet quotient

The existing quotient map is required to be a surjective intertwiner for the
actual flattened standard action and the transported iterated action.
-/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding FlattenedJacquetQuotientStatement
open Langlands.AllField.Parabolic

universe uF uV

/-- The actual flattened Jacquet quotient map is an equivariant surjection
onto the iterated normalized Jacquet module, pulled back along the constructed
flattened Levi equivalence. This includes rank zero and arbitrary carriers. -/
def FlattenedJacquetQuotientStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V),
    ∃ f : (T.normalizedJacquet (B.flatten S) ρ).IntertwiningMap
      ((T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)).comp
        (Geometric.flattenedLeviEquiv F B S).toMonoidHom),
      f.toLinearMap = Langlands.AllField.CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ ∧
        Function.Surjective f

end Langlands.AllField.Parabolic
