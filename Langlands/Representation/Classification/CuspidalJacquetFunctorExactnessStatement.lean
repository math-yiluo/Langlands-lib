import Langlands.Representation.Classification.CuspidalJacquetFunctors
import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Categorical properties of the actual upper and opposite Jacquet functors. -/

namespace Langlands

open CategoryTheory

universe uF uV

/-- Both actual Jacquet functors are additive and preserve monomorphisms and
epimorphisms on the smooth category for the supplied field topology. -/
def CuspidalJacquetFunctorExactnessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.generalLinearTopology n
    (CuspidalJacquetMultiplicity.upperFunctor.{uF, uV} T B).Additive ∧
    (CuspidalJacquetMultiplicity.upperFunctor.{uF, uV} T B).PreservesMonomorphisms ∧
    (CuspidalJacquetMultiplicity.upperFunctor.{uF, uV} T B).PreservesEpimorphisms ∧
    (CuspidalJacquetMultiplicity.oppositeFunctor.{uF, uV} T B).Additive ∧
    (CuspidalJacquetMultiplicity.oppositeFunctor.{uF, uV} T B).PreservesMonomorphisms ∧
    (CuspidalJacquetMultiplicity.oppositeFunctor.{uF, uV} T B).PreservesEpimorphisms

end Langlands
