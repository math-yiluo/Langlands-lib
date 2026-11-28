import Langlands.Correspondence.Laumon.FieldMonodromyLadic
import Langlands.Correspondence.Laumon.FieldMonodromy.GaloisAut

/-!
# Proof of `LadicFieldMonodromyStatement`

The statement follows from `Langlands.Henniart.Laumon.ladicFieldMonodromyStatement_of_isHomeomorph`
and the homeomorphism `Langlands.Henniart.Laumon.fieldGaloisToAut_isHomeomorph` of the Galois group
of a field onto the automorphism group of its finite étale fibre functor.
-/

universe u uW

namespace Langlands.Henniart.Laumon

/-- **ℓ-adic monodromy of a field** (Laumon 1987, (2.1.2)–(2.1.2.1)). -/
theorem ladicFieldMonodromyStatement : LadicFieldMonodromyStatement.{u, uW} :=
  ladicFieldMonodromyStatement_of_isHomeomorph fun K Ω _ _ _ _ =>
    fieldGaloisToAut_isHomeomorph K Ω

end Langlands.Henniart.Laumon
