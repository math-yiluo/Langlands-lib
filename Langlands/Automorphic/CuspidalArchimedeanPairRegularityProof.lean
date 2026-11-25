import Langlands.Automorphic.CuspidalArchimedeanPairRegularityReductionProof
import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Automorphic.CuspidalArchimedeanStandardGenericProof
import Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof
import Langlands.Representation.Archimedean.RealUnitaryGenericPairRegularityProof
import Langlands.Representation.Archimedean.ComplexUnitaryGenericPairRegularityProof

/-!
# Archimedean pair regularity of unitary cuspidal realizations

A proof of `Langlands.Automorphic.CuspidalArchimedeanPairRegularityStatement`: the Library's
reduction `cuspidalArchimedeanPairRegularityReduction` applied to the admissibility,
irreducibility, genericity and unitarizability of the archimedean standard-module components
and to the real and complex cases of Getz–Hahn, Theorem 11.5.2, for carriers in `Type`. See the
paired Markdown.
-/

universe u

namespace Langlands.Automorphic

/-- **Archimedean pair regularity (Getz–Hahn 2024, p. 309).** For actual cuspidal realizations
`T` of `GL_{r+1}` and `T'` of `GL_{t+1}` over a number field with unitary central characters,
and standard-module parameters `ds`, `ds'` of `T`, `T'` at the same real (resp. complex) place,
the denominator of the archimedean pair `L`-factor `L(s, ds × ds')` does not vanish when
`1 ≤ Re(s)`. -/
theorem cuspidalArchimedeanPairRegularity : CuspidalArchimedeanPairRegularityStatement.{u} :=
  cuspidalArchimedeanPairRegularityReduction archimedeanStandardAdmissible
    cuspidalArchimedeanStandardIrreducible cuspidalArchimedeanStandardGeneric
    cuspidalArchimedeanStandardUnitarizable
    Archimedean.realUnitaryGenericPairRegularity.{0, 0}
    Archimedean.complexUnitaryGenericPairRegularity.{0, 0}

end Langlands.Automorphic
