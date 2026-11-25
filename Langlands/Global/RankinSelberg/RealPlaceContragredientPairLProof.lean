import Langlands.Global.RankinSelberg.RealPlaceContragredientReduction
import Langlands.Global.RankinSelberg.RealStandardPairingReduction
import Langlands.Global.RankinSelberg.RealStandardDualPairingProof
import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLProof
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof

/-!
# Real-place pair factors of contragredient realizations

A proof of `Langlands.Global.RankinSelbergGlobal.RealPlaceContragredientPairLStatement`: the
Library's reduction `realPlaceContragredientPairLReduction` applied to the irreducibility of the
archimedean standard-module components of cuspidal realizations
(`Automorphic.cuspidalArchimedeanStandardIrreducible`) and to the local pairing statement, which
is the reduction `realStandardPairingPairLReduction` applied to the duality
`realStandardDualPairing` and the factor invariance `realStandardIntertwinerPairL`. See the
paired Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **Contragredient pair factors at a real place.** For actual cuspidal realizations `T`, `T'`
of `GL_(r+1)`, `GL_(t+1)` over a number field with contragredient realizations `Td`, `Td'`, and
real-place parameters `ds`, `es`, `dds`, `ees` of `T`, `T'`, `Td`, `Td'` at the same real place,
the pair `L`-factor of `dds` and `ees` has the same denominator as that of the dualized blocks
`ds.map dualBlock` and `es.map dualBlock`. -/
theorem realPlaceContragredientPairL : RealPlaceContragredientPairLStatement.{u} :=
  realPlaceContragredientPairLReduction Langlands.Automorphic.cuspidalArchimedeanStandardIrreducible
    (realStandardPairingPairLReduction realStandardDualPairing realStandardIntertwinerPairL)

end Langlands.Global.RankinSelbergGlobal
