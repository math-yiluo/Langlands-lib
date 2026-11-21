import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLReduction
import Langlands.Representation.Archimedean.RealStandardEllipticCartanComparisonProof
import Langlands.Representation.Archimedean.RealStandardEllipticCartanReduction

/-! # Pair L-factors of isomorphic irreducible real standard modules -/

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean

/-- A nonzero intertwiner between rank-matched irreducible real standard modules
preserves the pair L-factor denominators against any real block list in either slot. -/
theorem realStandardIntertwinerPairL : RealStandardIntertwinerPairLStatement :=
  realStandardIntertwinerPairLReduction
    (realStandardEllipticCartanReduction
      RealStandardEllipticCartan.realStandardEllipticCartanComparison)

end Langlands.Global.RankinSelbergGlobal
