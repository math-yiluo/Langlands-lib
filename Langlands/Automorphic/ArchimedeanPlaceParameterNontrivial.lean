import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-! # Nonvanishing of the standard modules in archimedean place parameters -/

namespace Langlands.Automorphic

open Langlands.LocalFactor.Archimedean

/-- Real blocks of total rank `n` give a nonzero submodule of `O(n)`-finite functions. -/
theorem realStandardKFinite_ne_bot (n : ℕ) (ds : List RealBlock) (hrank : realRank ds = n) :
    realStandardKFinite n ds ≠ ⊥ :=
  Submodule.nontrivial_iff_ne_bot.mp (Archimedean.realStandardNontrivial n ds hrank)

/-- A list of `n` complex characters gives a nonzero submodule of `U(n)`-finite functions. -/
theorem complexStandardKFinite_ne_bot (n : ℕ) (ds : List ComplexCharacterData)
    (hlen : ds.length = n) :
    complexStandardKFinite n ds ≠ ⊥ :=
  Submodule.nontrivial_iff_ne_bot.mp (Archimedean.complexStandardNontrivial n ds hlen)

end Langlands.Automorphic
