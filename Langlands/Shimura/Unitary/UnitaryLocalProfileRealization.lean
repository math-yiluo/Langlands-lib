import Langlands.Shimura.Unitary.UnitaryProfileDiscriminantValues

/-! # Global realization of unitary local profiles -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra

/-- The compatible signed split Brauer and real signature data are realized over the
given CM extension, with maximal Witt index at every other finite place. -/
theorem unitaryLocalProfileRealization (E : Type u) (K : Type v)
    [Field E] [NumberField E] [Field K] [NumberField K]
    [IsTotallyReal E] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K] :
    UnitaryLocalProfileRealizationStatement E K := by
  classical
  intro n hn s hs positive a r hr hc
  let W : UnitaryLocalProfileWitness (lt_trans Nat.zero_lt_one hn) positive a r :=
    if he : Even n then
      let P := initialUnitaryProfile hn positive a r hs hr
      realizeEvenUnitaryLocalProfileOfDiscriminant hn positive a r he P hc
        (unitaryProfileDiscriminantValues hn positive a r he.two_dvd hs P)
    else
      realizeOddUnitaryLocalProfile hn (Nat.not_even_iff_odd.mp he) hs positive a r hr
  exact ⟨W.carrier, W.ring, W.baseAlgebra, W.centerAlgebra, W.tower, W.data, W.signatures,
    W.maximalWitt, W.signedBrauer⟩

end Langlands.Shimura.FiniteUnitary
