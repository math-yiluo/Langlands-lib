import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplitStatement
import Langlands.GroupScheme.Rational.FrobeniusStableBorel
import Langlands.GroupScheme.Absolute.FrobeniusBorelDescent
import Langlands.GroupScheme.Absolute.BorelConjugacyProof

/-! # Connected reductive groups over finite fields are quasi-split -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Every connected reductive group over a finite field is quasi-split. -/
theorem finiteFieldQuasiSplit : FiniteFieldQuasiSplitStatement.{u} := by
  intro k _ _ G hG
  let : Fintype k := Fintype.ofFinite k
  let := hG.smooth
  let := hG.isAffineHom
  let := hG.connectedSpace
  obtain ⟨B, i, hi, hF⟩ :=
    exists_frobeniusStableBorel_of_borelConjugacy k (AlgebraicClosure k) G borelConjugacy.{u}
  exact isQuasiSplit_of_borel_frobeniusTransport_eq hG hi hF

end Langlands.GroupScheme
