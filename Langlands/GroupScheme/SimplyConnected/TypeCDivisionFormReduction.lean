import Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormStatement
import Langlands.GroupScheme.SimplyConnected.TypeCQuasiSplitInnerFormStatement
import Langlands.GroupScheme.SimplyConnected.SymplecticInnerFormAntihermitianStatement
import Langlands.GroupScheme.SimplyConnected.AntihermitianSymplecticSplitRankStatement
import Langlands.GroupScheme.SimplyConnected.TypeCDistinguishedVerticesStatement
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Reduction of the type-C division-form classification to four prerequisites -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The general type-C division-form classification follows from: a type-`C_n` simply
connected group is an inner form of `Sp_{2n}`; inner forms of `Sp_{2n}` are symplectic groups
of antihermitian division forms; the split rank of such a group is the Witt index; and the
distinguished vertices of such a group are `j * degree` for `1 ≤ j ≤` the Witt index. -/
theorem typeCDivisionForm_of_inputs
    (h1a : TypeCQuasiSplitInnerFormStatement.{u})
    (h1b : SymplecticInnerFormAntihermitianStatement.{u})
    (h2 : AntihermitianSymplecticSplitRankStatement.{u})
    (h3 : TypeCDistinguishedVerticesStatement.{u}) :
    TypeCDivisionFormStatement.{u} := by
  intro K _ G _ _ d n e hn hsc has hcartan
  obtain ⟨q, ⟨iq⟩⟩ := h1a K G d n e hn hsc hcartan
  obtain ⟨degree, m, hm, D, _, _, _, _, hdeg, hmd, hfin, σ, hsym, H, hH, hu, ⟨iso⟩⟩ :=
    h1b K G n q hn ⟨iq⟩
  have hrank : splitRank G = σ.wittIndex H := by
    rw [splitRank_eq_of_iso iso]
    exact h2 K D degree m σ H hfin hsym hH hu
  refine ⟨degree, m, hm, D, inferInstance, inferInstance, inferInstance, inferInstance,
    hdeg, hmd, hfin, σ, hsym, H, hH, hu, hrank.symm, ⟨iso⟩, fun a => ?_⟩
  rw [h3 K G d n e hn hsc has hcartan degree m D hdeg hmd hfin σ hsym H hH hu ⟨iso⟩ a, hrank]
  simp only [Nat.cast_le]

end Langlands.GroupScheme
