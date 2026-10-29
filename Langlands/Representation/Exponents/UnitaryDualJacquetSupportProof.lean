import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
import Langlands.Representation.Exponents.CentralDualEigenQuotientProof
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof
import Langlands.Representation.Exponents.TemperedJacquetClassExponentProof

/-!
# Prescribed unitary dual-exponent tempered opposite support

A dual eigenfunctional gives an irreducible scalar quotient of the whole
opposite Jacquet module. Analytic class-exponent comparison makes it tempered,
and actual opposite adjunction gives the source embedding.
-/

namespace Langlands

open UnitaryDualJacquetSupport

universe uF uV

/-- Every prescribed unitary dual exponent supports opposite induction from an
actual irreducible tempered Levi quotient with exactly that scalar character. -/
theorem glUnitaryDualJacquetTemperedSupport :
    GLUnitaryDualJacquetTemperedSupportStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B A hi ht χ hχ
  let := T.leviTopologicalGroup B
  have hsm : IsSmooth A.ρ := ht.isAdmissible.1
  have hfin := Parabolic.oppositeJacquetFiniteGeneration.{uF, uV}
    p F T n B A hsm (moduleFinite_of_irreducible A.ρ hi)
  obtain ⟨S, hS, hSadm, hSχ, q, hq⟩ :=
    centralDualEigenQuotient.{uF, uF, uV}
      (B.Levi F.Carrier) (levi_compactOpen_cofinal T B)
      (Fin B.length → F.Carrierˣ) (B.blockScalarLevi F.Carrier)
      (B.blockScalarLevi_commute F.Carrier) χ
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A)
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
      hfin (jacquet_admissible T B A ht)
      (exists_dualEigenfunctional T B A χ hχ.1)
  have hclass := classExponent_of_quotient T B A S hS hSadm q hq
  refine ⟨S, hclass, hSχ, ?_, embedding_of_quotient T B A S hi hsm hS q hq⟩
  intro Q _ _ μ _
  exact (glTemperedJacquetClassExponent.{uF, uV, uV}
    p F T n hn B μ A hi ht S χ hclass hSχ).mpr hχ.2

end Langlands
