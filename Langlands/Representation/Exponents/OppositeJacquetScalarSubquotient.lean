import Langlands.Representation.Exponents.AdmissibleCentralSubquotientProof
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
import Langlands.Representation.Classification.ProductLeviCentralCharacter

noncomputable section

namespace Langlands

universe uF uV uW

/-- The scalar character of an actual irreducible opposite Jacquet
subquotient is an ordinary transpose-dual exponent. -/
theorem isDualJacquetExponent_of_scalar_oppositeClassExponent
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.ρ)
    (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hS : T.IsOppositeJacquetClassExponent B A S)
    (hscalar : Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ) :
    T.IsDualJacquetExponent B A χ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  obtain ⟨hSirr, _, U, q, hq⟩ := hS
  have := hSirr
  have : Nontrivial S := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (B.Levi F.Carrier)) S.ρ.asModule
  have hcont : Continuous (B.blockScalarLevi F.Carrier) := by
    change Continuous fun a : Fin B.length → F.Carrierˣ =>
      fun k => GeneralLinear.scalar (n := B.size k) (a k)
    exact continuous_pi fun k =>
      GeneralLinear.scalarContinuous.continuous.comp (continuous_apply k)
  have hc : Continuous (B.blockScalarToCenter F.Carrier) := hcont.subtype_mk _
  have hadm := Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hA
  have hdet := admissibleCentralSubquotient
    (B.Levi F.Carrier) (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B)
    (Fin B.length → F.Carrierˣ)
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A)
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
    (B.blockScalarToCenter F.Carrier) hc hadm χ U S q.toLinearMap hq
    (fun a u => (Representation.IntertwiningMap.isIntertwining _ _ q _ u).trans
      (hscalar a (q u)))
  exact hdet

end Langlands
