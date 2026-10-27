import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Exponents.DualJacquetFinitenessProof
import Langlands.Representation.Exponents.ScalarSubquotientDualSpectrumProof
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
import Langlands.Representation.Classification.MaximalConeQuotient
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof

noncomputable section

namespace Langlands.DualJacquetClassExponent

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- An ordinary dual exponent gives an actual irreducible admissible quotient
of the whole opposite Jacquet module with the same scalar character. -/
theorem classExponent_of_dualExponent
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hA : Representation.IsIrreducible A.ρ)
    (hAadm : letI := T.topology; IsAdmissible A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    ∃ S : Rep.{uV} ℂ (B.Levi F.Carrier),
      T.IsOppositeJacquetClassExponent B A S ∧
      Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ := by
  let := T.topology
  have := T.leviTopologicalGroup B
  have hfinA := UnitaryDualJacquetSupport.moduleFinite_of_irreducible A.ρ hA
  have hfin := Parabolic.oppositeJacquetFiniteGeneration p F T n B A hAadm.1 hfinA
  have hadm := Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hAadm
  obtain ⟨φ, hφ, heig⟩ :=
    UnitaryDualJacquetSupport.exists_dualEigenfunctional T B A χ hχ
  obtain ⟨S, hS, hSadm, hscalar, q, hq⟩ :=
    MaximalConeQuotient.exists_irreducible_quotient
      (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B)
      (B.blockScalarLevi F.Carrier)
      (fun c g =>
        (Subgroup.mem_center_iff.mp (B.blockScalarLevi_mem_center F.Carrier c) g).symm)
      χ (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ hfin hadm φ hφ heig
  exact ⟨S, UnitaryDualJacquetSupport.classExponent_of_quotient T B A S hS hSadm q hq,
    hscalar⟩

/-- Generalized spanning indexed by actual dual exponents detects the scalar
character of any actual irreducible opposite Jacquet subquotient. -/
theorem dualExponent_of_classExponent_of_spanning
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hspan : (⨆ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
      (_ : T.IsDualJacquetExponent B A χ),
      (generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ).toSubmodule) = ⊤)
    (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hS : T.IsOppositeJacquetClassExponent B A S)
    (hscalar : Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ) :
    T.IsDualJacquetExponent B A χ := by
  obtain ⟨hSirr, _, U, q, hq⟩ := hS
  have := hSirr
  have : Nontrivial S := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (B.Levi F.Carrier)) S.ρ.asModule
  let Uc : Subrepresentation (T.splitCentreOppositeJacquet B A).ρ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun a => U.apply_mem_toSubmodule (B.blockScalarLevi F.Carrier a) }
  apply ScalarSubquotientDualSpectrum.scalarSubquotient_mem
    (T.splitCentreOppositeJacquet B A).ρ
    (T.IsDualJacquetExponent B A) hspan χ Uc S q.toLinearMap hq
  change ∀ (a : Fin B.length → F.Carrierˣ) (u : U.toSubmodule),
    q (U.toRepresentation (B.blockScalarLevi F.Carrier a) u) = (χ a : ℂ) • q u
  intro a u
  exact (Representation.IntertwiningMap.isIntertwining _ _ q _ u).trans (hscalar a (q u))

end Langlands.DualJacquetClassExponent

namespace Langlands

/-- Ordinary full-dual exponents are exactly the scalar split-center
characters of actual irreducible admissible opposite Jacquet subquotients. -/
theorem glDualJacquetClassExponent.{uF, uV} :
    GLDualJacquetClassExponentStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn B A hA hAadm χ
  constructor
  · exact DualJacquetClassExponent.classExponent_of_dualExponent T B A hA hAadm χ
  · rintro ⟨S, hS, hscalar⟩
    exact DualJacquetClassExponent.dualExponent_of_classExponent_of_spanning T B A
      (glDualJacquetFiniteness p F T n hn B A hA hAadm).2.2 S χ hS hscalar

end Langlands
