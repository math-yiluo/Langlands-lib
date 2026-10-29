import Langlands.Representation.Exponents.WeakCriticalStatement
import Langlands.Representation.Exponents.DualCharacterQuotient
import Langlands.Representation.Exponents.DualCharacterMaximalLayerProof
import Langlands.Representation.Exponents.WeakCriticalTopLayerL2Proof
import Langlands.Representation.Exponents.DualJacquetFinitenessProof
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
import Langlands.Representation.Classification.MaximalConeQuotient
import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Group.GL.CompactOpen

/-! Prescribed weakly critical discrete-series opposite support.
The proof extracts a quotient of a nonzero maximal central-defect layer
and applies the published all-Haar square-integrability theorem to it. -/

noncomputable section

namespace Langlands.WeakCriticalSupport

universe uF uV uW uG uC

open Exponents

/-- A nonzero scalar representation supplies the full-dual eigenfunctional
required by prescribed-character quotient extraction. -/
theorem exists_dual_eigenfunctional_of_scalar
    {G : Type uG} [Group G] {C : Type uC} [Group C]
    (W : Rep.{uV} ℂ G) [Nontrivial W] (z : C →* G) (χ : C →* ℂˣ)
    (hχ : Classification.HasScalarCharacter W.ρ z χ) :
    ∃ φ : Module.Dual ℂ W, φ ≠ 0 ∧
      ∀ (c : C) (v : W), φ (W.ρ (z c) v) = (χ c : ℂ) * φ v := by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  refine ⟨φ, ?_, ?_⟩
  · intro hzero
    apply hφ
    rw [hzero]
    rfl
  · intro c w
    rw [hχ c w, map_smul, smul_eq_mul]

/-- Irreducibility supplies finite generation over the full group algebra.
It does not supply finite generation after restriction to the Levi. -/
theorem finite_of_irreducible
    {G : Type uG} [Group G] (A : Rep.{uV} ℂ G)
    (hA : Representation.IsIrreducible A.ρ) :
    Module.Finite (MonoidAlgebra ℂ G) A.ρ.asModule := by
  let := (Representation.irreducible_iff_isSimpleModule_asModule A.ρ).mp hA
  infer_instance

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Pullback at the standard presentation acts by conjugation by one. -/
theorem standard_pullbackRep (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    (ConjugateBlockPair.standard B).pullbackRep A = A := by
  have hρ : A.ρ.comp
      (MulAut.conj (1 : GeneralLinear n F.Carrier)).toMonoidHom = A.ρ := by
    ext g v
    change A.ρ (1 * g * 1⁻¹) v = A.ρ g v
    simp
  exact congrArg (fun ρ : Representation ℂ (GeneralLinear n F.Carrier) A =>
    Rep.of ρ) hρ

/-- The unitary exponent in criticality is an exponent of the original source
in standard coordinates. The full refinement condition is retained separately. -/
theorem unitaryExponent_of_critical
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsWeaklyCriticalDualJacquetExponent
      (ConjugateBlockPair.standard B) A χ) :
    T.IsUnitaryDualJacquetExponent B A χ := by
  have h := hχ.1
  change T.IsUnitaryDualJacquetExponent B
    ((ConjugateBlockPair.standard B).pullbackRep A) χ at h
  rwa [standard_pullbackRep B A] at h

/-- An actual nonzero dual eigenspace excludes nilpotence index zero. -/
theorem dualIndex_ne_zero
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    T.dualJacquetExponentNilpotenceIndex B A χ ≠ 0 := by
  intro hz
  have hbound := (T.dualJacquetExponentNilpotenceIndex_le_iff B A χ 0).mp
    (show T.dualJacquetExponentNilpotenceIndex B A χ ≤ (0 : ℕ∞) from hz.le)
  apply hχ.2
  apply le_antisymm
  · intro v hv
    have hgen : v ∈ generalizedCommutativeCharacterSpace
        (T.splitCentreDualJacquet B A).ρ χ :=
      (mem_generalizedCommutativeCharacterSpace _ _ _).mpr
        ⟨1, (mem_commutativeCharacterSpace _ _ _ _).mp hv⟩
    have hv0 := hbound hgen
    simpa only [commutativeCharacterSpace, centralCharacterSpace_zero] using hv0
  · exact bot_le

/-- Once a finite bound has been proved, an occurring exponent has a positive
natural exact index. This lemma supplies no finiteness theorem. -/
theorem exists_positive_exact_index
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ)
    (hfin : T.dualJacquetExponentNilpotenceIndex B A χ < ⊤) :
    ∃ d : ℕ, 0 < d ∧
      T.dualJacquetExponentNilpotenceIndex B A χ = (d : ℕ∞) := by
  let d := ENat.lift (T.dualJacquetExponentNilpotenceIndex B A χ) hfin
  have hd : (d : ℕ∞) = T.dualJacquetExponentNilpotenceIndex B A χ :=
    ENat.natCast_lift _ hfin
  refine ⟨d, Nat.pos_of_ne_zero ?_, hd.symm⟩
  intro hd0
  apply dualIndex_ne_zero T B A χ hχ
  rw [← hd, hd0, Nat.cast_zero]

/-- Published dual finiteness makes the prescribed critical exponent's exact
index a positive natural number, under the original source hypotheses. -/
theorem exists_positive_exact_index_of_critical
    (hn : 0 < n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hAirr : Representation.IsIrreducible A.ρ)
    (hA : T.IsTempered A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsWeaklyCriticalDualJacquetExponent
      (ConjugateBlockPair.standard B) A χ) :
    ∃ d : ℕ, 0 < d ∧
      T.dualJacquetExponentNilpotenceIndex B A χ = (d : ℕ∞) := by
  have hdual := (unitaryExponent_of_critical T B A χ hχ).1
  have hfinite := glDualJacquetFiniteness p F T n hn B A hAirr hA.isAdmissible
  exact exists_positive_exact_index T B A χ hdual (hfinite.2.1 χ hdual)

/-- The actual opposite Jacquet module is finitely generated over the Levi
group algebra when the source is irreducible and smooth. -/
theorem oppositeJacquet_finite
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hAsmooth : letI := T.topology; IsSmooth A.ρ)
    (hAirr : Representation.IsIrreducible A.ρ) :
    Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule := by
  exact Parabolic.oppositeJacquetFiniteGeneration p F T n B A hAsmooth
    (finite_of_irreducible A hAirr)

/-- Admissibility transfers to every actual defect image via its canonical
surjection from the whole opposite Jacquet module. -/
theorem defectRange_isAdmissible
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    letI := T.topology
    IsAdmissible (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  apply Unramified.SphericalExistence.isAdmissible_of_surjective
    (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B)
    (T.dualJacquetCharacterDefectRangeMap B A χ a k)
    (T.dualJacquetCharacterDefectRangeMap_surjective B A χ a k)
  exact Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hA

/-- Group-algebra finite generation transfers along the same canonical
surjection. Finite generation of the Jacquet module remains a premise here. -/
theorem defectRange_finite
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hJ : Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (a : Fin B.length → F.Carrierˣ) (k : ℕ) :
    Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
      (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ.asModule := by
  let := hJ
  exact Module.Finite.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (T.dualJacquetCharacterDefectRangeMap B A χ a k))
    (T.dualJacquetCharacterDefectRangeMap_surjective B A χ a k)

/-- A quotient of the selected layer is also a quotient of the whole Jacquet
module, and therefore gives the actual opposite-induction embedding. -/
theorem embedding_of_layer_quotient
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hAsmooth : letI := T.topology; IsSmooth A.ρ)
    (hAirr : Representation.IsIrreducible A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hS : Representation.IsIrreducible S.ρ)
    (q : (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ.IntertwiningMap
      S.ρ) (hq : Function.Surjective q) :
    letI := T.topology
    ∃ j : A.ρ.IntertwiningMap (T.normalizedOppositeParabolicInduced B S.ρ),
      Function.Injective j := by
  apply (OppositeSupport.quotient_iff_embedding T B A.ρ S.ρ hAsmooth hAirr hS).mp
  exact ⟨q.comp (T.dualJacquetCharacterDefectRangeMap B A χ a k),
    hq.comp (T.dualJacquetCharacterDefectRangeMap_surjective B A χ a k)⟩

/-- A nonzero scalar defect layer has an actual irreducible admissible quotient
in the original carrier universe, with the prescribed character, class witness
and opposite embedding. Nonzeroness and scalar action of the maximal layer
remain separate obligations. -/
theorem exists_support_of_scalar_layer
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hAirr : Representation.IsIrreducible A.ρ)
    (hA : letI := T.topology; IsAdmissible A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (hne : Nontrivial (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k))
    (hscalar : Classification.HasScalarCharacter
      (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ
      (B.blockScalarLevi F.Carrier) χ) :
    letI := T.topology
    ∃ S : Rep.{uV} ℂ (B.Levi F.Carrier),
      T.IsOppositeJacquetClassExponent B A S ∧
      Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ ∧
      (∃ q : (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ.IntertwiningMap
        S.ρ, Function.Surjective q) ∧
      ∃ j : A.ρ.IntertwiningMap (T.normalizedOppositeParabolicInduced B S.ρ),
        Function.Injective j := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let := hne
  obtain ⟨φ, hφ, heig⟩ := exists_dual_eigenfunctional_of_scalar
    (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k)
    (B.blockScalarLevi F.Carrier) χ hscalar
  have hz : ∀ c g, B.blockScalarLevi F.Carrier c * g =
      g * B.blockScalarLevi F.Carrier c := by
    intro c g
    exact (Subgroup.mem_center_iff.mp (B.blockScalarLevi_mem_center F.Carrier c) g).symm
  obtain ⟨S, hS, hSadm, hSscalar, q, hq⟩ :=
    MaximalConeQuotient.exists_irreducible_quotient
      (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B) (B.blockScalarLevi F.Carrier) hz χ
      (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ
      (defectRange_finite T B A (oppositeJacquet_finite T B A hA.1 hAirr) χ a k)
      (defectRange_isAdmissible T B A hA χ a k) φ hφ heig
  refine ⟨S, ?_, hSscalar, ⟨q, hq⟩, ?_⟩
  · exact UnitaryDualJacquetSupport.classExponent_of_quotient T B A S hS hSadm
      (q.comp (T.dualJacquetCharacterDefectRangeMap B A χ a k))
      (hq.comp (T.dualJacquetCharacterDefectRangeMap_surjective B A χ a k))
  · exact embedding_of_layer_quotient T B A hA.1 hAirr χ a k S hS q hq

/-- The algebraic maximal-layer assertion and its square-integrability
criterion assemble the prescribed support statement. -/
theorem support_of_layer_inputs
    (hmax : DualCharacterMaximalLayerStatement.{uF, uF, uV})
    (hL2 : GLWeaklyCriticalTopLayerL2Statement.{uF, uV, uV}) :
    GLWeaklyCriticalDiscreteSeriesSupportStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn B A hAirr hA χ hχ
  obtain ⟨d, hd, hindex⟩ :=
    exists_positive_exact_index_of_critical T B hn A hAirr hA χ hχ
  obtain ⟨⟨a, hne⟩, hscalar⟩ :=
    hmax (B.Levi F.Carrier) (Fin B.length → F.Carrierˣ)
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A)
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
      (B.blockScalarLevi F.Carrier) (B.blockScalarLevi_mem_center F.Carrier)
      χ d hd hindex
  obtain ⟨S, hS, hSscalar, ⟨q, hq⟩, hj⟩ :=
    exists_support_of_scalar_layer T B A hAirr hA.isAdmissible χ a (d - 1)
      hne (hscalar a)
  refine ⟨S, hS, hSscalar, ?_, hj⟩
  exact hL2 p F T n hn B A hAirr hA χ hχ d hd hindex a S
    hS.1 hS.2.1 hSscalar q hq

/-- The published maximal-layer theorem discharges the algebraic premise.
The exact all-Haar selected-layer assertion remains an explicit premise. -/
theorem support_of_top_layer_l2
    (hL2 : GLWeaklyCriticalTopLayerL2Statement.{uF, uV, uV}) :
    GLWeaklyCriticalDiscreteSeriesSupportStatement.{uF, uV} :=
  support_of_layer_inputs dualCharacterMaximalLayer hL2

end Langlands.WeakCriticalSupport

namespace Langlands

universe uF uV

/-- Every prescribed weakly critical exponent of an irreducible tempered source
gives discrete-series opposite-inducing data with that exact scalar character. -/
theorem glWeaklyCriticalDiscreteSeriesSupport :
    GLWeaklyCriticalDiscreteSeriesSupportStatement.{uF, uV} :=
  WeakCriticalSupport.support_of_top_layer_l2 glWeaklyCriticalTopLayerL2

end Langlands
