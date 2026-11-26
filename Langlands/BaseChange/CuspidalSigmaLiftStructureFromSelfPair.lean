import Langlands.BaseChange.CuspidalSigmaLiftStructureReduction
import Langlands.BaseChange.PadicCanonicalDataEquality
import Langlands.BaseChange.PadicSigmaLiftOrbitIdentification
import Langlands.BaseChange.RelativeNormRealTwist
import Langlands.BaseChange.SigmaLiftSelfPairLFactorStatement
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! # Supercuspidal σ-lift structure from the self-pair comparison -/

noncomputable section

namespace Langlands.BaseChange

open CharZeroLocalField GeneralLinear HarmonicAnalysis JacquetLanglands LocalField

universe u v uV uW

private theorem exists_finset_normTrivial {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type v} [Field E] [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) :
    ∃ S : Finset (Fˣ →* ℂˣ), ∀ κ, κ ∈ S ↔ IsNormTrivial E κ := by
  classical
  let H := normTrivialCharacterGroup F E
  have hH : Nat.card H ≠ 0 := (card_normTrivialCharacterGroup h).trans_ne h.pos.ne'
  let : Finite H := Nat.finite_of_card_ne_zero hH
  let : Fintype H := Fintype.ofFinite H
  let f : H ↪ (Fˣ →* ℂˣ) := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨Finset.univ.map f, fun κ => ?_⟩
  constructor
  · intro hκ
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hκ
    exact a.property
  · intro hκ
    exact Finset.mem_map.mpr ⟨⟨κ, hκ⟩, Finset.mem_univ _, rfl⟩

set_option maxHeartbeats 4500000 in
private theorem padicIdentification_from_selfPair
    (hSelf : SigmaLiftSelfPairLFactorStatement.{u, v, uV, uW})
    {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
    (T : K.TopologicalData) (U : L.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := U.topology
    letI := U.valuativeRel
    letI := U.localField
    ∀ [IsModuleTopology K.Carrier L.Carrier]
      (σ : L.Carrier ≃ₐ[K.Carrier] L.Carrier) (l n : ℕ), IsCyclicAlgebra σ l → 0 < n →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n K.Carrier) V) (hπ : IsAdmissible π),
      π.IsIrreducible → IsSupercuspidal π → T.IsSquareIntegrable π →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear n L.Carrier) W) (hP : IsAdmissible P),
      IsSigmaDiscreteSeries σ n P →
    ∀ (A : SigmaIntertwiner σ n P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space K.Carrier n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace K.Carrier n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace K.Carrier n
       haveI := LocalFieldTopology.generalLinear_t2Space L.Carrier n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace L.Carrier n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace L.Carrier n
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ (t m : ℕ) (hm : 0 < m) (h : t * m = n)
      {Y : Type uW} [AddCommGroup Y] [Module ℂ Y]
      (P₁ : Representation ℂ (GeneralLinear m L.Carrier) Y),
      P₁.IsIrreducible → U.IsSquareIntegrable P₁ →
      (∀ i : ℕ, Nonempty (P₁.Equiv (P₁.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i) →
      Nonempty (P.Equiv ((sigmaOrbitProduct σ t hm P₁).comp
        (GeneralLinear.reindex (R := L.Carrier) (finCongr h)).symm.toMonoidHom)) →
      IsSupercuspidal P₁ ∧ t = Nat.card (normTwistStabilizer L.Carrier π) := by
  rw [T.eq_of_same_padicField K.canonicalTopologicalData, U.eq_of_same_padicField L.canonicalTopologicalData]
  let TC := K.canonicalTopologicalData
  let UC := L.canonicalTopologicalData
  let : TopologicalSpace K.Carrier := TC.topology
  let : ValuativeRel K.Carrier := TC.valuativeRel
  let : IsNonarchimedeanLocalField K.Carrier := TC.localField
  let : TopologicalSpace L.Carrier := UC.topology
  let : ValuativeRel L.Carrier := UC.valuativeRel
  let : IsNonarchimedeanLocalField L.Carrier := UC.localField
  let : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier
  intro _ σ l n hcyc hn V _ _ π hπ hπi hπs hπq W _ _ P hP hPd A c hLift
    t m hm h Y _ _ P₁ hP₁i hP₁q hperiod horbit
  let : FiniteDimensional K.Carrier L.Carrier := hcyc.1
  obtain ⟨f, hf, hres⟩ := exists_pos_residueDegree TC UC
  obtain ⟨S, hS⟩ := exists_finset_normTrivial hcyc
  obtain ⟨ψF⟩ := padicUnitaryAdditiveCharacterExists K TC
  obtain ⟨ψE⟩ := padicUnitaryAdditiveCharacterExists L UC
  obtain ⟨_, hνF⟩ := padicSelfDualMeasureExists K TC
  obtain ⟨_, hνE⟩ := padicSelfDualMeasureExists L UC
  obtain ⟨μF, hmF⟩ := hνF ψF
  obtain ⟨μE, hmE⟩ := hνE ψE
  let νF : LocalFactor.PadicAbelian.SelfDualHaar TC ψF := ⟨μF, hmF⟩
  let νE : LocalFactor.PadicAbelian.SelfDualHaar UC ψE := ⟨μE, hmE⟩
  exact padicSigmaLiftOrbitIdentification_of_selfPair K L σ ψF νF ψE νE hf hres hn hm h
    π hπi hπs hπq P P₁ hP₁i hP₁q hperiod horbit S hS
    (hSelf p K L σ l f n hcyc hres hn V W π hπ P hP A c hπi hπq hPd hLift ψF νF ψE νE S hS)

set_option maxHeartbeats 2000000 in
/-- Use the p-adic realizations of the same field carriers to apply the local
self-pair comparison and its orbit consequence. -/
theorem discreteSigmaLiftOrbitIdentification_of_selfPair
    (hSelf : SigmaLiftSelfPairLFactorStatement.{u, v, uV, uW}) :
    DiscreteSigmaLiftOrbitIdentificationStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l n hcyc hn
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let : FiniteDimensional F E := hcyc.1
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let K := padicField F
  let L := PadicField.ofField (p := p) E
  let T := topologicalData F
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let U : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : TopologicalSpace L.Carrier := U.topology
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : IsModuleTopology K.Carrier L.Carrier := (inferInstance : IsModuleTopology F E)
  intro V _ _ π hπ hπi hπs hπq W _ _ P hP hPd A c hLift
    t m hm h Y _ _ P₁ hP₁i hP₁q hperiod horbit
  exact padicIdentification_from_selfPair hSelf K L T U σ l n hcyc hn
    π hπ hπi hπs hπq P hP hPd A c hLift t m hm h P₁ hP₁i hP₁q hperiod horbit

/-- The forward supercuspidal structure follows from existence and uniqueness of
lifts, σ-discrete orbit decomposition, and the certified self-pair identity. -/
theorem cuspidalSigmaLiftStructure_from_selfPair
    (hExists : DiscreteSeriesSigmaLiftStatement.{u, v, uV, uW})
    (hUnique : SigmaLiftUniquenessStatement.{u, v, uV, uW, uW})
    (hOrbit : SigmaDiscreteSeriesOrbitDecompositionStatement.{u, v, uW})
    (hSelf : SigmaLiftSelfPairLFactorStatement.{u, v, uV, uW}) :
    CuspidalSigmaLiftStructureStatement.{u, v, uV, uW} :=
  cuspidalSigmaLiftStructure_of_normalized hExists hUnique hOrbit
    (discreteSigmaLiftOrbitIdentification_of_selfPair hSelf)

end Langlands.BaseChange
