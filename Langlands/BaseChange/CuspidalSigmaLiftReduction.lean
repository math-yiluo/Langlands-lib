import Langlands.BaseChange.CuspidalSigmaLiftExistenceStatement
import Langlands.BaseChange.SigmaDiscreteDescentStatement
import Langlands.BaseChange.SigmaLiftSelfPairLFactorStatement
import Langlands.BaseChange.NormTrivialCharacterGroup
import Langlands.BaseChange.SigmaOrbitDiscreteness
import Langlands.BaseChange.SigmaOrbitUntwisting
import Langlands.BaseChange.CuspidalSelfPairDescentProfile
import Langlands.BaseChange.RankOneNormNeighborhood
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.RankinSelberg.UnitaryCuspidalProductSelfPair

/-! # Reduction of the supercuspidal σ-lift converse to descent and self-pair comparison -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear CharZeroLocalField LocalField HarmonicAnalysis LocalFactor RankinSelberg
open LocalClassField ClassFieldTheory.Local
open _root_.Polynomial

universe u v uV uW

private theorem exists_selfDualHaar {p : ℕ} [Fact p.Prime] (F : PadicField p)
    (T : F.TopologicalData) :
    letI := T.topology
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier, Nonempty (PadicAbelian.SelfDualHaar T ψ) := by
  intro ψ
  obtain ⟨_, h⟩ := padicSelfDualMeasureExists F T
  obtain ⟨μ, hμ⟩ := h ψ
  exact ⟨⟨μ, hμ⟩⟩

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cuspidal_profile_of_unitarySigmaOrbitLift
    (hCompare : SigmaLiftSelfPairLFactorStatement.{u,v,uV,max v uW})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData) :
    letI := T.topology
    letI := S.topology
    letI := T.valuativeRel
    letI := S.valuativeRel
    letI := T.localField
    letI := S.localField
    ∀ [IsModuleTopology F.Carrier E.Carrier] (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
      (l s r : ℕ) (_hcyc : IsCyclicAlgebra σ l),
      let n := s * (r + 1)
      letI := LocalFieldTopology.generalLinear_t2Space F.Carrier n
      letI := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n
      letI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n
      letI := LocalFieldTopology.generalLinear_t2Space E.Carrier n
      letI := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
      letI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
      ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (P₁ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) W),
        P₁.IsIrreducible → IsSupercuspidal P₁ → IsUnitarizable P₁ →
        (∀ i : ℕ, Nonempty (P₁.Equiv (P₁.comp (entrywiseAut (σ ^ i) (r + 1)).toMonoidHom)) ↔
          s ∣ i) →
        let P := sigmaOrbitProduct σ s (Nat.succ_pos r) P₁
        ∀ (hP : IsAdmissible P), IsSigmaDiscreteSeries σ n P →
        ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
          (π : Representation ℂ (GeneralLinear n F.Carrier) V) (hπ : IsAdmissible π),
          π.IsIrreducible → T.IsSquareIntegrable π →
          ∀ (A : SigmaIntertwiner σ n P) (c : ℂ), IsSigmaLift σ l π hπ P hP A c →
          IsSupercuspidal π ∧ Nat.card (normTwistStabilizer E.Carrier π) = s := by
  rw [T.eq_canonicalTopologicalData, S.eq_canonicalTopologicalData]
  let TF := F.canonicalTopologicalData
  let SE := E.canonicalTopologicalData
  let := TF.topology
  let := SE.topology
  let := TF.valuativeRel
  let := SE.valuativeRel
  let := TF.localField
  let := SE.localField
  intro _ σ l s r hcyc n
  let := LocalFieldTopology.generalLinear_t2Space F.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n
  let := LocalFieldTopology.generalLinear_t2Space E.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
  intro W _ _ P₁ hi₁ hsc₁ hu₁ hperiod P hP hdisc V _ _ π hπ hi hsq A c hlift
  let : FiniteDimensional F.Carrier E.Carrier := hcyc.1
  let : IsAbelianGalois F.Carrier E.Carrier := hcyc.isAbelianGalois
  have hs := (sigmaConjugate_period_pos_dvd σ P₁ hperiod hcyc).1
  have hn : 0 < n := Nat.mul_pos hs (Nat.succ_pos r)
  obtain ⟨f, hf, hdegree⟩ := exists_pos_residueDegree TF SE
  let : CharZero F.Carrier := charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  let D := normTrivialCharacterGroup F.Carrier E.Carrier
  let : Finite D := Nat.finite_of_card_ne_zero
    ((card_normTrivialCharacterGroup hcyc).trans_ne hcyc.pos.ne')
  let : Fintype D := Fintype.ofFinite D
  let chars := (Finset.univ : Finset D).map ⟨Subtype.val, Subtype.val_injective⟩
  have hchars (κ : F.Carrierˣ →* ℂˣ) : κ ∈ chars ↔ IsNormTrivial E.Carrier κ := by
    dsimp only [chars]
    rw [Finset.mem_map]
    refine ⟨?_, fun h => ⟨⟨κ, h⟩, Finset.mem_univ _, rfl⟩⟩
    rintro ⟨η, -, rfl⟩
    exact η.property
  have hopen (κ : chars) : IsOpen (κ.val.ker : Set F.Carrierˣ) := by
    apply κ.val.ker.isOpen_of_mem_nhds
    refine Filter.mem_of_superset
      ((isOpen_normSubgroup_of_isAbelianGalois TF SE).mem_nhds (Subgroup.one_mem _)) ?_
    rintro _ ⟨x, rfl⟩
    exact (hchars κ.val).mp κ.property x
  obtain ⟨ψF⟩ := padicUnitaryAdditiveCharacterExists F TF
  obtain ⟨ψE⟩ := padicUnitaryAdditiveCharacterExists E SE
  obtain ⟨μF⟩ := exists_selfDualHaar F TF ψF
  obtain ⟨μE⟩ := exists_selfDualHaar E SE ψE
  let C (i : Fin s) : SupercuspidalRep.{v,uW} (F := E.Carrier) (n := r + 1) := by
    let ρ := P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (r + 1)).toMonoidHom
    have hsc : IsSupercuspidal ρ := isSupercuspidal_comp_entrywiseAut (σ ^ (i : ℕ)) P₁ hsc₁
    exact ⟨SmoothRep.of ρ hsc.1.1,
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff P₁ (entrywiseAut _ _)).mpr hi₁, hsc⟩
  obtain ⟨Q, hQ, hne, horder⟩ := unitaryCuspidalProduct_selfPair E hs ψE μE C
    (fun i => hu₁.comp _) (sigmaConjugates_pairwise_inequivalent σ P₁ hperiod)
  have hQU : IsPadicRankLPolynomial E ψE μE.val P (smoothContragredient P) Q := hQ
  choose R hR using fun κ : chars => exists_twistedSelfPairPolynomial F ψF μF hn π hi hsq κ.val (hopen κ)
  have hprod := hCompare p F E σ l f n hcyc hdegree hn V _ π hπ P hP A c hi hsq hdisc hlift
    ψF μF ψE μE chars hchars Q R hQU hR
  have hq : SE.residueCardinality = TF.residueCardinality ^ f := hdegree
  have hne' : Q.eval ((TF.residueCardinality : ℂ) ^ f) ≠ 0 := by
    rw [← Nat.cast_pow, ← hq]
    exact hne
  exact cuspidalSelfPairDescentProfile p F E.Carrier n hn V π hi hsq ψF μF chars hchars hopen
    f s hf Q R hR hne' horder hprod

/-- Discrete descent and the self-pair Euler identity imply the supercuspidal
σ-lift converse. The induced upper carrier lies in `Type (max v uW)`. -/
def CuspidalSigmaLiftReductionStatement : Prop :=
  SigmaDiscreteDescentStatement.{u, v, uV, max v uW} →
  SigmaLiftSelfPairLFactorStatement.{u, v, uV, max v uW} →
  CuspidalSigmaLiftExistenceStatement.{u, v, uV, uW}

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalize the upper orbit, descend it, and detect lower supercuspidality
and the twist stabilizer by comparing the self-pair denominators. -/
theorem cuspidalSigmaLiftExistence_of_descent_and_selfPair :
    CuspidalSigmaLiftReductionStatement.{u, v, uV, uW} := by
  intro hDesc hCompare F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc s n hn W _ _ P₁ hsc₁ hi₁ hperiod
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let : FiniteDimensional F E := hcyc.1
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨t, hi', hsc', hu'⟩ := exists_unitary_realPowerTwist P₁ hn hi₁ hsc₁
  let P₁' := realPowerTwist ((LocalFieldData.ofInstances E).determinantNorm (r + 1)) t P₁
  have hperiod' (i : ℕ) :
      Nonempty (P₁'.Equiv (P₁'.comp (entrywiseAut (σ ^ i) (r + 1)).toMonoidHom)) ↔ s ∣ i :=
    (nonempty_equiv_conjugate_realPowerTwist_iff P₁ (σ ^ i) t).trans (hperiod i)
  let n := s * (r + 1)
  let P := sigmaOrbitProduct σ s hn P₁'
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let := LocalFieldTopology.generalLinear_t2Space E n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
  have hDisc : IsSigmaDiscreteSeries σ n P :=
    unitarySigmaOrbitDiscreteness F E σ l s (r + 1) hcyc hn W P₁' hi' hsc' hu' hperiod'
  let A := hDisc.2.2.2.1.some
  have hP : IsAdmissible P := hDisc.1
  obtain ⟨V, addV, modV, π, hπ, c, hiπ, hsqπ, hLift⟩ := hDesc F E σ l n hcyc P hP hDisc A
  let := addV
  let := modV
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let T := topologicalData F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : TopologicalSpace L.Carrier := S.topology
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : IsModuleTopology K.Carrier L.Carrier := (inferInstance : IsModuleTopology F E)
  obtain ⟨hscπ, hcount⟩ := cuspidal_profile_of_unitarySigmaOrbitLift hCompare T S σ l s r hcyc
    P₁' hi' hsc' hu' hperiod' hP hDisc π hπ hiπ hsqπ A c hLift
  obtain ⟨hI, hSC, hirr, hcard, hπ₀, hP₀, A₀, lift₀⟩ :=
    exists_cuspidalSigmaLift_of_realPowerTwist F E σ hcyc hn P₁ t hP hDisc.2.1 π hπ A c
      hscπ hiπ hcount hLift
  exact ⟨hI, hP₀, V, addV, modV, _, hπ₀, A₀, c, hSC, hirr, hcard, lift₀⟩

end Langlands.BaseChange
