import Langlands.BaseChange.CyclicNormPullbackConductorOfPadicBase
import Langlands.BaseChange.RankOneSigmaLiftFromConcordance

/-! # Rank-one sigma-lift conductors over a supplied p-adic base -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis (Quasicharacter)
open RankinSelberg (rankOneCharacter)
open LocalField
open scoped BigOperators

universe u v uV uW

/-- The rank-one conductor identity for the original field carriers when the
base has a supplied finite p-adic structure. -/
def CuspidalSigmaLiftConductorRankOneOverPadicBaseStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] [Algebra F.Carrier E] [IsModuleTopology F.Carrier E]
      (σ : E ≃ₐ[F.Carrier] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear 1 F.Carrier) V)
      (hπ : IsAdmissible π), GeneralLinear.IsSupercuspidal π → π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      GeneralLinear.IsSupercuspidal P₁ → P₁.IsIrreducible →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear 1 E) W)
      (hP : IsAdmissible P),
      Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (A : SigmaIntertwiner σ 1 P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F.Carrier 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier 1
       haveI := LocalFieldTopology.generalLinear_t2Space E 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E 1
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ f d : ℕ, IsResidueDegree F.Carrier E f → IsDifferentExponent F.Carrier E d →
    ∀ X : Finset (F.Carrierˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      ∑ κ ∈ X, Conductor.firstFixedLevel (twist (κ.comp GeneralLinear.determinant) π) =
        (f : WithTop ℕ) * ((s : WithTop ℕ) * Conductor.firstFixedLevel P₁ +
          ((1 : ℕ) : WithTop ℕ) * (d : WithTop ℕ))

theorem cuspidalSigmaLiftConductorRankOneOverPadicBase :
    CuspidalSigmaLiftConductorRankOneOverPadicBaseStatement.{u, v, uV, uW} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro E _ _ _ _ _ _ σ l hcyc V _ _ π hπ hπsuper hπirr
    s k₁ hrank W₁ _ _ P₁ hP₁super hP₁irr W _ _ P hP horbit A c hlift f d hf hd X hX
  have hspos : 0 < s := Nat.pos_of_ne_zero fun h => by simp [h] at hrank
  have hsle : s ≤ s * (k₁ + 1) := Nat.le_mul_of_pos_right s (Nat.succ_pos k₁)
  have hkle : k₁ + 1 ≤ s * (k₁ + 1) := Nat.le_mul_of_pos_left (k₁ + 1) hspos
  rw [hrank] at hsle hkle
  have hs : s = 1 := by omega
  have hk₁ : k₁ = 0 := by omega
  subst s
  subst k₁
  obtain ⟨eOrbit⟩ := horbit
  obtain ⟨eBlock⟩ := sigmaOrbitProduct_one_equiv σ (Nat.succ_pos 0) P₁ hP₁super.1.1
  have eP₁ : P.Equiv P₁ := eOrbit.trans eBlock
  have hPirr := CyclicExtraction.irreducible_of_equiv eP₁.symm hP₁irr
  obtain ⟨χ, ⟨eπ⟩⟩ := GodementJacquet.exists_tateCharacterModel π hπ hπirr
  obtain ⟨η, ⟨eP⟩⟩ := GodementJacquet.exists_tateCharacterModel P hP hPirr
  let : FiniteDimensional F.Carrier E := hcyc.1
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F.Carrier)
  let : IsScalarTower (Padic p) F.Carrier E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F.Carrier E
  let K := PadicField.ofField (p := p) E
  have hcont : Continuous (algebraMap F.Carrier E) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F.Carrier E)
  let S : K.TopologicalData := suppliedPadicExtension T E hcont
  let : Algebra F.Carrier K.Carrier := (inferInstance : Algebra F.Carrier E)
  let : IsScalarTower (Padic p) F.Carrier K.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier E)
  let : TopologicalSpace K.Carrier := S.topology
  let : IsModuleTopology F.Carrier K.Carrier := (inferInstance : IsModuleTopology F.Carrier E)
  have hnorm :=
    rankOneSigmaLiftNormPullback p F K T S σ l hcyc V W π hπ P hP A c hlift χ η eπ eP
  obtain ⟨a, ha, hsum⟩ :=
    cyclicNormPullbackConductorOfPadicBase p F T E σ l hcyc χ η hnorm f d hf hd X hX
  have hP₁level := Conductor.firstFixedLevel_eq_multiplicativeConductor η (eP₁.symm.trans eP)
  have htwist (κ : F.Carrierˣ →* ℂˣ) (hκ : κ ∈ X) :
      Conductor.firstFixedLevel (twist (κ.comp GeneralLinear.determinant) π) =
        (a κ : WithTop ℕ) := by
    obtain ⟨χκ, hχκ, hcond⟩ := ha κ hκ
    have heq : twist (κ.comp GeneralLinear.determinant) (rankOneCharacter χ.toMonoidHom) =
        rankOneCharacter χκ.toMonoidHom := by
      rw [hχκ]
      ext g
      simp [rankOneCharacter, characterRepresentation, twist]
    have e : (twist (κ.comp GeneralLinear.determinant) π).Equiv
        (rankOneCharacter χκ.toMonoidHom) :=
      heq ▸ twistEquiv (κ.comp GeneralLinear.determinant) eπ
    exact (Conductor.firstFixedLevel_eq_multiplicativeConductor χκ e).trans
      (congrArg (fun n : ℕ => (n : WithTop ℕ)) hcond)
  calc
    _ = ∑ κ ∈ X, (a κ : WithTop ℕ) := Finset.sum_congr rfl htwist
    _ = _ := by
      rw [hP₁level]
      simp only [Nat.cast_one, one_mul]
      exact_mod_cast hsum

end Langlands.BaseChange
