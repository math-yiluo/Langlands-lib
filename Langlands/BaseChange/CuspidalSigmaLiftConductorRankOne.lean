import Langlands.BaseChange.CuspidalSigmaLiftConductorStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentityStatement
import Langlands.BaseChange.RankOneSigmaLiftNorm
import Langlands.Representation.Conductor.RankOneMultiplicativeConductor
import Langlands.Representation.GodementJacquet.TateCharacterReduction
import Langlands.Representation.Smooth.Factorization.CyclicExtractionProof

/-!
# Reduction of the rank-one sigma-lift conductor identity

The cyclic norm pullback formula for character conductors supplies the
rank-one instance of the cuspidal sigma-lift conductor statement.
-/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis (Quasicharacter)
open RankinSelberg (rankOneCharacter)
open scoped BigOperators

universe u v uV uW

/-- The local conductor identity for a norm pullback of a continuous
quasicharacter, using the actual principal-unit conductor on each field. -/
def CyclicNormPullbackConductorStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (χ : Quasicharacter F) (η : Quasicharacter E),
      η.toMonoidHom = χ.toMonoidHom.comp (Units.map (Algebra.norm F : E →* F)) →
    ∀ f d : ℕ, IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      ∃ a : (Fˣ →* ℂˣ) → ℕ,
        (∀ κ ∈ X, ∃ χκ : Quasicharacter F,
          χκ.toMonoidHom = κ * χ.toMonoidHom ∧
          (LocalFieldData.ofInstances F).multiplicativeConductor χκ = a κ) ∧
        ∑ κ ∈ X, a κ = f * ((LocalFieldData.ofInstances E).multiplicativeConductor η + d)

/-- The exact rank-one instance of the cuspidal sigma-lift conductor formula. -/
def CuspidalSigmaLiftConductorRankOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear 1 F) V)
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
      (haveI := LocalFieldTopology.generalLinear_t2Space F 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F 1
       haveI := LocalFieldTopology.generalLinear_t2Space E 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E 1
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ f d : ℕ, IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      ∑ κ ∈ X, Conductor.firstFixedLevel (twist (κ.comp GeneralLinear.determinant) π) =
        (f : WithTop ℕ) * ((s : WithTop ℕ) * Conductor.firstFixedLevel P₁ +
          ((1 : ℕ) : WithTop ℕ) * (d : WithTop ℕ))

/-- The pointwise character identity and the cyclic norm conductor formula give
rank one of the cuspidal sigma-lift conductor statement. -/
def CuspidalSigmaLiftConductorRankOneReductionStatement : Prop :=
  SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
    CyclicNormPullbackConductorStatement.{u, v} →
    CuspidalSigmaLiftConductorRankOneStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorRankOneReduction :
    CuspidalSigmaLiftConductorRankOneReductionStatement.{u, v, uV, uW} := by
  intro hidentity harith F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc V _ _ π hπ hπsuper hπirr
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
  let := LocalFieldTopology.generalLinear_t2Space F 1
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F 1
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F 1
  let := LocalFieldTopology.generalLinear_t2Space E 1
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E 1
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E 1
  have hshint := (hidentity F E σ l 1 hcyc π hπ P hP hπirr hPirr A c).mp hlift
  obtain ⟨χ, ⟨eπ⟩⟩ := GodementJacquet.exists_tateCharacterModel π hπ hπirr
  obtain ⟨η, ⟨eP⟩⟩ := GodementJacquet.exists_tateCharacterModel P hP hPirr
  have hnorm := IsShintaniLift.rankOne_normPullback hcyc hshint eπ eP
  obtain ⟨a, ha, hsum⟩ := harith F E σ l hcyc χ η hnorm f d hf hd X hX
  have hP₁level := Conductor.firstFixedLevel_eq_multiplicativeConductor η (eP₁.symm.trans eP)
  have htwist (κ : Fˣ →* ℂˣ) (hκ : κ ∈ X) :
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
