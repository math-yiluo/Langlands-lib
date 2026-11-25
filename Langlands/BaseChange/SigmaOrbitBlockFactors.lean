import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.AllField.LocalFactor.ResidueReflection
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Langlands.Representation.Classification.SupercuspidalInverseTranspose
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.LocalFactor.Abelian.SpectralTransport
import Langlands.Representation.GodementJacquet.TateCharacterLFactor
import Langlands.Representation.GodementJacquet.TateCharacterReduction
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality

noncomputable section

namespace Langlands.BaseChange

open _root_.Polynomial HarmonicAnalysis GeneralLinear Whittaker
open RankinSelberg (IsOfWhittakerType rankOneCharacter
  isOfWhittakerType_firstDual supercuspidalUnequalRankLFactor)
open AllField.RankinSelberg (IsPadicPairLPolynomial)

universe u v uW

/-- Entrywise Galois pullback preserves the two actual predicates on a block. -/
theorem sigmaOrbitBlock_supercuspidal_irreducible
    {K : Type u} [Field K] [TopologicalSpace K] {E : Type v} [Field E] [TopologicalSpace E]
    [Algebra K E] [IsModuleTopology K E]
    (σ : E ≃ₐ[K] E) {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E) W)
    (hs : GeneralLinear.IsSupercuspidal P) (hi : P.IsIrreducible) :
    Representation.IsIrreducible (P.comp (entrywiseAut σ n).toMonoidHom) ∧
      GeneralLinear.IsSupercuspidal (P.comp (entrywiseAut σ n).toMonoidHom) := by
  have := IsModuleTopology.toContinuousAdd K E
  have hc : Continuous σ.toRingEquiv := IsModuleTopology.continuous_of_linearMap σ.toLinearMap
  have hcs : Continuous σ.toRingEquiv.symm :=
    IsModuleTopology.continuous_of_linearMap σ.symm.toLinearMap
  exact ⟨(isIrreducible_comp_continuousMulEquiv_iff P (fieldEquiv n σ.toRingEquiv hc hcs)).mpr hi,
    isSupercuspidal_comp_fieldEquiv n σ.toRingEquiv hc hcs P hs⟩

section SuppliedPadic

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{v} p)

/-- Whittaker type of an irreducible supercuspidal on the supplied p-adic realization. -/
theorem sigmaOrbitBlock_whittakerType (T : E.TopologicalData) :
    letI := T.topology
    ∀ {r : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ψ : UnitaryAdditiveCharacter E.Carrier)
      (P : Representation ℂ (GeneralLinear (r + 1) E.Carrier) W),
      P.IsIrreducible → GeneralLinear.IsSupercuspidal P →
        IsOfWhittakerType r (standardCharacter ψ r) P := by
  rw [T.eq_canonicalTopologicalData]
  intro r W _ _ ψ P hi hs
  let := E.canonicalTopologicalData.topology
  exact RankinSelberg.SupercuspidalLFactorCharacterization.isOfWhittakerType_of_isSupercuspidal
    E ψ r (SmoothRep.of P hs.1.1) hi hs

set_option maxHeartbeats 700000 in
/-- For supercuspidal blocks of rank greater than one the original and dual
standard L-polynomials are both one, with the same additive measure. -/
theorem sigmaOrbitBlock_unequalRankLPolynomials (T : E.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {r : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ψ : UnitaryAdditiveCharacter E.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
      (P : Representation ℂ (GeneralLinear (r + 1) E.Carrier) W),
      0 < r → P.IsIrreducible → GeneralLinear.IsSupercuspidal P →
        IsPadicPairLPolynomial E.Carrier ψ ν.val P (rankOneCharacter 1) 1 ∧
        IsPadicPairLPolynomial E.Carrier (ψ.scale (-1)) ν.val
          (inverseTransposePullback P) (inverseTransposePullback (rankOneCharacter 1)) 1 := by
  rw [T.eq_canonicalTopologicalData]
  intro r W _ _ ψ ν P hr hi hs
  let := E.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  let one := rankOneCharacter (F := E.Carrier) 1
  have hone : IsOfWhittakerType 0 (standardCharacter ψ 0) one :=
    RankinSelberg.rankOneCharacter_isOfWhittakerType p E ψ 1
  have hd := isOfWhittakerType_firstDual ψ one hone
  have hdi : (inverseTransposePullback P).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff P (inverseTransposeContinuous (r + 1) E.Carrier)).mpr hi
  have hds : GeneralLinear.IsSupercuspidal (inverseTransposePullback P) :=
    isSupercuspidal_comp_inverseTranspose P hs
  let νd := RankinSelberg.DominantRankTransport.negatedSelfDualHaar E ψ ν
  exact ⟨supercuspidalUnequalRankLFactor p E ψ ν r 0 P one hi hs hone hr,
    supercuspidalUnequalRankLFactor p E (ψ.scale (-1)) νd r 0
      (inverseTransposePullback P) (inverseTransposePullback one) hdi hds hd hr⟩

end SuppliedPadic

section RankOne

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{v} p)

private local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology
private local instance : ValuativeRel E.Carrier := E.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField E.Carrier := E.canonicalTopologicalData.localField

open PadicField.ConductorTransport (quasicharacter quasicharacter_apply unitsEquiv
  unitsEquiv_symm_apply)
open PadicField.AbelianTransport (lPolynomial_eq)
open LocalFactor.PadicAbelian (lPolynomial uniformizerUnit)

private theorem inverseTransposePullback_rankOneCharacter
    (χ : Quasicharacter E.Carrier) :
    inverseTransposePullback (rankOneCharacter (χ : E.Carrierˣ →* ℂˣ)) =
      rankOneCharacter ((χ⁻¹ : Quasicharacter E.Carrier) : E.Carrierˣ →* ℂˣ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (χ (determinant (inverseTranspose 1 E.Carrier g)) : ℂ) * v =
    ((χ⁻¹ : Quasicharacter E.Carrier) (determinant g) : ℂ) * v
  rw [RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose, map_inv]
  rfl

private def blockRankOneEquiv
    {K : Type u} [Field K] [Algebra (Padic p) K] [Algebra K E.Carrier]
    [IsScalarTower (Padic p) K E.Carrier] (σ : E.Carrier ≃ₐ[K] E.Carrier)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {P : Representation ℂ (GeneralLinear 1 E.Carrier) W} {χ : Quasicharacter E.Carrier}
    (f : P.Equiv (rankOneCharacter (χ : E.Carrierˣ →* ℂˣ))) :
    Representation.Equiv (P.comp (entrywiseAut σ 1).toMonoidHom)
      (rankOneCharacter (quasicharacter E E (σ.restrictScalars (Padic p)).symm χ :
        E.Carrierˣ →* ℂˣ)) := by
  have hdet (g : GeneralLinear 1 E.Carrier) : determinant (entrywiseAut σ 1 g) =
      (unitsEquiv E E (σ.restrictScalars (Padic p)).symm).symm (determinant g) := by
    apply Units.ext
    rw [unitsEquiv_symm_apply]
    change (σ.toRingHom.mapMatrix g.val).det = σ.toRingHom g.val.det
    rw [RingHom.map_det]
  refine Representation.Equiv.mk f.toLinearEquiv (fun g => ?_)
  ext x
  have hx := LinearMap.congr_fun (f.isIntertwining' (entrywiseAut σ 1 g)) x
  change f (P (entrywiseAut σ 1 g) x) =
    (χ (determinant (entrywiseAut σ 1 g)) : ℂ) * f x at hx
  change f (P (entrywiseAut σ 1 g) x) =
    (quasicharacter E E (σ.restrictScalars (Padic p)).symm χ (determinant g) : ℂ) * f x
  simpa only [quasicharacter_apply, ← hdet] using hx

private theorem quasicharacter_mul_one (χ : Quasicharacter E.Carrier) :
    χ * (1 : Quasicharacter E.Carrier) = χ := by
  apply ContinuousMonoidHom.ext
  intro z
  change χ z * 1 = χ z
  exact mul_one _

private theorem lPolynomial_pair_separated
    (s : ℕ) (χ : Quasicharacter E.Carrier) :
    ∀ x : ℂ, x ≠ 0 → (∏ _ : Fin s, lPolynomial E.canonicalTopologicalData χ).eval x = 0 →
      (∏ _ : Fin s, lPolynomial E.canonicalTopologicalData χ⁻¹).eval
        ((AllField.LocalFactor.residueReflection E.Carrier : ℂˣ) / x) ≠ 0 := by
  classical
  let T := E.canonicalTopologicalData
  let δ := (AllField.LocalFactor.residueReflection E.Carrier : ℂˣ)
  have hδ : (δ : ℂ) ≠ 1 := by
    rw [show (δ : ℂ) = (T.residueCardinality : ℂ)⁻¹ from
      AllField.LocalFactor.coe_residueReflection E.Carrier]
    intro h
    exact (Nat.ne_of_gt T.residueCardinality_gt_one) (by exact_mod_cast inv_eq_one.mp h)
  intro x hx h
  by_cases hc : T.multiplicativeConductor χ = 0
  · have hc' : T.multiplicativeConductor χ⁻¹ = 0 := by
      apply (T.multiplicativeConductor_eq_zero_iff χ⁻¹).mpr
      intro b hb
      have hχ := (T.multiplicativeConductor_eq_zero_iff χ).mp hc b hb
      change (χ b)⁻¹ = 1
      rw [hχ, inv_one]
    let a : ℂ := χ (uniformizerUnit T)
    have ha : a * x = 1 := by
      have hzero : (1 - a * x) ^ s = 0 := by
        simpa [lPolynomial, hc, a, T] using h
      by_contra hne
      exact pow_ne_zero s (sub_ne_zero.mpr (Ne.symm hne)) hzero
    have hdual : 1 - a⁻¹ * ((δ : ℂ) / x) ≠ 0 := by
      have hmul : a⁻¹ * ((δ : ℂ) / x) = (δ : ℂ) * (a * x)⁻¹ := by
        rw [mul_inv_rev, div_eq_mul_inv]
        ring
      rw [hmul, ha, inv_one, mul_one]
      exact sub_ne_zero.mpr (Ne.symm hδ)
    have hcoeff : ((χ⁻¹ : Quasicharacter E.Carrier) (uniformizerUnit T) : ℂ) = a⁻¹ := by
      change (((χ (uniformizerUnit T))⁻¹ : ℂˣ) : ℂ) = (χ (uniformizerUnit T) : ℂ)⁻¹
      simp
    simpa [lPolynomial, hc', hcoeff, a, T, δ] using pow_ne_zero s hdual
  · simp [lPolynomial, hc, T] at h

set_option maxHeartbeats 800000 in
private theorem canonical_rankOneOrbitLPolynomials
    {K : Type u} [Field K] [Algebra (Padic p) K] [Algebra K E.Carrier]
    [IsScalarTower (Padic p) K E.Carrier] (σ : E.Carrier ≃ₐ[K] E.Carrier) (s : ℕ)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ψ : UnitaryAdditiveCharacter E.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar E.canonicalTopologicalData ψ)
    (P₁ : Representation ℂ (GeneralLinear 1 E.Carrier) W)
    (hi : P₁.IsIrreducible) (hs : GeneralLinear.IsSupercuspidal P₁) :
    let B := fun i : Fin s => P₁.comp (entrywiseAut (σ ^ (i : ℕ)) 1).toMonoidHom
    ∃ P PD : ℂ[X],
      (∀ i, IsPadicPairLPolynomial E.Carrier ψ ν.val (B i) (rankOneCharacter 1) P) ∧
      (∀ i, IsPadicPairLPolynomial E.Carrier (ψ.scale (-1)) ν.val
        (inverseTransposePullback (B i)) (inverseTransposePullback (rankOneCharacter 1)) PD) ∧
      (∀ x : ℂ, x ≠ 0 → (∏ _ : Fin s, P).eval x = 0 →
        (∏ _ : Fin s, PD).eval ((AllField.LocalFactor.residueReflection E.Carrier : ℂˣ) / x) ≠ 0) := by
  intro B
  let T := E.canonicalTopologicalData
  let := borel E.Carrier
  obtain ⟨χ, ⟨f⟩⟩ := GodementJacquet.exists_tateCharacterModel P₁ hs.1 hi
  let P := lPolynomial T χ
  let PD := lPolynomial T χ⁻¹
  let one := rankOneCharacter (F := E.Carrier) 1
  have hone : inverseTransposePullback one = one := by
    ext g
    simp [one, inverseTransposePullback, characterRepresentation, twist]
  refine ⟨P, PD, ?_, ?_, lPolynomial_pair_separated E s χ⟩
  · intro i
    let σi := σ ^ (i : ℕ)
    let χi := quasicharacter E E (σi.restrictScalars (Padic p)).symm χ
    let fi := blockRankOneEquiv E σi f
    have hpoly := GodementJacquet.Padic.rankOneCharacters_isPadicPairLPolynomial E χi ψ 1 ν.val
    have h := (RankinSelberg.IsPadicPairLPolynomial.congr_equiv fi.symm
      (Representation.Equiv.refl one)).mp hpoly
    rw [quasicharacter_mul_one, show χi = quasicharacter E E
      (σi.restrictScalars (Padic p)).symm χ from rfl, lPolynomial_eq] at h
    exact h
  · intro i
    let σi := σ ^ (i : ℕ)
    let χi := quasicharacter E E (σi.restrictScalars (Padic p)).symm χ
    let fi := blockRankOneEquiv E σi f
    have hcinv : χi⁻¹ = quasicharacter E E (σi.restrictScalars (Padic p)).symm χ⁻¹ := by
      ext x
      rfl
    let fd : Representation.Equiv (inverseTransposePullback (B i))
        (inverseTransposePullback (rankOneCharacter (χi : E.Carrierˣ →* ℂˣ))) :=
      Representation.Equiv.mk fi.toLinearEquiv (fun g => by
        ext x
        exact LinearMap.congr_fun (fi.isIntertwining' (inverseTranspose 1 E.Carrier g)) x)
    rw [hone]
    rw [inverseTransposePullback_rankOneCharacter] at fd
    have hpoly := GodementJacquet.Padic.rankOneCharacters_isPadicPairLPolynomial E
      χi⁻¹ (ψ.scale (-1)) 1 ν.val
    have h := (RankinSelberg.IsPadicPairLPolynomial.congr_equiv fd.symm
      (Representation.Equiv.refl one)).mp hpoly
    rw [quasicharacter_mul_one, hcinv, lPolynomial_eq] at h
    exact h

end RankOne

/-- The full Whittaker type and separated original and dual L-polynomials
of the actual supercuspidal orbit blocks over a supplied p-adic field. -/
def SigmaOrbitBlockFactorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [TopologicalSpace K] [Algebra (Padic p) K]
    (E : PadicField.{v} p) [Algebra K E.Carrier] [IsScalarTower (Padic p) K E.Carrier]
    (T : E.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [IsModuleTopology K E.Carrier] (σ : E.Carrier ≃ₐ[K] E.Carrier) (s r : ℕ)
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ψ : UnitaryAdditiveCharacter E.Carrier) (ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
      (P₁ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) W),
    P₁.IsIrreducible → GeneralLinear.IsSupercuspidal P₁ →
    let B := fun i : Fin s => P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (r + 1)).toMonoidHom
    (∀ i, Representation.IsIrreducible (B i) ∧ GeneralLinear.IsSupercuspidal (B i) ∧
      IsOfWhittakerType r (standardCharacter ψ r) (B i)) ∧
    ∃ P PD : Fin s → ℂ[X],
      (∀ i, IsPadicPairLPolynomial E.Carrier ψ ν.val (B i) (rankOneCharacter 1) (P i)) ∧
      (∀ i, IsPadicPairLPolynomial E.Carrier (ψ.scale (-1)) ν.val
        (inverseTransposePullback (B i)) (inverseTransposePullback (rankOneCharacter 1)) (PD i)) ∧
      (∀ x : ℂ, x ≠ 0 → (∏ i, P i).eval x = 0 →
        (∏ i, PD i).eval ((AllField.LocalFactor.residueReflection E.Carrier : ℂˣ) / x) ≠ 0)

set_option maxHeartbeats 600000 in
/-- These are actual certificates, not assumptions on their Euler polynomials. -/
theorem sigmaOrbitBlockFactors : SigmaOrbitBlockFactorsStatement.{u, v, uW} := by
  intro p _ K _ _ _ E _ _ T
  rw [T.eq_canonicalTopologicalData]
  intro _ σ s r W _ _ ψ ν P₁ hi hs B
  let T := E.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hb (i : Fin s) : Representation.IsIrreducible (B i) ∧ GeneralLinear.IsSupercuspidal (B i) :=
    sigmaOrbitBlock_supercuspidal_irreducible (σ ^ (i : ℕ)) P₁ hs hi
  refine ⟨fun i => ⟨(hb i).1, (hb i).2, sigmaOrbitBlock_whittakerType E T ψ _ (hb i).1 (hb i).2⟩, ?_⟩
  cases r with
  | zero =>
      obtain ⟨P, PD, hP, hPD, hsep⟩ := canonical_rankOneOrbitLPolynomials E σ s ψ ν P₁ hi hs
      exact ⟨fun _ => P, fun _ => PD, hP, hPD, hsep⟩
  | succ r =>
      have h (i : Fin s) := sigmaOrbitBlock_unequalRankLPolynomials E T ψ ν (B i)
        (Nat.succ_pos r) (hb i).1 (hb i).2
      exact ⟨fun _ => 1, fun _ => 1, fun i => (h i).1, fun i => (h i).2, by simp⟩

end Langlands.BaseChange
