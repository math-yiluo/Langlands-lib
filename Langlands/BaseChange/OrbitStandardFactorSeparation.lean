import Langlands.AllField.Representation.RankinSelberg.SeparatedStandardFactorProduct
import Langlands.AllField.Representation.RankinSelberg.StandardInductionDualPolynomial
import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction
import Langlands.BaseChange.SigmaOrbitBlockFactors
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.LocalField.SuppliedPadicExtension
import Langlands.Representation.RankinSelberg.LanglandsFactors

/-! # Separated standard factors of an actual supercuspidal orbit product -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v uF uW

namespace Langlands.BaseChange

open CharZeroLocalField GeneralLinear HarmonicAnalysis MeasureTheory Whittaker
open RankinSelberg (IsOfWhittakerType IsPairEpsilonFactor LeftUnipotentQuotient
  rankOneCharacter rankCastRepresentation isOfWhittakerType_standard_iff_inverse)
open AllField.RankinSelberg

/-- Actual standard certificates with disjoint forward and reflected dual roots,
at any nontrivial additive character and its self-dual measure. -/
def HasSeparatedLocalStandardFactors (E : Type v) [Field E] [TopologicalSpace E] [ValuativeRel E]
    [IsNonarchimedeanLocalField E] {r : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear (r + 1) E) W) : Prop :=
  let one := rankOneCharacter (1 : Eˣ →* ℂˣ)
  ∀ (ψ : UnitaryAdditiveCharacter E)
    (ν : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E) ψ),
    ∃ (e : ℂˣ × ℤ) (p pd : Polynomial ℂ),
      IsEpsilonFactorAgainstTrivialCharacter ψ ν.val ρ e ∧
      IsPadicPairLPolynomial E ψ ν.val ρ one p ∧
      IsPadicPairLPolynomial E (ψ.scale (-1)) ν.val
        (inverseTransposePullback ρ) (inverseTransposePullback one) pd ∧
      ∀ x : ℂ, x ≠ 0 → p.eval x = 0 →
        pd.eval (((LocalFieldData.ofInstances E).residueCardinality : ℂ)⁻¹ / x) ≠ 0

/-- Actual separated standard factors of a positive-rank supercuspidal orbit
product on a characteristic-zero local extension. -/
def OrbitStandardFactorSeparationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [TopologicalSpace E] [ValuativeRel E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [FiniteDimensional F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (s k₁ r : ℕ) (h : s * (k₁ + 1) = r + 1)
    (W₁ W : Type uW) [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W] [Module ℂ W]
    (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁)
    (P : Representation ℂ (GeneralLinear (r + 1) E) W),
    P₁.IsIrreducible → IsSupercuspidal P₁ →
    Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    HasSeparatedLocalStandardFactors E P

private theorem rankCast_eq_comp_reindex
    {E : Type v} [Field E] {a b : ℕ} (h : a = b)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear a E) W) :
    rankCastRepresentation h P =
      P.comp (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom := by
  subst b
  ext x
  simp only [rankCastRepresentation, GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_symm,
    MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulEquiv.refl_apply]

set_option maxHeartbeats 5300000 in
theorem orbitStandardFactorSeparation : OrbitStandardFactorSeparationStatement.{v, uF, uW} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ _ _ σ s k₁ r h W₁ W _ _ _ _ P₁ P hi hs ⟨f⟩ ψ ν
  let one := rankOneCharacter (1 : Eˣ →* ℂˣ)
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let K := padicField F
  let T := topologicalData F
  let D := PadicField.ofField (p := p) E
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : D.TopologicalData := LocalField.suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : Algebra F D.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) F D.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : TopologicalSpace D.Carrier := S.topology
  let : IsModuleTopology F D.Carrier := (inferInstance : IsModuleTopology F E)
  have hB := sigmaOrbitBlockFactors p F D S σ s k₁ ψ ν P₁ hi hs
  let blocks (i : Fin s) := P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom
  have ht (i : Fin s) : IsOfWhittakerType k₁ (standardCharacter ψ k₁) (blocks i) := (hB.1 i).2.2
  obtain ⟨pF, pD, hpF, hpD, hsep⟩ := hB.2
  have h1 : IsOfWhittakerType 0 (standardCharacter ψ 0) one := rankOneCharacter_isOfWhittakerType E ψ 1
  have h1' := (isOfWhittakerType_standard_iff_inverse ψ one).mp h1
  choose e he using fun i =>
    (padicPairGammaConstructionInput_of_whittakerType E ψ ν k₁ 0 W₁ ℂ (blocks i) one
      (Nat.zero_le k₁) (ht i) h1').2.2.1
  let T' := LocalFieldData.ofInstances E
  let B := BlockShape.uniform s (k₁ + 1) (Nat.succ_pos k₁)
  have hsum : ∑ _ : Fin s, (k₁ + 1) = r + 1 := by simpa using h
  obtain ⟨hε, hL⟩ := separatedStandardFactorProduct E ψ ν (fun _ : Fin s => k₁) hsum blocks
    ht e pF pD he hpF hpD hsep
  have hD := standardInductionDualPolynomial E ψ ν r s (fun _ : Fin s => k₁) hsum
    (fun _ => W₁) blocks ht e pF pD he hpF hpD hε hL
  rw [← rankCast_eq_comp_reindex] at f
  let g := normalizedProductRankCastEquiv T' B h blocks
  let fg := f.trans g
  let π := T'.normalizedProductInduced (RankinSelberg.succBlockShape (fun _ : Fin s => k₁) hsum) blocks
  let fd : (inverseTransposePullback P).Equiv (inverseTransposePullback π) :=
    Representation.Equiv.mk fg.toLinearEquiv (fun g₀ => fg.isIntertwining' (inverseTranspose (r + 1) E g₀))
  refine ⟨(∏ i, (e i).1, ∑ i, (e i).2), ∏ i, pF i, ∏ i, pD i, ?_, ?_, ?_, ?_⟩
  · let := borel E
    let : BorelSpace E := ⟨rfl⟩
    let := borel (GeneralLinear 1 E)
    let : BorelSpace (GeneralLinear 1 E) := ⟨rfl⟩
    let := borel (upperUnipotent 1 E)
    let : BorelSpace (upperUnipotent 1 E) := ⟨rfl⟩
    let := borel (LeftUnipotentQuotient 0 E)
    exact (IsPairEpsilonFactor.congr_equiv fg (Representation.Equiv.refl one)).mpr hε
  · exact (IsPadicPairLPolynomial.congr_equiv fg (Representation.Equiv.refl one)).mpr hL
  · exact (IsPadicPairLPolynomial.congr_equiv fd (Representation.Equiv.refl (inverseTransposePullback one))).mpr hD
  · intro x hx hp
    have h := hsep x hx hp
    rw [AllField.LocalFactor.coe_residueReflection] at h
    exact h

end Langlands.BaseChange
