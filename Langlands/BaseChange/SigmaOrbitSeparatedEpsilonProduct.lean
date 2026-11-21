import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.AllField.Representation.RankinSelberg.SeparatedStandardFactorProduct
import Langlands.Representation.RankinSelberg.LanglandsFactors

noncomputable section

namespace Langlands.BaseChange

open _root_.Polynomial HarmonicAnalysis Whittaker GeneralLinear
open RankinSelberg (IsOfWhittakerType rankOneCharacter rankCastRepresentation
  IsPairEpsilonFactor epsilonMonomial epsilonFactorProduct epsilonMonomial_factorProduct)
open AllField.RankinSelberg (IsPadicPairEpsilonFactor IsPadicPairLPolynomial
  separatedStandardFactorProduct normalizedProductRankCastEquiv)

universe u v uW uP

/-- The standard epsilon product on the actual reindexed sigma-orbit, given
block certificates and separation of the original and reflected dual roots. -/
def SigmaOrbitSeparatedEpsilonProductStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [Field E] [TopologicalSpace E] [ValuativeRel E]
    [IsNonarchimedeanLocalField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (s k₁ t : ℕ) (h : s * (k₁ + 1) = t + 1)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W)
    {V : Type uP} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (t + 1) E) V),
    Nonempty (ρ.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (ψ : UnitaryAdditiveCharacter E)
      (ν : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E) ψ)
      (e : Fin s → ℂˣ × ℤ) (P PD : Fin s → ℂ[X]),
    let blocks := fun i : Fin s => P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom
    (∀ i, IsOfWhittakerType k₁ (standardCharacter ψ k₁) (blocks i)) →
    (∀ i, IsPadicPairEpsilonFactor E ψ ν.val (blocks i) (rankOneCharacter 1) (e i)) →
    (∀ i, IsPadicPairLPolynomial E ψ ν.val (blocks i) (rankOneCharacter 1) (P i)) →
    (∀ i, IsPadicPairLPolynomial E (ψ.scale (-1)) ν.val
      (inverseTransposePullback (blocks i)) (inverseTransposePullback (rankOneCharacter 1)) (PD i)) →
    (∀ x : ℂ, x ≠ 0 → (∏ i, P i).eval x = 0 →
      (∏ i, PD i).eval ((AllField.LocalFactor.residueReflection E : ℂˣ) / x) ≠ 0) →
    IsPadicPairEpsilonFactor E ψ ν.val ρ (rankOneCharacter 1)
      (∏ i, (e i).1, ∑ i, (e i).2) ∧
    (∀ z : ℂ,
      ∏ i : Fin s, epsilonMonomial (LocalFieldData.ofInstances E).residueCardinality
          (e i).1 (e i).2 z =
        epsilonMonomial (LocalFieldData.ofInstances E).residueCardinality
          (∏ i, (e i).1) (∑ i, (e i).2) z)

private theorem rankCastRepresentation_eq_comp_reindex
    {E : Type v} [Field E] {a b : ℕ} (h : a = b)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear a E) W) :
    rankCastRepresentation h P =
      P.comp (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom := by
  subst b
  ext x
  simp only [rankCastRepresentation, GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_symm,
    MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulEquiv.refl_apply]

set_option maxHeartbeats 600000 in
/-- Exact orientation and rank transport of separated epsilon multiplicativity. -/
theorem sigmaOrbitSeparatedEpsilonProduct : SigmaOrbitSeparatedEpsilonProductStatement.{u,v,uW,uP} := by
  intro F _ E _ _ _ _ _ σ s k₁ t h W _ _ P₁ V _ _ ρ hρ ψ ν e P PD blocks htype he hP hPD hsep
  let T := LocalFieldData.ofInstances E
  let C := BlockShape.uniform s (k₁ + 1) (Nat.succ_pos k₁)
  have hsum : ∑ _ : Fin s, (k₁ + 1) = t + 1 := by simpa using h
  have hm := (separatedStandardFactorProduct E ψ ν (fun _ : Fin s => k₁) hsum blocks
    htype e P PD he hP hPD hsep).1
  obtain ⟨f⟩ := hρ
  rw [← rankCastRepresentation_eq_comp_reindex] at f
  let g := normalizedProductRankCastEquiv T C h blocks
  have fg := f.trans g
  let one := rankOneCharacter (F := E) 1
  refine ⟨?_, fun z => ?_⟩
  · let := borel E
    let : BorelSpace E := ⟨rfl⟩
    let := borel (GeneralLinear 1 E)
    let : BorelSpace (GeneralLinear 1 E) := ⟨rfl⟩
    let := borel (upperUnipotent 1 E)
    let : BorelSpace (upperUnipotent 1 E) := ⟨rfl⟩
    let := borel (RankinSelberg.LeftUnipotentQuotient 0 E)
    change IsPairEpsilonFactor T.residueCardinality ψ
      (AllField.RankinSelberg.normalizedAbsoluteValue T) ν.val ρ one _
    exact (IsPairEpsilonFactor.congr_equiv fg (Representation.Equiv.refl one)).mpr hm
  · simpa [epsilonFactorProduct] using
      (epsilonMonomial_factorProduct (fun (i : Fin s) (_ : Unit) => e i)
        T.residueCardinality_gt_one z).symm

end Langlands.BaseChange
