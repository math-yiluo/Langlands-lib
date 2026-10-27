import Langlands.Representation.Induction.HeterogeneousPairs

/-! The literal heterogeneous pair and its comparison with a common-universe pair. -/

noncomputable section

namespace Langlands.PadicField

open GeneralLinear Shahidi

universe uF uV₀ uV₁ uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
variable {V₀ : Type uV₀} [AddCommGroup V₀] [Module ℂ V₀]
variable {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]

/-- Normalized upper pair induction with the exact two literal carrier lifts.
Its carrier lives in `max uF uV₀ uV₁`. -/
def heterogeneousPair
    (ρ₀ : Representation ℂ (GeneralLinear a F.Carrier) V₀)
    (ρ₁ : Representation ℂ (GeneralLinear b F.Carrier) V₁) :=
  let ρ₀L : Representation ℂ (GeneralLinear a F.Carrier) (ULift.{uV₁} V₀) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ₀
  let ρ₁L : Representation ℂ (GeneralLinear b F.Carrier) (ULift.{uV₀} V₁) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ₁
  F.canonicalNormalizedProductInduced (twoBlocks a b ha hb) (pairFamily ρ₀L ρ₁L)

variable {W₀ W₁ : Type uW} [AddCommGroup W₀] [Module ℂ W₀]
  [AddCommGroup W₁] [Module ℂ W₁]
variable {ρ₀ : Representation ℂ (GeneralLinear a F.Carrier) V₀}
  {ρ₁ : Representation ℂ (GeneralLinear b F.Carrier) V₁}
variable {τ₀ : Representation ℂ (GeneralLinear a F.Carrier) W₀}
  {τ₁ : Representation ℂ (GeneralLinear b F.Carrier) W₁}

/-- Factor equivalences compare the literal heterogeneous pair with the actual
normalized pair on any two common-universe carriers. -/
def heterogeneousPairToPairEquiv (e₀ : ρ₀.Equiv τ₀) (e₁ : ρ₁.Equiv τ₁) :
    letI := F.canonicalTopologicalData.topology
    Representation.Equiv (F.heterogeneousPair ha hb ρ₀ ρ₁)
      (F.canonicalNormalizedProductInduced (twoBlocks a b ha hb) (pairFamily τ₀ τ₁)) :=
  F.canonicalTopologicalData.normalizedPairInducedEquiv ha hb
    ((literalULiftEquiv ρ₀).symm.trans e₀)
    ((literalULiftEquiv ρ₁).symm.trans e₁)

/-- The literal heterogeneous pair is smooth, as an actual normalized induction. -/
theorem isSmooth_heterogeneousPair
    (ρ₀ : Representation ℂ (GeneralLinear a F.Carrier) V₀)
    (ρ₁ : Representation ℂ (GeneralLinear b F.Carrier) V₁) :
    letI := F.canonicalTopologicalData.topology
    IsSmooth (F.heterogeneousPair ha hb ρ₀ ρ₁) :=
  F.canonicalTopologicalData.isSmooth_normalizedProductInduced _ _

end Langlands.PadicField
