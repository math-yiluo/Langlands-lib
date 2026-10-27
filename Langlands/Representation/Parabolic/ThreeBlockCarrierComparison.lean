import Langlands.Representation.Induction.HeterogeneousConstruction

/-! Concrete carrier comparisons for the two literal three-block bracketings. -/

noncomputable section

namespace Representation.Equiv

universe uG uH uV uW uV' uW'

/-- Transport an equivalence through two carrier comparisons and group precomposition. -/
def ofPrecompComparison
    {G : Type uG} [Group G] {H : Type uH} [Group H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
    {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {ρ' : Representation ℂ H V'} {τ' : Representation ℂ H W'}
    (f : H →* G) (eL : ρ.Equiv τ) (eR : ρ'.Equiv τ')
    (e : Representation.Equiv (τ.comp f) τ') :
    Representation.Equiv (ρ.comp f) ρ' :=
  (eL.precomp f).trans (e.trans eR.symm)

end Representation.Equiv

namespace Langlands.PadicField

open GeneralLinear Shahidi

universe uF uV₀ uV₁ uV₂ uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {C A B : ℕ} (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)
variable {V₀ : Type uV₀} [AddCommGroup V₀] [Module ℂ V₀]
variable {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
variable {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
variable {W₀ W₁ W₂ : Type (max uF uW)}
  [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁]
  [AddCommGroup W₂] [Module ℂ W₂]
variable {ρ₀ : Representation ℂ (GeneralLinear C F.Carrier) V₀}
  {ρ₁ : Representation ℂ (GeneralLinear A F.Carrier) V₁}
  {ρ₂ : Representation ℂ (GeneralLinear B F.Carrier) V₂}
variable {τ₀ : Representation ℂ (GeneralLinear C F.Carrier) W₀}
  {τ₁ : Representation ℂ (GeneralLinear A F.Carrier) W₁}
  {τ₂ : Representation ℂ (GeneralLinear B F.Carrier) W₂}
variable (e₀ : ρ₀.Equiv τ₀) (e₁ : ρ₁.Equiv τ₁) (e₂ : ρ₂.Equiv τ₂)

/-- Compare the literal left bracketing, with its four ULifts, to the left
bracketing on three common-universe carriers. -/
def heterogeneousLeftCommonEquiv :
    letI := F.canonicalTopologicalData.topology
    let τ₁₂ := F.canonicalNormalizedProductInduced
      (twoBlocks A B hA hB) (pairFamily τ₁ τ₂)
    let commonLeft := F.canonicalNormalizedProductInduced
      (twoBlocks C (A + B) hC (Nat.add_pos_left hA B)) (pairFamily τ₀ τ₁₂)
    Representation.Equiv
      (F.heterogeneousPair hC (Nat.add_pos_left hA B) ρ₀
        (F.heterogeneousPair hA hB ρ₁ ρ₂)) commonLeft :=
  F.heterogeneousPairToPairEquiv hC (Nat.add_pos_left hA B) e₀
    (F.heterogeneousPairToPairEquiv hA hB e₁ e₂)

/-- Compare the literal right bracketing, with its four ULifts, to the right
bracketing on the same common-universe carriers. -/
def heterogeneousRightCommonEquiv :
    letI := F.canonicalTopologicalData.topology
    let τ₀₁ := F.canonicalNormalizedProductInduced
      (twoBlocks C A hC hA) (pairFamily τ₀ τ₁)
    let commonRight := F.canonicalNormalizedProductInduced
      (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB) (pairFamily τ₀₁ τ₂)
    Representation.Equiv
      (F.heterogeneousPair (Nat.add_pos_left hC A) hB
        (F.heterogeneousPair hC hA ρ₀ ρ₁) ρ₂) commonRight :=
  F.heterogeneousPairToPairEquiv (Nat.add_pos_left hC A) hB
    (F.heterogeneousPairToPairEquiv hC hA e₀ e₁) e₂

/-- An actual common-universe associativity equivalence yields the exact
heterogeneous one, retaining all eight ULifts and the fixed ambient rank cast. -/
def heterogeneousAssociativityEquiv :=
  letI := F.canonicalTopologicalData.topology
  let rankTransport := GeneralLinear.reindex (R := F.Carrier)
    (finCongr (Nat.add_assoc C A B))
  Representation.Equiv.ofPrecompComparison rankTransport.toMonoidHom
    (F.heterogeneousLeftCommonEquiv hC hA hB e₀ e₁ e₂)
    (F.heterogeneousRightCommonEquiv hC hA hB e₀ e₁ e₂)

end Langlands.PadicField
