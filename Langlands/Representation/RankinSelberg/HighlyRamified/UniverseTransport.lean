import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.Whittaker.Transport

/-!
# Moving gamma stability to smaller universes

`PairStability` and `UniformPairStability` quantify over representation spaces in fixed
universes. This module shows that both pass from larger universes to smaller ones: a
representation on `V` is equivalent to its copy on `ULift V`, and genericity, central
characters, level vectors and gamma factors are invariant under equivalence.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW uV' uW' uG uX uY

variable {p : ℕ} [Fact p.Prime]

section Lift

variable {G : Type uG} [Monoid G] {V : Type uX} [AddCommGroup V] [Module ℂ V]

/-- The representation `ρ` moved to `ULift V` along `ULift.moduleEquiv`. -/
def uliftRepresentation (ρ : Representation ℂ G V) : Representation ℂ G (ULift.{uY} V) where
  toFun g := (ULift.moduleEquiv (R := ℂ) (M := V)).symm.toLinearMap ∘ₗ ρ g ∘ₗ
    (ULift.moduleEquiv (R := ℂ) (M := V)).toLinearMap
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Module.End.mul_apply]

/-- `ρ` is equivalent to its copy on `ULift V`. -/
def uliftRepresentationEquiv (ρ : Representation ℂ G V) :
    ρ.Equiv (uliftRepresentation.{uG, uX, uY} ρ) :=
  Representation.Equiv.mk (ULift.moduleEquiv (R := ℂ) (M := V)).symm fun _ => rfl

end Lift

section Invariance

variable {G : Type uG} [Group G] {V : Type uX} [AddCommGroup V] [Module ℂ V]
  {W : Type uY} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G W}

/-- A scalar character passes along an equivalence. -/
theorem hasScalarCharacter_of_equiv (e : ρ.Equiv τ) {C : Type*} [Group C] {z : C →* G}
    {ω : C →* ℂˣ} (h : Classification.HasScalarCharacter ρ z ω) :
    Classification.HasScalarCharacter τ z ω := by
  intro c w
  have h1 := Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap (z c)
    (e.symm w)
  rw [h c] at h1
  have h2 : e (e.symm w) = w := e.toLinearEquiv.apply_symm_apply w
  change e.toLinearEquiv ((ω c : ℂ) • e.symm w) = τ (z c) (e.toLinearEquiv (e.symm w)) at h1
  rw [map_smul] at h1
  change (ω c : ℂ) • e (e.symm w) = τ (z c) (e (e.symm w)) at h1
  rw [h2] at h1
  exact h1.symm

/-- A nonzero fixed vector passes along an equivalence. -/
theorem fixedVectors_ne_bot_of_equiv (e : ρ.Equiv τ) {K : Subgroup G}
    (h : Langlands.fixedVectors ρ K ≠ ⊥) : Langlands.fixedVectors τ K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Submodule.ne_bot_iff]
  refine ⟨e v, ?_, ?_⟩
  · simp only [Langlands.fixedVectors, Representation.mem_invariants] at hv ⊢
    intro g
    have h1 := Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap g v
    change e (ρ g v) = τ g (e v) at h1
    change τ g (e v) = e v
    rw [← h1]
    exact congrArg e (hv g)
  · intro h0
    exact hv0 (e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm))

end Invariance

/-- Two candidates with the same central character keep it after equivalences. -/
theorem sameGLCentralCharacter_of_equiv (F : PadicField.{uF} p) {r : ℕ}
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    {U₁ U₂ : Type uX} [AddCommGroup U₁] [Module ℂ U₁] [AddCommGroup U₂] [Module ℂ U₂]
    {π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {τ₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) U₁}
    {τ₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) U₂}
    (e₁ : π₁.Equiv τ₁) (e₂ : π₂.Equiv τ₂) (h : SameGLCentralCharacter F π₁ π₂) :
    SameGLCentralCharacter F τ₁ τ₂ := by
  obtain ⟨ω, h₁, h₂⟩ := h
  exact ⟨ω, hasScalarCharacter_of_equiv e₁ h₁, hasScalarCharacter_of_equiv e₂ h₂⟩

/-- A principal level vector passes along an equivalence. -/
theorem hasPrincipalLevelVector_of_equiv (F : PadicField.{uF} p) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {U : Type uX} [AddCommGroup U] [Module ℂ U]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) U}
    (e : π.Equiv τ) {m : ℕ} (h : HasPrincipalLevelVector F π m) :
    HasPrincipalLevelVector F τ m :=
  fixedVectors_ne_bot_of_equiv e h

/-- `PairStability` passes from the universes `(max uV uV', max uW uW')` to `(uV, uW)`:
apply it to the copies of the representations on `ULift` spaces. -/
theorem pairStability_of_ulift {r t : ℕ}
    (h : PairStability.{uF, max uV uV', max uW uW'} r t) :
    PairStability.{uF, uV, uW} r t := by
  intro p _ F ψ ν hψ V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hc
  let := F.canonicalTopologicalData.topology
  let e₁ := uliftRepresentationEquiv.{_, uV, uV'} π₁
  let e₂ := uliftRepresentationEquiv.{_, uV, uV'} π₂
  let e₃ := uliftRepresentationEquiv.{_, uW, uW'} σ
  obtain ⟨A, hA⟩ := h p F ψ ν hψ _ _ _ ((isGeneric_iff_of_equiv ψ r e₁).mp hπ₁)
    ((isGeneric_iff_of_equiv ψ r e₂).mp hπ₂) ((isGeneric_iff_of_equiv ψ t e₃).mp hσ)
    (sameGLCentralCharacter_of_equiv F e₁ e₂ hc)
  refine ⟨A, fun χ hχ G₁ G₂ hG₁ hG₂ => hA χ hχ G₁ G₂ ?_ ?_⟩
  · exact (IsPadicSymmetricGammaFactor.congr_equiv
      (Langlands.twistEquiv ((χ : F.Carrierˣ →* ℂˣ).comp determinant) e₁) e₃).mp hG₁
  · exact (IsPadicSymmetricGammaFactor.congr_equiv
      (Langlands.twistEquiv ((χ : F.Carrierˣ →* ℂˣ).comp determinant) e₂) e₃).mp hG₂

/-- `UniformPairStability` passes from the universes `(max uV uV', max uW uW')` to
`(uV, uW)`, with the same bound. -/
theorem uniformPairStability_of_ulift {r t : ℕ}
    (h : UniformPairStability.{uF, max uV uV', max uW uW'} r t) :
    UniformPairStability.{uF, uV, uW} r t := by
  intro p _ F ψ ν hψ m m'
  obtain ⟨A, hA⟩ := h p F ψ ν hψ m m'
  refine ⟨A, ?_⟩
  intro V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ h₁ h₂ h₃ hc χ hχ G₁ G₂ hG₁ hG₂
  let := F.canonicalTopologicalData.topology
  let e₁ := uliftRepresentationEquiv.{_, uV, uV'} π₁
  let e₂ := uliftRepresentationEquiv.{_, uV, uV'} π₂
  let e₃ := uliftRepresentationEquiv.{_, uW, uW'} σ
  exact hA _ _ _ ((isGeneric_iff_of_equiv ψ r e₁).mp hπ₁)
    ((isGeneric_iff_of_equiv ψ r e₂).mp hπ₂) ((isGeneric_iff_of_equiv ψ t e₃).mp hσ)
    (hasPrincipalLevelVector_of_equiv F e₁ h₁) (hasPrincipalLevelVector_of_equiv F e₂ h₂)
    (hasPrincipalLevelVector_of_equiv F e₃ h₃) (sameGLCentralCharacter_of_equiv F e₁ e₂ hc)
    χ hχ G₁ G₂
    ((IsPadicSymmetricGammaFactor.congr_equiv
      (Langlands.twistEquiv ((χ : F.Carrierˣ →* ℂˣ).comp determinant) e₁) e₃).mp hG₁)
    ((IsPadicSymmetricGammaFactor.congr_equiv
      (Langlands.twistEquiv ((χ : F.Carrierˣ →* ℂˣ).comp determinant) e₂) e₃).mp hG₂)

/-- The common-universe form used by the adjacent-rank induction: stability with both
spaces in `max uF uV uW` gives stability at `(uV, uW)`. -/
theorem pairStability_of_common {r t : ℕ}
    (h : PairStability.{uF, max uF uV uW, max uF uV uW} r t) :
    PairStability.{uF, uV, uW} r t :=
  pairStability_of_ulift.{uF, uV, uW, max uF uW, max uF uV} h

end Langlands.RankinSelberg.HighlyRamified
