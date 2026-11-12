import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Transfer away from a distinguished factor

Let `Φ : G ≃ₜ* L × H` and `Φ' : G' ≃ₜ* L' × H'` split two topological groups into a
distinguished factor and its complement, and let `θ : H ≃ₜ* H'` identify the complements.
Given a relation `R` between representations of `L` and of `L'`, two complex representations
`ρ` of `G` and `ρ'` of `G'` are related when they are external tensor products, through `Φ`
and `Φ'`, of a common complement constituent (transported by `θ`) and of distinguished
constituents related by `R`. See `AwayTransfer.md`.
-/

open scoped TensorProduct

namespace Langlands.JacquetLanglands

universe u uG uG' uL uL' uH uH'

variable {G : Type uG} {G' : Type uG'} {L : Type uL} {L' : Type uL'} {H : Type uH}
  {H' : Type uH'}
variable [Group G] [Group G'] [Group L] [Group L'] [Group H] [Group H']
variable [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace L] [TopologicalSpace L']
  [TopologicalSpace H] [TopologicalSpace H']

/-- The representation `(π ⊠ σ) ∘ Φ` of `G`, for a splitting `Φ : G ≃ₜ* L × H`: the external
tensor product of `π` and `σ` (built from the projections and `Representation.tprod`, as in the
Library's Flath statements) pulled back along `Φ`. -/
noncomputable def splitTensor (Φ : G ≃ₜ* L × H) {X Y : Type u} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ L X) (σ : Representation ℂ H Y) :
    Representation ℂ G (X ⊗[ℂ] Y) :=
  (Representation.tprod (π.comp (MonoidHom.fst L H)) (σ.comp (MonoidHom.snd L H))).comp
    Φ.toMulEquiv.toMonoidHom

theorem splitTensor_apply_tmul (Φ : G ≃ₜ* L × H) {X Y : Type u} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ L X) (σ : Representation ℂ H Y)
    (g : G) (x : X) (y : Y) :
    splitTensor Φ π σ g (x ⊗ₜ y) = π (Φ g).1 x ⊗ₜ σ (Φ g).2 y :=
  rfl

/-- `ρ` of `G` and `ρ'` of `G'` agree away from the distinguished factor and are related by `R`
there: for some representations `π` of `L`, `π'` of `L'` and `σ` of `H` on complex vector
spaces of the universe of `ρ` and `ρ'`, `R π π'` holds, `ρ ≅ (π ⊠ σ) ∘ Φ` and
`ρ' ≅ (π' ⊠ (σ ∘ θ⁻¹)) ∘ Φ'`. -/
def IsAwayTransfer (Φ : G ≃ₜ* L × H) (Φ' : G' ≃ₜ* L' × H') (θ : H ≃ₜ* H')
    (R : ∀ X X' : ModuleCat.{u} ℂ, Representation ℂ L X → Representation ℂ L' X' → Prop)
    {V V' : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') : Prop :=
  ∃ (X X' Y : ModuleCat.{u} ℂ) (π : Representation ℂ L X) (π' : Representation ℂ L' X')
    (σ : Representation ℂ H Y),
    R X X' π π' ∧ Nonempty (ρ.Equiv (splitTensor Φ π σ)) ∧
      Nonempty (ρ'.Equiv (splitTensor Φ' π' (σ.comp θ.symm.toMulEquiv.toMonoidHom)))

section API

variable {Φ : G ≃ₜ* L × H} {Φ' : G' ≃ₜ* L' × H'} {θ : H ≃ₜ* H'}
  {R : ∀ X X' : ModuleCat.{u} ℂ, Representation ℂ L X → Representation ℂ L' X' → Prop}

/-- Nonvacuity: whenever `R π π'` holds, the external tensor products `(π ⊠ σ) ∘ Φ` and
`(π' ⊠ (σ ∘ θ⁻¹)) ∘ Φ'` are related. -/
theorem isAwayTransfer_splitTensor {X X' Y : ModuleCat.{u} ℂ} (π : Representation ℂ L X)
    (π' : Representation ℂ L' X') (σ : Representation ℂ H Y) (h : R X X' π π') :
    IsAwayTransfer Φ Φ' θ R (splitTensor Φ π σ)
      (splitTensor Φ' π' (σ.comp θ.symm.toMulEquiv.toMonoidHom)) :=
  ⟨X, X', Y, π, π', σ, h, ⟨Representation.Equiv.refl _⟩, ⟨Representation.Equiv.refl _⟩⟩

variable {V₁ V₂ V' : Type u} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V'] [Module ℂ V']

/-- The relation depends only on the isomorphism class of the representation of `G`. -/
theorem IsAwayTransfer.of_equiv_left {ρ₁ : Representation ℂ G V₁}
    {ρ₂ : Representation ℂ G V₂} {ρ' : Representation ℂ G' V'} (e : ρ₁.Equiv ρ₂)
    (h : IsAwayTransfer Φ Φ' θ R ρ₂ ρ') : IsAwayTransfer Φ Φ' θ R ρ₁ ρ' := by
  obtain ⟨X, X', Y, π, π', σ, hR, ⟨f⟩, hf'⟩ := h
  exact ⟨X, X', Y, π, π', σ, hR, ⟨e.trans f⟩, hf'⟩

/-- The relation depends only on the isomorphism class of the representation of `G'`. -/
theorem IsAwayTransfer.of_equiv_right {ρ : Representation ℂ G V'}
    {ρ'₁ : Representation ℂ G' V₁} {ρ'₂ : Representation ℂ G' V₂} (e : ρ'₁.Equiv ρ'₂)
    (h : IsAwayTransfer Φ Φ' θ R ρ ρ'₂) : IsAwayTransfer Φ Φ' θ R ρ ρ'₁ := by
  obtain ⟨X, X', Y, π, π', σ, hR, hf, ⟨f'⟩⟩ := h
  exact ⟨X, X', Y, π, π', σ, hR, hf, ⟨e.trans f'⟩⟩

/-- The relation is monotone in the local relation `R`. -/
theorem IsAwayTransfer.mono
    {S : ∀ X X' : ModuleCat.{u} ℂ, Representation ℂ L X → Representation ℂ L' X' → Prop}
    (hRS : ∀ X X' π π', R X X' π π' → S X X' π π') {ρ : Representation ℂ G V₁}
    {ρ' : Representation ℂ G' V'} (h : IsAwayTransfer Φ Φ' θ R ρ ρ') :
    IsAwayTransfer Φ Φ' θ S ρ ρ' := by
  obtain ⟨X, X', Y, π, π', σ, hR, hf, hf'⟩ := h
  exact ⟨X, X', Y, π, π', σ, hRS X X' π π' hR, hf, hf'⟩

end API

end Langlands.JacquetLanglands
