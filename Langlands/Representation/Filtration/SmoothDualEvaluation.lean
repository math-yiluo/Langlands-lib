import Langlands.Representation.Filtration.InvariantBilinear
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Twist.Definitions

/-! # Covariant evaluation against the ambient smooth dual -/

noncomputable section

namespace Langlands.InvariantBilinear

universe uK uG uH uV uW uX

section Algebra

variable {k : Type uK} [Field k]
variable {G : Type uG} [Monoid G] {H : Type uH} [Monoid H]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X]

/-- Pull back the two actions and their covariance along a group homomorphism,
keeping both carriers and the underlying bilinear map. -/
def comapGroup (φ : H →* G) (ρ : Representation k G V)
    (σ : Representation k G W) (χ : G → k) :
    forms ρ σ χ →ₗ[k] forms (ρ.comp φ) (σ.comp φ) (χ ∘ φ) where
  toFun B := ⟨B.val, fun h v w => B.property (φ h) v w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem comapGroup_apply (φ : H →* G) (ρ : Representation k G V)
    (σ : Representation k G W) (χ : G → k) (B : forms ρ σ χ) (v : V) (w : W) :
    (comapGroup φ ρ σ χ B).val v w = B.val v w := rfl

theorem comapGroup_separatingLeft (φ : H →* G) (ρ : Representation k G V)
    (σ : Representation k G W) (χ : G → k) (B : forms ρ σ χ)
    (hB : B.val.SeparatingLeft) :
    (comapGroup φ ρ σ χ B).val.SeparatingLeft := hB

/-- Pullback along an injective intertwiner preserves separation on the left. -/
theorem comapLeft_separatingLeft {ρ : Representation k G V}
    {τ : Representation k G X} (σ : Representation k G W) (χ : G → k)
    (f : ρ.IntertwiningMap τ) (hf : Function.Injective f) (B : forms τ σ χ)
    (hB : B.val.SeparatingLeft) :
    (comapLeft σ χ f B).val.SeparatingLeft := by
  intro v hv
  apply hf
  rw [map_zero]
  exact hB (f v) hv

/-- On a nonzero source, an injective pullback of a separating form is nonzero. -/
theorem comapLeft_ne_zero_of_separatingLeft [Nontrivial V]
    {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k)
    (f : ρ.IntertwiningMap τ) (hf : Function.Injective f) (B : forms τ σ χ)
    (hB : B.val.SeparatingLeft) :
    comapLeft σ χ f B ≠ 0 := by
  intro h
  exact (comapLeft_separatingLeft σ χ f hf B hB).ne_zero
    (congrArg Subtype.val h)

end Algebra

section Evaluation

variable {k : Type uK} [Field k]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module k V]

/-- Evaluation with a character twist on the smooth-dual action has precisely
that character as its simultaneous covariance. -/
def smoothDualEvaluation (ρ : Representation k G V) (χ : G →* kˣ) :
    forms (W := SmoothDual ρ) ρ
      (twist (V := SmoothDual ρ) χ (smoothContragredient ρ)) (fun g => (χ g : k)) :=
  ⟨(smoothDualPairing ρ).flip, by
    intro g v ℓ
    change smoothDualPairing ρ ((χ g : k) • smoothContragredient ρ g ℓ) (ρ g v) =
      (χ g : k) * smoothDualPairing ρ ℓ v
    rw [map_smul, LinearMap.smul_apply, smoothDualPairing_invariant, smul_eq_mul]⟩

@[simp]
theorem smoothDualEvaluation_apply (ρ : Representation k G V) (χ : G →* kˣ)
    (v : V) (ℓ : SmoothDual ρ) :
    (smoothDualEvaluation ρ χ).val v ℓ = smoothDualPairing ρ ℓ v := rfl

end Evaluation

section Separation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Cofinal compact open subgroups make this evaluation form separating on the
left for every smooth complex representation, without admissibility. -/
theorem smoothDualEvaluation_separatingLeft
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (χ : G →* ℂˣ) :
    (smoothDualEvaluation ρ χ).val.SeparatingLeft := by
  intro v hv
  apply smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ
  rw [map_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro ℓ
  exact hv ℓ

end Separation

end Langlands.InvariantBilinear
