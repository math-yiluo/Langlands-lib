import Langlands.Representation.Jacquet.SmoothTwist
import Langlands.Representation.Jacquet.PositiveCharacter

/-!
# Normalized Jacquet actions from a supplied positive modulus

The input positive character must be identified with the intended modulus by
the geometric application. The action uses its canonical inverse half.
-/

namespace Langlands.Jacquet

open scoped NNReal

universe uG uV uW uX

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- Jacquet normalization by the inverse half of a supplied positive modulus. -/
noncomputable def normalizedActionOfModulus (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) :
    Representation ℂ M (Coinvariants ρ N) :=
  characterTwistedAction ρ N M hMN (inverseHalfCharacter δ)

theorem normalizedActionOfModulus_mk (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ)
    (m : M) (v : V) :
    normalizedActionOfModulus ρ N M hMN δ m (mk ρ N v) =
      (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ))⁻¹ • mk ρ N (ρ m v) := by
  simp [normalizedActionOfModulus]

/-- The normalized quotient map, with the same inverse half on its source. -/
noncomputable def normalizedQuotientMapOfModulus (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) :
    (twist (inverseHalfCharacter δ) (ρ.comp M.subtype)).IntertwiningMap
      (normalizedActionOfModulus ρ N M hMN δ) :=
  characterTwistedQuotientMap ρ N M hMN (inverseHalfCharacter δ)

@[simp]
theorem normalizedQuotientMapOfModulus_apply (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) (v : V) :
    normalizedQuotientMapOfModulus ρ N M hMN δ v = mk ρ N v := rfl

theorem normalizedQuotientMapOfModulus_surjective (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) :
    Function.Surjective (normalizedQuotientMapOfModulus ρ N M hMN δ) :=
  mk_surjective ρ N

/-- An ambient intertwiner on normalized quotients using a common modulus. -/
noncomputable def normalizedMapOfModulus
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ)
    (f : ρ.IntertwiningMap σ) :
    (normalizedActionOfModulus ρ N M hMN δ).IntertwiningMap
      (normalizedActionOfModulus σ N M hMN δ) :=
  characterTwistedMap N M hMN (inverseHalfCharacter δ) f

@[simp]
theorem normalizedMapOfModulus_mk
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ)
    (f : ρ.IntertwiningMap σ) (v : V) :
    normalizedMapOfModulus N M hMN δ f (mk ρ N v) = mk σ N (f v) := rfl

theorem normalizedMapOfModulus_comp_quotientMap
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ)
    (f : ρ.IntertwiningMap σ) :
    (normalizedMapOfModulus N M hMN δ f).comp
        (normalizedQuotientMapOfModulus ρ N M hMN δ) =
      (normalizedQuotientMapOfModulus σ N M hMN δ).comp
        (twistIntertwining (inverseHalfCharacter δ) (restrictMap f M)) :=
  characterTwistedMap_comp_quotientMap N M hMN (inverseHalfCharacter δ) f

@[simp]
theorem normalizedMapOfModulus_id (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) :
    normalizedMapOfModulus N M hMN δ (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (normalizedActionOfModulus ρ N M hMN δ) :=
  characterTwistedMap_id ρ N M hMN (inverseHalfCharacter δ)

@[simp]
theorem normalizedMapOfModulus_comp
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    normalizedMapOfModulus N M hMN δ (g.comp f) =
      (normalizedMapOfModulus N M hMN δ g).comp (normalizedMapOfModulus N M hMN δ f) :=
  characterTwistedMap_comp N M hMN (inverseHalfCharacter δ) f g

/-- An open-kernel positive modulus gives a smooth normalized Jacquet action. -/
theorem isSmooth_normalizedActionOfModulus [TopologicalSpace G]
    (ρ : Representation ℂ G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set M)) (hρ : IsSmooth ρ) :
    IsSmooth (normalizedActionOfModulus ρ N M hMN δ) :=
  isSmooth_characterTwistedAction ρ N M hMN (inverseHalfCharacter δ)
    (isOpen_ker_inverseHalfCharacter δ hδ) hρ

end Langlands.Jacquet
