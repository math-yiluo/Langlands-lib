import Langlands.Representation.Jacquet.CharacterTwistEquiv
import Langlands.Representation.Jacquet.Normalized

/-!
# Character-twisted and normalized Jacquet quotients under a trivial-radical twist

The equivalence of `Langlands.Representation.Jacquet.CharacterTwistEquiv` with a
common additional character, restated for the named character-twisted Jacquet
action and for the Jacquet action normalized by a supplied positive modulus.
The same literal character, respectively modulus, appears on both sides.
-/

namespace Langlands.Jacquet

open scoped NNReal

universe uR uG uV uW

section CharacterTwisted

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- The character-twisted Jacquet quotient of a twist by a character trivial on
`N` is the twist of the character-twisted Jacquet quotient. -/
noncomputable def characterTwistedActionTwistEquiv (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ)
    (hN : N ≤ χ.ker) (ψ : M →* Rˣ) :
    (characterTwistedAction (twist χ ρ) N M hMN ψ).Equiv
      (twist (χ.comp M.subtype) (characterTwistedAction ρ N M hMN ψ)) :=
  twistActionTwistEquiv ρ N M hMN χ hN ψ

@[simp]
theorem characterTwistedActionTwistEquiv_mk (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ)
    (hN : N ≤ χ.ker) (ψ : M →* Rˣ) (v : V) :
    characterTwistedActionTwistEquiv ρ N M hMN χ hN ψ (mk (twist χ ρ) N v) =
      mk ρ N v := rfl

@[simp]
theorem characterTwistedActionTwistEquiv_symm_mk (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ)
    (hN : N ≤ χ.ker) (ψ : M →* Rˣ) (v : V) :
    (characterTwistedActionTwistEquiv ρ N M hMN χ hN ψ).symm (mk ρ N v) =
      mk (twist χ ρ) N v := rfl

section Naturality

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- The identification commutes with the character-twisted induced maps. -/
theorem characterTwistedActionTwistEquiv_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) :
    (twistIntertwining (χ.comp M.subtype) (characterTwistedMap N M hMN ψ f)).comp
        (characterTwistedActionTwistEquiv ρ N M hMN χ hN ψ).toIntertwiningMap =
      (characterTwistedActionTwistEquiv σ N M hMN χ hN ψ).toIntertwiningMap.comp
        (characterTwistedMap N M hMN ψ (twistIntertwining χ f)) :=
  twistActionTwistEquiv_naturality N M hMN χ hN ψ f

theorem characterTwistedActionTwistEquiv_map_apply (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) (q : Coinvariants (twist χ ρ) N) :
    characterTwistedActionTwistEquiv σ N M hMN χ hN ψ
        (characterTwistedMap N M hMN ψ (twistIntertwining χ f) q) =
      characterTwistedMap N M hMN ψ f (characterTwistedActionTwistEquiv ρ N M hMN χ hN ψ q) :=
  twistActionTwistEquiv_map_apply N M hMN χ hN ψ f q

theorem characterTwistedActionTwistEquiv_symm_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) :
    (characterTwistedMap N M hMN ψ (twistIntertwining χ f)).comp
        (characterTwistedActionTwistEquiv ρ N M hMN χ hN ψ).symm.toIntertwiningMap =
      (characterTwistedActionTwistEquiv σ N M hMN χ hN ψ).symm.toIntertwiningMap.comp
        (twistIntertwining (χ.comp M.subtype) (characterTwistedMap N M hMN ψ f)) :=
  twistActionTwistEquiv_symm_naturality N M hMN χ hN ψ f

end Naturality

end CharacterTwisted

section Normalized

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- The Jacquet quotient normalized by a supplied positive modulus, of a twist by
a character trivial on `N`, is the twist of the normalized Jacquet quotient by
the restricted character. The same modulus `δ` normalizes both sides. -/
noncomputable def normalizedActionOfModulusTwistEquiv (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ)
    (hN : N ≤ χ.ker) (δ : M →* ℝ≥0ˣ) :
    (normalizedActionOfModulus (twist χ ρ) N M hMN δ).Equiv
      (twist (χ.comp M.subtype) (normalizedActionOfModulus ρ N M hMN δ)) :=
  twistActionTwistEquiv ρ N M hMN χ hN (inverseHalfCharacter δ)

/-- The normalized equivalence is the common-character equivalence at the
inverse half of the supplied modulus. -/
theorem normalizedActionOfModulusTwistEquiv_eq (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ)
    (hN : N ≤ χ.ker) (δ : M →* ℝ≥0ˣ) :
    normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ =
      twistActionTwistEquiv ρ N M hMN χ hN (inverseHalfCharacter δ) := rfl

@[simp]
theorem normalizedActionOfModulusTwistEquiv_mk (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ)
    (hN : N ≤ χ.ker) (δ : M →* ℝ≥0ˣ) (v : V) :
    normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ (mk (twist χ ρ) N v) =
      mk ρ N v := rfl

@[simp]
theorem normalizedActionOfModulusTwistEquiv_symm_mk (ρ : Representation ℂ G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ)
    (hN : N ≤ χ.ker) (δ : M →* ℝ≥0ˣ) (v : V) :
    (normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ).symm (mk ρ N v) =
      mk (twist χ ρ) N v := rfl

section Naturality

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The normalized identification commutes with the normalized induced maps. -/
theorem normalizedActionOfModulusTwistEquiv_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ) (hN : N ≤ χ.ker)
    (δ : M →* ℝ≥0ˣ) (f : ρ.IntertwiningMap σ) :
    (twistIntertwining (χ.comp M.subtype) (normalizedMapOfModulus N M hMN δ f)).comp
        (normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ).toIntertwiningMap =
      (normalizedActionOfModulusTwistEquiv σ N M hMN χ hN δ).toIntertwiningMap.comp
        (normalizedMapOfModulus N M hMN δ (twistIntertwining χ f)) :=
  twistActionTwistEquiv_naturality N M hMN χ hN (inverseHalfCharacter δ) f

theorem normalizedActionOfModulusTwistEquiv_map_apply (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ) (hN : N ≤ χ.ker)
    (δ : M →* ℝ≥0ˣ) (f : ρ.IntertwiningMap σ) (q : Coinvariants (twist χ ρ) N) :
    normalizedActionOfModulusTwistEquiv σ N M hMN χ hN δ
        (normalizedMapOfModulus N M hMN δ (twistIntertwining χ f) q) =
      normalizedMapOfModulus N M hMN δ f
        (normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ q) :=
  twistActionTwistEquiv_map_apply N M hMN χ hN (inverseHalfCharacter δ) f q

theorem normalizedActionOfModulusTwistEquiv_symm_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* ℂˣ) (hN : N ≤ χ.ker)
    (δ : M →* ℝ≥0ˣ) (f : ρ.IntertwiningMap σ) :
    (normalizedMapOfModulus N M hMN δ (twistIntertwining χ f)).comp
        (normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ).symm.toIntertwiningMap =
      (normalizedActionOfModulusTwistEquiv σ N M hMN χ hN δ).symm.toIntertwiningMap.comp
        (twistIntertwining (χ.comp M.subtype) (normalizedMapOfModulus N M hMN δ f)) :=
  twistActionTwistEquiv_symm_naturality N M hMN χ hN (inverseHalfCharacter δ) f

end Naturality

end Normalized

end Langlands.Jacquet
