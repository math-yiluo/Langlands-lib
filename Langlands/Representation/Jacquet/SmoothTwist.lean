import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Twist.SmoothProof

/-!
# Smooth Jacquet actions and generic character twists

The character in this file is arbitrary. Modulus normalization is supplied
separately by taking the inverse positive square root of a modulus character.
-/

namespace Langlands.Jacquet

universe uR uG uV uW uX

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup X] [Module R X]

/-- A generic character twist of the actual Jacquet quotient action. -/
noncomputable def characterTwistedAction (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ) :
    Representation R M (Coinvariants ρ N) :=
  twist χ (action ρ N M hMN)

@[simp]
theorem characterTwistedAction_mk (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ)
    (m : M) (v : V) :
    characterTwistedAction ρ N M hMN χ m (mk ρ N v) =
      (χ m : R) • mk ρ N (ρ m v) := rfl

/-- The source action must be twisted too for the quotient map to intertwine. -/
noncomputable def characterTwistedQuotientMap (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ) :
    (twist χ (ρ.comp M.subtype)).IntertwiningMap
      (characterTwistedAction ρ N M hMN χ) :=
  twistIntertwining χ (quotientMap ρ N M hMN)

@[simp]
theorem characterTwistedQuotientMap_apply (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ) (v : V) :
    characterTwistedQuotientMap ρ N M hMN χ v = mk ρ N v := rfl

theorem characterTwistedQuotientMap_surjective (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ) :
    Function.Surjective (characterTwistedQuotientMap ρ N M hMN χ) :=
  mk_surjective ρ N

/-- The induced map for a common generic character twist. -/
noncomputable def characterTwistedMap
    {ρ : Representation R G V} {σ : Representation R G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) :
    (characterTwistedAction ρ N M hMN χ).IntertwiningMap
      (characterTwistedAction σ N M hMN χ) :=
  twistIntertwining χ (map N M hMN f)

@[simp]
theorem characterTwistedMap_mk
    {ρ : Representation R G V} {σ : Representation R G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) (v : V) :
    characterTwistedMap N M hMN χ f (mk ρ N v) = mk σ N (f v) := rfl

theorem characterTwistedMap_comp_quotientMap
    {ρ : Representation R G V} {σ : Representation R G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) :
    (characterTwistedMap N M hMN χ f).comp
        (characterTwistedQuotientMap ρ N M hMN χ) =
      (characterTwistedQuotientMap σ N M hMN χ).comp
        (twistIntertwining χ (restrictMap f M)) := by
  ext v
  rfl

@[simp]
theorem characterTwistedMap_id (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ) :
    characterTwistedMap N M hMN χ (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (characterTwistedAction ρ N M hMN χ) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

@[simp]
theorem characterTwistedMap_comp
    {ρ : Representation R G V} {σ : Representation R G W} {τ : Representation R G X}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    characterTwistedMap N M hMN χ (g.comp f) =
      (characterTwistedMap N M hMN χ g).comp (characterTwistedMap N M hMN χ f) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

section Smooth

variable [TopologicalSpace G]

/-- Smoothness descends along restriction and the actual surjective quotient map. -/
theorem isSmooth_action (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (hρ : IsSmooth ρ) :
    IsSmooth (action ρ N M hMN) :=
  isSmooth_of_surjective (quotientMap ρ N M hMN) (mk_surjective ρ N)
    (isSmooth_comp M.subtype continuous_subtype_val hρ)

/-- An open-kernel character preserves smoothness of the quotient action. -/
theorem isSmooth_characterTwistedAction (ρ : Representation R G V)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (χ : M →* Rˣ)
    (hχ : IsOpen (χ.ker : Set M)) (hρ : IsSmooth ρ) :
    IsSmooth (characterTwistedAction ρ N M hMN χ) :=
  (isSmooth_twist_iff χ (action ρ N M hMN) hχ).mpr
    (isSmooth_action ρ N M hMN hρ)

end Smooth

end Langlands.Jacquet
