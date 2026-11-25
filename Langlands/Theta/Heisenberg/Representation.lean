import Langlands.Theta.Heisenberg.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Basic

/-!
# Representations of a Heisenberg group: central character and normalizing operators

Two predicates on representations of `HeisenbergGroup B` (GKT §1.1 and §2.1.2):

* `HasCentralCharacter ρ ψ`: the central element `(0, t)` acts by `ψ t`;
* `Normalizes ρ a ω`: for a group `G` acting on the Heisenberg group by `a`, the representation `ω`
  of `G` carries `ρ h` to `ρ (a g h)`: `ω g ∘ ρ h = ρ (a g h) ∘ ω g`. For `G` the symplectic group
  acting as in GKT (2.1) this is relation (2.2), which defines the pairs of the metaplectic group.
-/

namespace Langlands.HeisenbergGroup

universe u v

variable {R : Type u} [CommRing R] {W : Type v} [AddCommGroup W] [Module R W]
  {B : LinearMap.BilinForm R W}

/-- `ρ` has central character `ψ`: the central element `(0, t)` acts by `ψ t`. -/
def HasCentralCharacter {S : Type*} [AddCommGroup S] [Module ℂ S] [Invertible (2 : R)]
    (ρ : Representation ℂ (HeisenbergGroup B) S) (ψ : AddChar R ℂ) : Prop :=
  ∀ (t : R) (v : S), ρ (central t) v = ψ t • v

/-- `ω` normalizes `ρ` along the action `a` of `G` on the Heisenberg group:
`ω g ∘ ρ h = ρ (a g h) ∘ ω g`. -/
def Normalizes {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S] [Invertible (2 : R)]
    (ρ : Representation ℂ (HeisenbergGroup B) S) (a : G →* MulAut (HeisenbergGroup B))
    (ω : Representation ℂ G S) : Prop :=
  ∀ (g : G) (h : HeisenbergGroup B), ω g ∘ₗ ρ h = ρ (a g h) ∘ₗ ω g

variable [Invertible (2 : R)]

/-- The normalizing relation on vectors. -/
theorem Normalizes.apply {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
    {ρ : Representation ℂ (HeisenbergGroup B) S} {a : G →* MulAut (HeisenbergGroup B)}
    {ω : Representation ℂ G S} (h : Normalizes ρ a ω) (g : G) (k : HeisenbergGroup B) (v : S) :
    ω g (ρ k v) = ρ (a g k) (ω g v) :=
  LinearMap.congr_fun (h g k) v

/-- With a central character, the action of `(w, t)` is `ψ t` times the action of `(w, 0)`. -/
theorem HasCentralCharacter.apply_eq {S : Type*} [AddCommGroup S] [Module ℂ S]
    {ρ : Representation ℂ (HeisenbergGroup B) S} {ψ : AddChar R ℂ} (h : HasCentralCharacter ρ ψ)
    (g : HeisenbergGroup B) (v : S) : ρ g v = ψ g.cen • ρ (ofVec g.vec) v := by
  rw [← h, ← Module.End.mul_apply, ← map_mul, central_mul_ofVec]

end Langlands.HeisenbergGroup
