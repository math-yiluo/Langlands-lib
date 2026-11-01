import Langlands.Representation.Whittaker.Transport

/-! # Entire coefficient ranges under surjective functional pullback -/

namespace Langlands.Whittaker

universe uR uG uV uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {N : Subgroup G} {θ : N →* Rˣ}
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Pulling back a specified nonzero functional along a surjection preserves
its nonzeroness. -/
theorem functionalsComap_ne_zero (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) (ℓ : functionals N θ σ) (hℓ : ℓ.val ≠ 0) :
    (functionalsComap f ℓ).val ≠ 0 := by
  intro hzero
  apply hℓ
  ext w
  obtain ⟨v, rfl⟩ := hf w
  exact LinearMap.congr_fun hzero v

/-- A pulled-back coefficient is the target coefficient of the image vector,
as an identity on the entire group. -/
theorem coefficient_functionalsComap (f : ρ.IntertwiningMap σ)
    (ℓ : functionals N θ σ) (v : V) (g : G) :
    (functionalsComap f ℓ).val (ρ g v) = ℓ.val (σ g (f v)) := by
  change ℓ.val (f (ρ g v)) = _
  rw [f.isIntertwining]

/-- A surjective intertwiner preserves the entire set of coefficient functions
of a specified functional, rather than merely their values at each group element. -/
theorem coefficientRange_functionalsComap (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) (ℓ : functionals N θ σ) :
    Set.range (fun v : V => fun g : G => (functionalsComap f ℓ).val (ρ g v)) =
      Set.range (fun w : W => fun g : G => ℓ.val (σ g w)) := by
  ext a
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨f v, funext fun g => (coefficient_functionalsComap f ℓ v g).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨v, funext fun g => coefficient_functionalsComap f ℓ v g⟩

end Langlands.Whittaker
