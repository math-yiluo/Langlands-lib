import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Algebra.Group.AddChar
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # The continuous multiplication pairing of a topological ring -/

noncomputable section

universe u

namespace Langlands.Global.RingPontryaginPairing

variable {R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Multiplication by a ring element followed by a continuous additive character. -/
def character (ψ : AddChar R Circle) (hψ : Continuous ψ) (a : Multiplicative R) :
    PontryaginDual (Multiplicative R) where
  toMonoidHom := (ψ.mulShift a.toAdd).toMonoidHom
  continuous_toFun := hψ.comp (continuous_const.mul continuous_toAdd)

@[simp]
theorem character_apply (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (a x : Multiplicative R) :
    character ψ hψ a x = ψ (a.toAdd * x.toAdd) := rfl

/-- The multiplication pairing as a homomorphism into the full compact-open dual. -/
def hom (ψ : AddChar R Circle) (hψ : Continuous ψ) :
    Multiplicative R →ₜ* PontryaginDual (Multiplicative R) where
  toFun := character ψ hψ
  map_one' := by
    apply PontryaginDual.ext
    intro x
    change ψ (0 * x.toAdd) = 1
    simp
  map_mul' a b := by
    apply PontryaginDual.ext
    intro x
    change ψ ((a.toAdd + b.toAdd) * x.toAdd) =
      ψ (a.toAdd * x.toAdd) * ψ (b.toAdd * x.toAdd)
    rw [add_mul, ψ.map_add_eq_mul]
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact hψ.comp ((continuous_toAdd.comp continuous_fst).mul
      (continuous_toAdd.comp continuous_snd))

@[simp]
theorem hom_apply (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (a x : Multiplicative R) : hom ψ hψ a x = ψ (a.toAdd * x.toAdd) := rfl

/-- A bijective multiplication pairing is a group homeomorphism when the ring is
locally compact and sigma compact. The conclusion retains the compact-open topology. -/
def equivOfBijective [LocallyCompactSpace R] [SigmaCompactSpace R]
    (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (hbij : Function.Bijective (hom ψ hψ)) :
    Multiplicative R ≃ₜ* PontryaginDual (Multiplicative R) := by
  let : SigmaCompactSpace (Multiplicative R) := ‹SigmaCompactSpace R›
  let e := MulEquiv.ofBijective (hom ψ hψ) hbij
  have hopen : IsOpenMap e :=
    (hom ψ hψ).toMonoidHom.isOpenMap_of_sigmaCompact hbij.2 (hom ψ hψ).continuous
  exact ContinuousMulEquiv.mk'
    (e.toEquiv.toHomeomorphOfContinuousOpen (hom ψ hψ).continuous hopen) e.map_mul

@[simp]
theorem equivOfBijective_apply [LocallyCompactSpace R] [SigmaCompactSpace R]
    (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (hbij : Function.Bijective (hom ψ hψ)) (a x : Multiplicative R) :
    equivOfBijective ψ hψ hbij a x = ψ (a.toAdd * x.toAdd) := rfl

end Langlands.Global.RingPontryaginPairing
