import Langlands.ClassFieldTheory.Local.Cohomology
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Conjugacy transport for relative Galois cohomology

A compatible pair of field isomorphisms transports the actual Galois group,
its action on units, and its group cohomology.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v w

variable {K : Type v} {K' : Type w} {L L' : Type u}
  [Field K] [Field K'] [Field L] [Field L']
  [Algebra K L] [Algebra K' L']

/-- The two field isomorphisms form a commuting square of algebra maps. -/
def CompatibleFieldEquivalences (eK : K ≃+* K') (eL : L ≃+* L') : Prop :=
  ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)

theorem CompatibleFieldEquivalences.symm
    {eK : K ≃+* K'} {eL : L ≃+* L'}
    (h : CompatibleFieldEquivalences eK eL) :
    CompatibleFieldEquivalences eK.symm eL.symm := by
  intro x
  apply eL.injective
  simpa using (h (eK.symm x)).symm

/-- Conjugate an actual algebra automorphism by a compatible field isomorphism. -/
def conjugateAutomorphism (eK : K ≃+* K') (eL : L ≃+* L')
    (h : CompatibleFieldEquivalences eK eL) (σ : Gal(L/K)) : Gal(L'/K') where
  __ := eL.symm.trans (σ.toRingEquiv.trans eL)
  commutes' x := by
    change eL (σ (eL.symm (algebraMap K' L' x))) = algebraMap K' L' x
    rw [h.symm x, σ.commutes, h, eK.apply_symm_apply]

@[simp]
theorem conjugateAutomorphism_apply (eK : K ≃+* K') (eL : L ≃+* L')
    (h : CompatibleFieldEquivalences eK eL) (σ : Gal(L/K)) (x : L') :
    conjugateAutomorphism eK eL h σ x = eL (σ (eL.symm x)) := rfl

/-- The genuine Galois-group isomorphism attached to a commuting field square. -/
def galoisConjugacy (eK : K ≃+* K') (eL : L ≃+* L')
    (h : CompatibleFieldEquivalences eK eL) : Gal(L/K) ≃* Gal(L'/K') where
  toFun := conjugateAutomorphism eK eL h
  invFun := conjugateAutomorphism eK.symm eL.symm h.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp
  map_mul' σ τ := by ext x; simp

/-- Transport of additive units, linear over the same lifted integer ring used
by `unitsRepresentation`. -/
def unitsConjugacy (eL : L ≃+* L') :
    Additive Lˣ ≃ₗ[IntegerScalars.{u}] Additive L'ˣ :=
  (Units.mapEquiv eL.toMulEquiv).toAdditive.toIntLinearEquiv.restrictScalars
    IntegerScalars.{u}

theorem unitsConjugacy_intertwines (eK : K ≃+* K') (eL : L ≃+* L')
    (h : CompatibleFieldEquivalences eK eL) (σ : Gal(L/K)) :
    (unitsConjugacy eL).toLinearMap ∘ₗ (unitsRepresentation K L).ρ σ =
      (unitsRepresentation K' L').ρ (galoisConjugacy eK eL h σ) ∘ₗ
        (unitsConjugacy eL).toLinearMap := by
  ext x
  change eL (σ (x : Lˣ).val) = eL (σ (eL.symm (eL (x : Lˣ).val)))
  rw [eL.symm_apply_apply]

/-- Relative cohomology transport induced by an actual compatible field square.
No cohomology equivalence is supplied as an input. -/
def relativeConjugacy (eK : K ≃+* K') (eL : L ≃+* L')
    (h : CompatibleFieldEquivalences eK eL) (n : ℕ) :
    relativeCohomology K L n ≅ relativeCohomology K' L' n :=
  groupCohomology.mapIso (galoisConjugacy eK eL h) (unitsConjugacy eL)
    (unitsConjugacy_intertwines eK eL h) n

end Langlands.ClassFieldTheory.Local
