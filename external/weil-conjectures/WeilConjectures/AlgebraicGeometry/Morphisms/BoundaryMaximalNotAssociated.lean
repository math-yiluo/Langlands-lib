/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.BoundaryLocalizedFiniteDetector

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-! The algebraic core: a module with no nonzero element annihilated by the
maximal ideal has no maximal associated prime.

## References

* Stacks Project, Tag 0AVN, finite basic-open cover argument
* Tags 01LC and 05AM
-/
private theorem no_maximal_associated_of_annihilator_zero
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hz : ∀ z : M, (∀ a : IsLocalRing.maximalIdeal R, (a : R) • z = 0) → z = 0) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R M := by
  intro h
  obtain ⟨hp, z, he⟩ := isAssociatedPrime_iff.mp h
  have hz0 : z = 0 := hz z (fun a ↦ by
    have ha : (a : R) ∈ (⊥ : Submodule R M).colon {z} := he ▸ a.property
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using ha)
  subst z
  exact hp.ne_top (he.trans (by simp))

/-- The maximal ideal is not associated to a boundary localization of a submodule
of restriction sections. -/
theorem boundary_maximal_not_associated
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens) (N : L.Modules)
    (hqc : N.IsQuasicoherent) (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG) (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hy : hV.fromSpec ⟨p, inferInstance⟩ ∉ U) :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) ∉
      associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p S) := by
  have _hS := hS
  let : IsNoetherianRing (L.presheaf.obj (op V)) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  apply no_maximal_associated_of_annihilator_zero
  obtain ⟨n, Q, a, φ, hinj, hzero⟩ :=
    boundary_localized_finite_detector U N hqc V hV S p hy
  intro z hz
  apply hzero z
  intro i
  apply hinj i
  change (a i : Localization.AtPrime p) • φ i z =
    (a i : Localization.AtPrime p) • (0 : Q i)
  rw [smul_zero, ← (φ i).map_smul, hz (a i), map_zero]


end AlgebraicGeometry.Scheme
