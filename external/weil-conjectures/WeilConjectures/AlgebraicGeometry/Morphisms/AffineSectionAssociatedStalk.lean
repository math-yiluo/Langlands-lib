/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization

/-! # Detecting an affine section at an associated stalk

## References

* Stacks Project, Tag 0B3M, the cyclic image argument, and Tag 05AR
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Unequal sections on an affine open differ at an associated stalk. -/
theorem exists_associated_stalk_germ_ne_of_isAffineOpen
    {L : Scheme.{u}} [IsLocallyNoetherian L] (N : L.Modules)
    (hqc : N.IsQuasicoherent) (V : L.Opens) (hV : IsAffineOpen V)
    (hfinite : Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (s t : N.val.obj (op V)) (hne : s ≠ t) :
    ∃ (y : L) (hy : y ∈ V),
      IsAssociatedPrime (IsLocalRing.maximalIdeal (L.presheaf.stalk y))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) ∧
      N.presheaf.germ V y hy s ≠ N.presheaf.germ V y hy t := by
  classical
  have := hfinite
  let : IsNoetherianRing (L.presheaf.obj (op V)) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  by_contra h
  push Not at h
  have hz : s - t = 0 :=
    (Module.injective_pi_localization_associatedPrimes
      (L.presheaf.obj (op V)) (N.val.obj (op V))).2 (s - t) (by
      intro p
      let y : V := hV.isoSpec.inv ⟨p.1, p.2.isPrime⟩
      have hp : (hV.primeIdealOf y).asIdeal = p.1 := by
        have he : hV.primeIdealOf y = (⟨p.1, p.2.isPrime⟩ :
            PrimeSpectrum (L.presheaf.obj (op V))) := by
          change (hV.isoSpec.inv ≫ hV.isoSpec.hom) _ = _
          simp
        exact congrArg PrimeSpectrum.asIdeal he
      let : Module (L.presheaf.obj (op V))
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) :=
        Module.compHom _ (L.presheaf.germ V y y.2).hom
      obtain ⟨f, hf, hloc⟩ := isLocalizedModule_affine_germ N hqc V hV y
      let := hloc
      let := hV.isLocalization_stalk y
      let : IsScalarTower (L.presheaf.obj (op V)) (L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) :=
        IsScalarTower.of_algebraMap_smul (fun r m ↦ rfl)
      have hass : IsAssociatedPrime (IsLocalRing.maximalIdeal (L.presheaf.stalk y))
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) := by
        open Module.associatedPrimes in
          apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
            (hV.primeIdealOf y).asIdeal.primeCompl f
        change (IsLocalRing.maximalIdeal (L.presheaf.stalk y)).under
          (L.presheaf.obj (op V)) ∈ _
        rw [IsLocalization.AtPrime.under_maximalIdeal _ (hV.primeIdealOf y).asIdeal, hp]
        exact p.2
      have heq : f s = f t := by
        rw [hf, hf]
        exact h y y.2 hass
      obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists
        (hV.primeIdealOf y).asIdeal.primeCompl f).mp heq
      refine ⟨c, ?_, ?_⟩
      · rw [← hp]
        exact c.2
      · simpa only [smul_sub, sub_eq_zero, Submonoid.smul_def] using hc)
  exact hne (sub_eq_zero.mp hz)

end AlgebraicGeometry.Scheme
