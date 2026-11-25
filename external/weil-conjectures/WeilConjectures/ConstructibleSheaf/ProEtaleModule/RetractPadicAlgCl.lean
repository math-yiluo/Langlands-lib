/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import WeilConjectures.Mathlib.CategoryTheory.Retract

/-!
# Retracts of constructible `ℚ̄_ℓ`-complexes

On a topologically noetherian scheme `T`, constructible module objects over the coefficient ring
`ℚ̄_ℓ,T` are closed under retracts, and hence so are bounded constructible complexes in the
derived category.

## Main results

- `ProEtale.isConstructibleModuleObject_of_retract_padicAlgClRingObj`: a retract of a
  constructible `ℚ̄_ℓ,T`-module object is constructible.
- `ProEtale.boundedConstructible_of_retract_padicAlgClRingObj`: a retract of a bounded
  constructible `ℚ̄_ℓ,T`-complex is bounded constructible.

A retract `M` of `N` is the cokernel of the endomorphism `𝟙 N - r ≫ i` of `N`, so the first
result follows from the closure of constructible module objects under cokernels
(`ProEtale.isConstructibleModuleObject_serre_padicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Constructible `ℚ̄_ℓ,T`-module objects on a topologically noetherian scheme are closed under
retracts. -/
theorem isConstructibleModuleObject_of_retract_padicAlgClRingObj {T : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ)}
    (e : Retract M N) (hN : IsConstructibleModuleObject (padicAlgClRingObj T ℓ) N) :
    IsConstructibleModuleObject (padicAlgClRingObj T ℓ) M :=
  (((isConstructibleModuleObject_serre_padicAlgCl T ℓ).1 N N _ hN hN).2).of_iso
    e.isoCokernel.symm

/-- Bounded constructible `ℚ̄_ℓ`-complexes on a topologically noetherian scheme are closed under
retracts. -/
theorem boundedConstructible_of_retract_padicAlgClRingObj {T : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (e : Retract K L) (hL : boundedConstructible _ L) : boundedConstructible _ K := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ L).1 hL
  exact (mem_boundedConstructible_iff _ K).2
    ⟨⟨a, b, fun i hi ↦ (e.map (DerivedCategory.homologyFunctor _ i)).isZero (hab i hi)⟩,
      fun n ↦ isConstructibleModuleObject_of_retract_padicAlgClRingObj ℓ
        (e.map (DerivedCategory.homologyFunctor _ n)) (hc n)⟩

end AlgebraicGeometry.ProEtale
