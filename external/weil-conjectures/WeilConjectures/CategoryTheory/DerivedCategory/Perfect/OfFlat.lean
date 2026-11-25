/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Bounded flat complexes with finite cohomology over a Noetherian ring are perfect

Let `A` be a Noetherian ring and `C` an object of `D(A)` represented by a bounded complex of flat
`A`-modules, all of whose cohomology modules are finitely generated. Then `C` is represented by a
bounded complex of finitely generated projective `A`-modules
(`DerivedCategory.isPerfect_of_flat_of_finite_homology`).

A bounded complex `F` of flat modules concentrated in `[a, b]` is K-flat, so for every module `N`
the derived tensor product `F ⊗ᴸ N` is the tensor product of complexes `F ⊗ N`, concentrated in
`[a, b]`: `C` has Tor amplitude in `[a, b]` (`DerivedCategory.torAmplitudeIn_Q_obj_of_flat`).
A bounded complex with finitely generated cohomology and finite Tor amplitude over a Noetherian
ring is perfect (`DerivedCategory.isPerfect_of_finiteTorAmplitude`): one resolves `C` by finite
free modules from the top degree down, and the cokernel in the lowest degree `a` is flat by the
Tor criterion, as `H^{a-1}(F ⊗ N) = 0`, and finitely presented, hence projective.
-/

@[expose] public section

universe u

open CategoryTheory

namespace DerivedCategory

variable {A : Type u} [CommRing A] [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- **A bounded flat complex with finite cohomology over a Noetherian ring is perfect.** Let `A`
be Noetherian and `C` an object of `D(A)` isomorphic to the image of a complex `F` of flat
`A`-modules concentrated in degrees `[a, b]`. If every cohomology module `H^i(C)` is finitely
generated, then `C` is represented by a bounded complex of finitely generated projective
`A`-modules (`DerivedCategory.IsPerfect`).

The complex `F` gives `C` Tor amplitude in `[a, b]`, and a bounded object with finitely
generated cohomology and finite Tor amplitude is perfect.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem isPerfect_of_flat_of_finite_homology [IsNoetherianRing A]
    {C : DerivedCategory (ModuleCat.{u} A)} (F : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b] (hF : ∀ n, Module.Flat A (F.X n)) (e : C ≅ Q.obj F)
    (hfin : ∀ i, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj C)) :
    C.IsPerfect := by
  have hTor : torAmplitudeIn (ModuleCat.{u} A) a b C :=
    (torAmplitudeIn (ModuleCat.{u} A) a b).prop_of_iso e.symm
      (torAmplitudeIn_Q_obj_of_flat F a b fun n ↦ (ModuleCat.flat_iff_flat _).2 (hF n))
  exact isPerfect_of_finiteTorAmplitude
    ((exists_homologyConcentratedIn_iff_bounded C).1
      ⟨a, b, homologyConcentratedIn_of_torAmplitudeIn hTor⟩) hfin ⟨a, b, hTor⟩

end DerivedCategory
