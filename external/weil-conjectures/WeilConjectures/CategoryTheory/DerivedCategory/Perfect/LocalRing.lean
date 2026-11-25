/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Perfect complexes over a local ring

A perfect complex over a commutative ring has finite Tor amplitude, and over a local ring it is
represented by a bounded complex of finitely generated *free* modules. Over a Noetherian local
ring (for instance the finite coefficient ring `A_{E,n} = 𝒪_E/ϖⁿ`), a bounded complex with
finite cohomology modules therefore has finite Tor amplitude exactly when it is quasi-isomorphic
to a bounded complex of finite free modules (`lemma-perfect-complexes-geometric-point--1`).

## Main statements

- `DerivedCategory.IsPerfect.torAmplitudeIn`, `DerivedCategory.IsPerfect.finiteTorAmplitude`:
  a perfect complex has finite Tor amplitude.
- `DerivedCategory.IsPerfect.exists_free`: over a local ring a perfect complex is represented by
  a bounded complex of finite free modules.
- `DerivedCategory.finiteTorAmplitude_iff_exists_free`
(`lemma-perfect-complexes-geometric-point--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- A bounded complex of finitely generated projective modules concentrated in `[a, b]` has Tor
amplitude in `[a, b]`: its terms are flat. -/
theorem torAmplitudeIn_Q_obj_of_projective (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ i, Module.Projective R (P.X i)) :
    torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj P) :=
  torAmplitudeIn_Q_obj_of_flat P a b fun n ↦ by
    have := hP n
    exact (ModuleCat.flat_iff_flat _).2 inferInstance

/-- A perfect complex has finite Tor amplitude. -/
theorem IsPerfect.finiteTorAmplitude {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    finiteTorAmplitude (ModuleCat.{u} R) C := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hC
  exact ⟨a, b, (torAmplitudeIn _ a b).prop_of_iso e.symm
    (torAmplitudeIn_Q_obj_of_projective P a b fun i ↦ (hP i).1)⟩

/-- Over a local ring, a perfect complex is quasi-isomorphic to a bounded complex of finitely
generated free modules: a finitely generated projective module over a local ring is free. -/
theorem IsPerfect.exists_free [IsLocalRing R] {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P) := by
  obtain ⟨P, a, b, ha, hb, hP, e⟩ := hC
  refine ⟨P, a, b, ha, hb, fun i ↦ ?_, e⟩
  have := (hP i).1
  have := (hP i).2
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point--1`: Finite Tor amplitude and perfectness
over the finite coefficient ring.

Let `R` be a Noetherian local ring (for instance the finite coefficient ring
`A_{E,n} = 𝒪_E/ϖⁿ`, a local Artinian ring) and `C` a bounded complex of `R`-modules with finite
cohomology modules. Then `C` has finite Tor amplitude if and only if it is quasi-isomorphic to
a bounded complex of finitely generated free `R`-modules, that is, lies in the category
`D^b_fin(R)` of `definition-categorical-trace`. The direct implication is
`DerivedCategory.isPerfect_of_finiteTorAmplitude` followed by freeness of finite projective
modules over a local ring; the converse holds since free modules are flat. The Tor amplitude
hypothesis cannot be dropped: `R/𝔪` has infinite Tor dimension unless `R` is regular. -/
theorem finiteTorAmplitude_iff_exists_free [IsLocalRing R] [IsNoetherianRing R]
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : TStructure.t.bounded C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    finiteTorAmplitude (ModuleCat.{u} R) C ↔
      ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧
        P.IsStrictlyLE b ∧ (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
        Nonempty (C ≅ Q.obj P) := by
  constructor
  · intro h
    exact (isPerfect_of_finiteTorAmplitude hC hfin h).exists_free
  · rintro ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩
    exact ⟨a, b, (torAmplitudeIn _ a b).prop_of_iso e.symm
      (torAmplitudeIn_Q_obj_of_projective P a b fun i ↦
        have := (hP i).1
        inferInstance)⟩

end DerivedCategory
