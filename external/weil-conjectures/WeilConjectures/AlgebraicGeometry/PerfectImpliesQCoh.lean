/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh

@[expose] public section

universe u w

open CategoryTheory
namespace AlgebraicGeometry

/-- Perfect complexes have quasi-coherent cohomology.
Source: Stacks Project, Cohomology of Sheaves, Tags 08C4 and 08CM.
(blueprint: lem-sc-perfect-qcoherent).

Proof: restrict to a neighbourhood where the perfect complex is represented by a
strictly perfect complex. Its terms are direct summands of finite free sheaves,
which are quasi-coherent; kernels and cokernels of maps between quasi-coherent
modules on a scheme are quasi-coherent. Exact restriction and locality of
quasi-coherence transfer this to every cohomology sheaf. -/
theorem schemeDerivedQCohProperty_of_isPerfect
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedCategory X) (hK : Scheme.IsPerfect X K) :
    schemeDerivedQCohProperty X K := by
  apply Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent X K
  intro x
  obtain ⟨U, hxU, P, hP, hKP⟩ := hK x
  obtain ⟨V, hxV, _, _, F, ⟨a, b, hb⟩, hf, e⟩ :=
    Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect X K U P hP hKP x hxU
  exact ⟨V, hxV, F, ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩, hf, e⟩

end AlgebraicGeometry
