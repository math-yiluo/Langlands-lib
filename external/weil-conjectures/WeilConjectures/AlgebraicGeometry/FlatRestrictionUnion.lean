/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact

/-! # Flatness on a union of finite locally free loci

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, cohomology-sheaf gluing
paragraph. (blueprint: lem-pc-flat-restriction-union).
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A module is flat on a union of opens where it is finite locally free.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, cohomology-sheaf gluing
paragraph; step 2 of lem-pc-derived-single-open-locus.
(blueprint: lem-pc-flat-restriction-union).

Proof: put W = the union of the U a. Each M restricted to U a is finite locally
free of some rank r a. Refine this cover by finite free trivializations. On each
trivializing open, tensoring with M is a finite direct sum of the identity,
hence preserves exact sequences. Tensor products commute with open restriction,
so the restriction of tensoring on W is tensoring with these finite free modules.
Exactness of a sequence of module sheaves can be checked on an open cover, or
on stalks. Thus tensoring with M restricted to W is exact, which is IsFlat.
Finite limits and colimits are preserved since this tensor functor is additive
between abelian categories and exact. No common rank or finite subcover is used.
For the empty family W is empty, the module category has only zero objects,
and every tensor functor is exact; rank-zero modules are also covered. -/
theorem isFlat_restrict_iSup_of_finiteLocallyFree
    {T : Scheme.{u}} (M : T.Modules) {ι : Type v} (U : ι → T.Opens)
    (hU : ∀ a, ∃ r : ℕ, ((restrictFunctor (U a).ι).obj M).IsFiniteLocallyFreeOfRank r) :
    SheafOfModules.IsFlat ((restrictFunctor (⨆ a, U a).ι).obj M) := by
  classical
  let W : T.Opens := ⨆ a, U a
  let N : W.toScheme.Modules := (restrictFunctor W.ι).obj M
  have hx (x : W) : ∃ a, x.val ∈ U a :=
    TopologicalSpace.Opens.mem_iSup.mp x.property
  let a : W → ι := fun x ↦ (hx x).choose
  let f (x : W) : (U (a x)).toScheme ⟶ W.toScheme :=
    T.homOfLE (le_iSup U (a x))
  have hf : ⨆ x, (f x).opensRange = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨x, ?_⟩
    change x ∈ (T.homOfLE (le_iSup U (a x))).opensRange
    rw [Scheme.opensRange_homOfLE]
    exact (hx x).choose_spec
  have hN : N.IsFiniteLocallyFree := by
    apply isFiniteLocallyFree_of_isOpenImmersion N f hf
    intro x
    obtain ⟨r, hr⟩ := hU (a x)
    have := hr
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((restrictFunctor (U (a x)).ι).obj M) r
    let e : ((pullback (f x)).obj N) ≅ (restrictFunctor (U (a x)).ι).obj M :=
      ((restrictFunctorIsoPullback (f x)).app N).symm ≪≫
        ((restrictFunctorComp (f x) W.ι).app M).symm ≪≫
        (restrictFunctorCongr (T.homOfLE_ι (le_iSup U (a x)))).app M
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} e.symm
  have := hN
  have h := finiteLocallyFree_tensorLeft_exact N
  have := h.1
  have := h.2
  change exactFunctor _ _ (MonoidalCategory.tensorRight N)
  exact ⟨preservesFiniteLimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight N),
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)⟩

end AlgebraicGeometry.Scheme.Modules
