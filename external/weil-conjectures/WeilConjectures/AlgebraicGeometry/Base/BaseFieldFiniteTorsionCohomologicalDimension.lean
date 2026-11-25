/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
import WeilConjectures.RepresentationTheory.DiscreteModule.FiniteFieldPrimeCohomology
import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.CategoryTheory.Sites.Point.Torsion
import WeilConjectures.RepresentationTheory.DiscreteModule.Torsion

/-!
# Torsion cohomological dimension of a finite base field

Source: the finite-field clause of `lemma-cohomological-dimension-base-field` (blueprint:
`det-base-field-cd-finite-torsion-bound`).

The proof follows the absolute Galois group computation for a finite field: every
geometric stalk is a torsion discrete module for the profinite completion of the
integers, and continuous cohomology of such a module vanishes above degree one.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite base field has torsion étale cohomological dimension at most one.

Source: Stacks Project, Tags 03QQ and 010T, and the finite-field part of
`lemma-cohomological-dimension-base-field` (blueprint: det-base-field-cd-finite-torsion-bound).

The proof identifies the small étale topos of `Spec K` with discrete modules for
its absolute Galois group. For finite `K`, the absolute Galois group is the profinite
completion of the integers. A torsion discrete module is the directed union of finite
stable submodules; each finite stable submodule factors through a finite cyclic quotient.
The periodic cyclic resolution and inflation along successive multiples kill every
cohomology class in degree at least two. The continuous cochain colimit therefore
vanishes in those degrees, and the stalk comparison transfers this vanishing to every
torsion étale sheaf.
-/
theorem hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField
    (K : Type u) [Field K] [Finite K] :
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 1 := by
  intro F hF q hq
  let Ω := SeparableClosure K
  have htwo : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (U : Subgroup Gal(Ω/K)),
      IsOpen (U : Set Gal(Ω/K)) →
        Subsingleton (DiscreteModule.H U (DiscreteModule.trivialZMod.{u + 1} U ℓ) 2) := by
    intro ℓ _ U hU
    have hE := InfiniteGalois.fixingSubgroup_fixedField_of_isOpen U hU
    have : FiniteDimensional K (IntermediateField.fixedField U) :=
      InfiniteGalois.finiteDimensional_fixedField_of_isOpen U hU
    let E := IntermediateField.fixedField U
    have : Finite E := Module.finite_of_finite K
    have : Algebra.IsSeparable E Ω := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    have : IsSepClosure E Ω := ⟨inferInstance, inferInstance⟩
    rw [← hE]
    have htwoE : Subsingleton (DiscreteModule.H Gal(Ω/E)
        (DiscreteModule.trivialZMod.{u + 1} Gal(Ω/E) ℓ) 2) := by
      by_cases hchar : (ℓ : E) = 0
      · have := (Spec (.of E)).subsingleton_sheafH_constantZMod_of_isAffine ℓ
          (by simpa using congrArg (ΓSpecIso (.of E)).inv.hom hchar) 2 le_rfl
        exact (sheafHConstantSheafAddEquivGaloisH E Ω _ 2).symm.injective.subsingleton
      · exact DiscreteModule.subsingleton_H_two_trivialZMod_of_finiteField E Ω ℓ hchar
    have := htwoE
    exact DiscreteModule.subsingleton_H_trivialZMod_of_continuousMulEquiv.{u + 1}
      E.fixingSubgroupContinuousMulEquiv ℓ 2
  have htors : ∀ x : ((etaleSheafEquivDiscreteModule K Ω).functor.obj F).obj.V,
      IsOfFinAddOrder x :=
    ((pointSmallEtale (specAlgebraMap K Ω)).ulift.{u + 1}).isAddTorsion_sheafFiber hF
  have := DiscreteModule.subsingleton_H_of_two_le_of_isTorsion htwo _ htors (by omega : 2 ≤ q)
  have : Subsingleton (CategoryTheory.Sheaf.H F q) :=
    (sheafHAddEquivGaloisH K Ω F q).injective.subsingleton
  have : Subsingleton ((CategoryTheory.Sheaf.functorH.{u + 1}
      (Spec (.of K)).smallEtaleTopology q).obj F) := by
    change Subsingleton (CategoryTheory.Sheaf.H F q)
    infer_instance
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso (Spec (.of K)) q
  exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry.Scheme
