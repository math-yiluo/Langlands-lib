/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal
import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Strong monoidal descent of open restriction
Source: Stacks Project, Tags 06YH and 079U.
(blueprint: lem-pc-open-restriction-derived-monoidal).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Use the standard localization on the open scheme.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-open-restriction-derived-monoidal). -/
local instance openRestrictionMonoidalStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- Strong monoidal descent of exact restriction to the standard category on the open.

Source: Stacks Project, cohomology.tex, Tags 06YH and 079U.
(blueprint: lem-pc-open-restriction-derived-monoidal).

Proof: identify tensor pullback along U.ι with ordinary restriction by
uniqueness of left adjoints to pushforward. Compose with overFunctorEquiv to
identify it with the exact over-site restriction followed by overEquiv.
Transport finite-limit and finite-colimit preservation through this isomorphism.
The exact tensor pullback's mapDerivedCategory is a left derived functor,
with mapDerivedCategoryFactorsh as its invertible counit. The transported
pullback across universes has its left-derived counit by
exists_derivedPullbackAcrossUniverses_leftDerived. Uniqueness of left derived
functors identifies the two. Derive the module isomorphism and use
mapDerivedCategoryCompIso to identify the displayed composite R with this
transported pullback. Compose the strong monoidal standard-localization
comparisons with the standard derived pullback monoidal model, then transport
the resulting monoidal structure along the comparison to R. All these are
functor isomorphisms, so both unit equations, associativity, and invertibility
are preserved. The construction uses each localization's own universe and
applies without change to the empty open and zero complexes. -/
theorem exists_openRestriction_derivedMonoidal (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    Nonempty R.Monoidal := by
  classical
  dsimp only
  let O := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let A : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  let R := O ⋙ A
  let P : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let η : P ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction U.ι)
  let θ : R ≅ P := Scheme.Modules.overFunctorEquiv U ≪≫ η.symm
  have : PreservesFiniteLimits P := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits P := preservesFiniteColimits_of_natIso θ
  obtain ⟨ε, hε⟩ := exists_derivedPullbackAcrossUniverses_leftDerived U.ι P
    (fun _ ↦ rfl) (by
      intros
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullbackAcrossUniverses U.ι).IsLeftDerivedFunctor ε W := hε
  have : P.mapDerivedCategory.IsLeftDerivedFunctor P.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ P.mapDerivedCategoryFactorsh
  let e : O.mapDerivedCategory ⋙ A.mapDerivedCategory ≅
      derivedPullbackAcrossUniverses U.ι :=
    Functor.mapDerivedCategoryCompIso O A ≪≫
      Functor.mapDerivedCategoryNatIso θ ≪≫
        Functor.leftDerivedUnique (derivedPullbackAcrossUniverses U.ι) P.mapDerivedCategory
          P.mapDerivedCategoryFactorsh.hom ε W
  obtain ⟨mX⟩ := exists_schemeDerivedStandardEquivalence_monoidal X
  obtain ⟨mU⟩ := exists_schemeDerivedStandardEquivalence_monoidal U.toScheme
  let := mX.toMonoidal
  let := mU.toMonoidal
  let := (schemeDerivedStandardEquivalence U.toScheme).inverseMonoidal
  obtain ⟨m, _⟩ := @exists_derivedPullbackMonoidalModel U.toScheme X U.ι
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  let := m.toMonoidal
  let : (derivedPullbackAcrossUniverses U.ι).Monoidal := by
    unfold derivedPullbackAcrossUniverses
    infer_instance
  exact ⟨Functor.Monoidal.transport e.symm⟩

end AlgebraicGeometry
