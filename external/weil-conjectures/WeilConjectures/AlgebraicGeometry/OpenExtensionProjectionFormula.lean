/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedAdjunction
import WeilConjectures.AlgebraicGeometry.OpenExtensionProjectionFormulaAux

/-! # Projection formula for open extension by zero
Source: Stacks Project, Tags 08BS, 01AK and 06YB.
(blueprint: lem-pc-open-extension-projection-formula).
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
(blueprint: lem-pc-open-extension-projection-formula). -/
local instance openExtensionProjectionStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

set_option linter.style.haveILetI false in
/-- Exact extension by zero satisfies the tensor projection formula for any
strong monoidal structure on the specified derived restriction functor.

Source: Stacks Project, cohomology.tex, Tag 08BS (exact extension by zero),
modules.tex, Tag 01AK; Tags 06YB and 06YH for the stalkwise tensor computation.
(blueprint: lem-pc-open-extension-projection-formula).

Proof: compose the inverse over-site equivalence with ordinary extension by zero
(the extension presheaf followed by sheafification) to construct J. Both factors
are exact. Derive the ordinary extension/restriction adjunction through the
specified localizations, using their factorization isomorphisms separately.
This gives J left adjoint to R. Its unit is invertible, as may be checked first
on ordinary modules on U and then on complexes. The counit on any complex whose
cohomology stalks outside U vanish is invertible: on U it is identified with the
identity by the adjunction identities, and outside U both stalk cohomologies
are zero. Thus these supported complexes are precisely J's essential image.
They form a subcategory where R reflects isomorphisms, since the cone of such
a map with acyclic restriction has acyclic stalks at every point of X.
For A on U, J(A) tensor K is supported on U. Compute using K-flat representatives:
stalks commute with the total tensor, K-flatness is stalkwise, and the acyclic
stalk of J(A) outside U tensored with a K-flat stalk remains acyclic.
Let p be the displayed adjunction transpose. Its source and target are both
supported. Applying R to p gives, by the defining homEquiv equation,
unit_(A tensor R(K)) inverse followed by (unit_A tensor identity) and μ_R.
Each factor is invertible. Reflection on the supported subcategory therefore
makes p invertible. No special choice of m is needed. Zero inputs and the
empty open give the same calculation between zero objects. Independent
localization universes do not affect the unit, counit or cone identities.
The left adjoint is constructed as above and is uniquely determined up to the
adjunction isomorphism; no arbitrary module or complex witness is chosen. -/
theorem exists_openExtension_projectionFormula (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ m : R.Monoidal,
      letI := m
      ∃ J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X,
        ∃ adj : J ⊣ R,
          ∀ (A : schemeDerivedCategory U.toScheme) (K : schemeDerivedCategory X),
            IsIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
              ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
                (Functor.Monoidal.μIso R (J.obj A) K).hom)) := by
  dsimp
  intro m
  have h := exists_openExtension_derivedAdjunction X U
  letI := m
  obtain ⟨J, ⟨adj⟩⟩ := h
  refine ⟨J, adj, ?_⟩
  exact openExtension_projection_formula_of_adjunction X U m J adj

end AlgebraicGeometry
