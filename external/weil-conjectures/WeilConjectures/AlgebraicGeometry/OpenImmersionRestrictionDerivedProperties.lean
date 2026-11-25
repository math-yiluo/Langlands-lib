/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.AlgebraicGeometry.Restrict

/-! # Exactness and K-injective preservation for open-immersion restriction
Source: Stacks Project, Tag 08BS and sectionwise module limits (Tag 01AH).
(blueprint: lem-pc-open-immersion-restriction-derived-properties).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry


/-- Restriction along any open immersion is exact and preserves K-injective complexes.
Source: Stacks Project, Tag 08BS and sectionwise module limits (Tag 01AH).
Proof: identify the source with the image open subscheme. Under this isomorphism,
restriction is the composite of the localized-site restriction, the exact equivalence
from the localized site to the open subscheme, and the equivalence induced by the
source isomorphism. The first functor preserves finite limits and colimits, since
sections over opens in the source are the same sections in the target. It preserves
K-injectives by Tag 08BS: extension by zero is an exact left adjoint, and the adjunction
identifies Hom complexes against acyclic complexes. The two equivalences are exact and
preserve K-injectives. Transport these properties across the natural restriction
isomorphism and compose them. This also covers an empty image open.
(blueprint: lem-pc-open-immersion-restriction-derived-properties). -/
theorem openImmersion_restriction_derived_properties
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) ∧
      (Scheme.Modules.restrictFunctor j).PreservesKInjectiveComplexes := by
  classical
  let e := j.isoOpensRange
  let F := Scheme.Modules.restrictFunctor e.hom
  let G := Scheme.Modules.restrictFunctor e.inv
  let : F.IsEquivalence := Functor.IsEquivalence.mk' G
    ((Scheme.Modules.restrictFunctorId).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId)
  let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) j.opensRange
  let E := (Scheme.Modules.overEquiv j.opensRange).functor
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : E.Additive := Functor.additive_of_preserves_binary_products _
  let : R.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open Y.toRingedSpace j.opensRange I⟩
  have h : (R ⋙ E) ⋙ F ≅ Scheme.Modules.restrictFunctor j :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv j.opensRange) F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom j.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι
  exact ⟨inferInstance, Functor.preservesKInjectiveComplexes_of_iso h⟩

end AlgebraicGeometry
