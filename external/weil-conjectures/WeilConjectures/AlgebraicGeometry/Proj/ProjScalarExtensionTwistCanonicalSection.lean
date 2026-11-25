/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData

/-! Pointwise evaluation of the section-normalized identity comparison.

## References

* Stacks Project, Tags 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The normalized identity pullback comparison evaluates a section at the same point. -/
theorem scalarExtension_twist_canonical_section
    {A : Type u} [CommRing A]
    {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (j : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(twist 𝒜 j, U))
    (x : (𝟙 (Proj 𝒜)) ⁻¹ᵁ U) :
    ((scalarExtensionTwistSection (𝟙 (Proj 𝒜))
      (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) j U s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 ⟨x.1, x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
  have hi := ((tensorPullbackSectionAdjunction (𝟙 (Proj 𝒜))).ofNatIsoRight
    (pushforwardId (Proj 𝒜))).unit_leftAdjointUniq_hom_app Adjunction.id (twist 𝒜 j)
  have hs := congrArg (fun z ↦ z.app U s) hi
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Hom.comp_app, pushforwardId_hom_app_app,
    Adjunction.id_unit, NatTrans.id_app, Hom.id_app] at hs
  change ((tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)).hom.app U
    (((tensorPullbackSectionAdjunction (𝟙 (Proj 𝒜))).unit.app (twist 𝒜 j)).app U s) = s
    at hs
  have hunit :
      ((tensorPullbackSectionAdjunction (𝟙 (Proj 𝒜))).unit.app (twist 𝒜 j)).app U s =
        tensorPullbackSection (𝟙 (Proj 𝒜)) (twist 𝒜 j) U s :=
    (Classical.choose_spec
      (existsUnique_tensorPullbackSectionAdjunction (𝟙 (Proj 𝒜)))).1 (twist 𝒜 j) U s
  erw [hunit] at hs
  exact congrArg (fun t : Γ(twist 𝒜 j, U) ↦
    (t.1 ⟨x.1, x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hs

end AlgebraicGeometry.Proj
