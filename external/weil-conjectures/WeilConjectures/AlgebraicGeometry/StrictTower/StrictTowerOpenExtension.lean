/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification

/-!
# Exact open extension on strict constant-coefficient towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-tower-open-extension).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The right-adjoint instance records the localized-site universal property.
Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable instance openPullback_rightAdjoint {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : (modulePullback B j).IsRightAdjoint := by
  simpa only [modulePullback] using
    (AlgebraicGeometry.Scheme.proEtaleOpenRestriction_isRightAdjoint j
      (coefficients B X) (coefficients B U) (constantRingIso B j))

/-- Open extension, determined up to its unit-preserving unique isomorphism by the
localized-site adjunction. Source: Stacks, Tag 09AE
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable abbrev moduleJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (modulePullback B j).leftAdjoint

/-- The ordinary open extension adjunction, with its specified unit and counit.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def moduleJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    moduleJ B j ⊣ modulePullback B j := Adjunction.ofIsRightAdjoint _

/-- Open extension is additive and exact, also on the empty open.
Source: Stacks, Tags 03DI and 03DJ
(blueprint: def-cbc-strict-tower-open-extension).
Proof: on the localized site the extension presheaf is the direct sum over lifts to
the open. Each object has at most one lift; stalkwise this is the original module or
zero. Sheafification is exact. The unit-preserving localization comparison transfers
additivity and exactness to the left adjoint chosen by its universal property. -/
theorem moduleJ_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (moduleJ B j).Additive ∧ PreservesFiniteLimits (moduleJ B j) ∧
      PreservesFiniteColimits (moduleJ B j) := by
  let P := AlgebraicGeometry.Scheme.proEtaleRingModulePullback j
    (coefficients B X) (coefficients B U) (constantRingIso B j)
  let E := AlgebraicGeometry.Scheme.proEtaleRingOpenExtension j
    (coefficients B X) (coefficients B U) (constantRingIso B j)
  let a : moduleJ B j ⊣ P := moduleJAdj B j
  let b : E ⊣ P := Adjunction.ofIsRightAdjoint P
  let e : E ≅ moduleJ B j := b.leftAdjointUniq a
  have hA : (moduleJ B j).Additive := Functor.additive_of_iso e
  have hL : PreservesFiniteLimits (moduleJ B j) :=
    preservesFiniteLimits_of_natIso e
  have hC : PreservesFiniteColimits (moduleJ B j) :=
    preservesFiniteColimits_of_natIso e
  exact ⟨hA, hL, hC⟩

/-- Additivity of open extension. Source: Stacks, Tag 03DI
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable instance moduleJ_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (moduleJ B j).Additive := (moduleJ_exact B j).1

/-- Left exactness of open extension. Source: Stacks, Tag 03DJ
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable instance moduleJ_finiteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (moduleJ B j) := (moduleJ_exact B j).2.1

/-- Right exactness of open extension. Source: Stacks, Tag 03DJ
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable instance moduleJ_finiteColimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (moduleJ B j) := (moduleJ_exact B j).2.2

/-- Termwise open extension before passage to complexes or localization.
Source: blueprint, first proof step (blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable abbrev towerJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B U) (Modules B X)).obj (moduleJ B j)

/-- Exactness persists on strict towers. Source: Stacks, Tag 03DJ and the diagram-site
realization (blueprint: def-cbc-strict-tower-open-extension).
Proof: finite limits and colimits in a functor category are levelwise; evaluation
reduces each comparison to the exactness statement for module extension by zero. -/
theorem towerJ_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (towerJ B j) ∧ PreservesFiniteColimits (towerJ B j) := by
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Left exactness of tower extension. Source: blueprint, first proof step
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable instance towerJ_finiteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (towerJ B j) := (towerJ_exact B j).1

/-- Right exactness of tower extension. Source: blueprint, first proof step
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable instance towerJ_finiteColimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (towerJ B j) := (towerJ_exact B j).2

/-- Exact open extension on derived strict towers.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Derived B U ⥤ Derived B X := (towerJ B j).mapDerivedCategory

/-- The exact derived open adjunction, retaining its termwise units.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J B j ⊣ G B j :=
  Adjunction.ofNatIsoRight
    (((moduleJAdj B j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction)
    (towerPullback B j).rightDerivedFunctorIsoMapDerivedCategory

/-- Composition of open extension with the composition-adjunction normalization.
Source: Stacks, Tags 03DI and 0F7D
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def jComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] : J B j ⋙ J B k ≅ J B (j ≫ k) :=
  Adjunction.leftAdjointCompIso (jAdj B j) (jAdj B k) (jAdj B (j ≫ k))
    (gComp B j k).symm

/-- Equality transport for the proof-irrelevant open-immersion structure.
Source: blueprint canonical composition identifications
(blueprint: def-cbc-strict-tower-open-extension).
Proof: substitute equality of the two scheme maps. The two open-immersion instances
are equal by proof irrelevance, so the constructed functors are definitionally equal. -/
theorem J_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J B f = J B g := by
  subst g
  rfl

/-- Transport open extension along equality of the underlying scheme maps.
Source: blueprint canonical composition identifications
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def jCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J B f ≅ J B g :=
  eqToIso (J_congr B h)

/-- The normalized open-extension identity.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def jId (X : Scheme.{u}) : J B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  Adjunction.leftAdjointIdIso (jAdj B (𝟙 X)) (gId B X)

/-- Evaluation commutes with strict termwise extension by zero.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-tower-open-extension).
Proof: the two functors have the identical object and morphism maps: extension
by zero of the n-th module and the n-th component of an extended tower. -/
theorem evaluationOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    towerJ B j ⋙ (evaluation ℕᵒᵖ (Modules B X)).obj (op n) =
      (evaluation ℕᵒᵖ (Modules B U)).obj (op n) ⋙ moduleJ B j := by
  rfl

/-- Evaluation of open extension uses precisely its termwise equality.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-tower-open-extension). -/
noncomputable def evalJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    J B j ⋙ ev B X n ≅ ev B U n ⋙ (moduleJ B j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso (evaluationOpen B j n)) ≪≫
  (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale.StrictTower
