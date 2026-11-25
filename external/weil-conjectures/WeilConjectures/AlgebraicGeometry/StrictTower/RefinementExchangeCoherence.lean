/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionMaps
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import WeilConjectures.Compactification.Cofiltered
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus

/-!
# Refinement exchange coherence for strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7F; the final independence and naturality
argument of the blueprint proof of `proposition-composition-base-change-rf-shriek--4`
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).

`compositionF`, `compositionC` and `compositionE` are the already published canonical
compactification candidate, refinement comparison and proper/open exchange. The wrappers
below only supply quasi-compactness and invertibility, not a new choice of any operation.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The proper-adjunction mate determines the proper/open comparison uniquely.
Source: equality elimination and Stacks, Tag 07A7
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: use the displayed mate itself; any other transformation equal to it is the same.
This keeps its large construction behind a theorem when components are compared. -/
private theorem refinementGamma_existsUnique {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : ∃! δ : R B r ⋙ J B i ⟶ J B k ⋙ R B p,
      δ = gamma B k r p i h := by
  exact ⟨_, rfl, fun _ hδ ↦ hδ⟩

/-- The proper/open comparison is exactly the proper-adjunction mate of alpha.
Source: Stacks, Tags 0F7B and 07A7
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence). -/
private noncomputable def refinementGamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R B r ⋙ J B i ⟶ J B k ⋙ R B p :=
  Classical.choose (refinementGamma_existsUnique B k r p i h)

/-- The normalized comparison is the original proper-adjunction mate.
Source: Stacks, Tag 07A7 (blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: the defining choice has the displayed equality by its specification. -/
private theorem refinementGamma_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : refinementGamma B k r p i h =
      gamma B k r p i h :=
  (Classical.choose_spec (refinementGamma_existsUnique B k r p i h)).1

private theorem refinementExchange_existsUnique :
    ∃! E : ExchangeFamily (Derived B) (G B) (R B), @E = @exchange.{u} B _ := by
  exact ⟨@exchange.{u} B _, rfl, fun _ hE ↦ hE⟩

private noncomputable def refinementExchange : ExchangeFamily (Derived B) (G B) (R B) :=
  @Classical.choose (ExchangeFamily (Derived B) (G B) (R B)) _
    (refinementExchange_existsUnique B)

private theorem refinementExchange_eq : @refinementExchange.{u} B _ = @exchange.{u} B _ :=
  (@Classical.choose_spec (ExchangeFamily (Derived B) (G B) (R B)) _
    (refinementExchange_existsUnique B)).1

private theorem refinementExchange_app_eq {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) :
    refinementExchange B a f' f b w = exchange B a f' f b w := by
  exact congrArg (fun E : ExchangeFamily (Derived B) (G B) (R B) ↦ E a f' f b w)
    (refinementExchange_eq B)

private theorem refinementMatePasting :
    matePastingLaw (G B) (R B) (@rCompEq.{u} B _) (@refinementExchange.{u} B _) := by
  exact (congrArg (matePastingLaw (G B) (R B) (@rCompEq.{u} B _))
    (refinementExchange_eq B)).mpr (strictTowerMatePasting B)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
-- Work with whole natural transformations before specializing components.
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G R J rId rComp gamma adj exchange
  towers_hasDerivedCategory

end AlgebraicGeometry.ProEtale.StrictTower
