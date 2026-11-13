/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Low-degree Herbrand quotients: Tate norm, `σ - 1`, fixed subgroup, right-regular action

Modified by Worker 5086: extract M113.001–M113.003 and M113.009 from the pinned
NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`
(lines 35–58 and 126–152), prefix the namespace with `Langlands.NYLL`, keep
the source's nine Mathlib imports unchanged, and write the section-variable telescope of
`rightRegularFunctionMulDistribMulAction` (source lines 62–64 with the `omit`
of lines 126–128) as explicit binders in the same order and binder kinds. The
declarations, their universes and their bodies, including every proof field,
are otherwise unchanged. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- Herbrand-quotient theory: the finite-group norm `N_G a = ∏ g, g • a`
for a multiplicative `G`-module. -/
def tateNorm (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (a : A) : A :=
  ∏ g : G, g • a

/-- Herbrand-quotient theory: the multiplicative coboundary `a^(σ-1)`. -/
def sigmaMinusOne (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : A) : A :=
  σ • a * a⁻¹

/-- Herbrand-quotient theory: the fixed subgroup `A^G`. -/
def fixedSubgroup (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] : Subgroup A where
  carrier := {a | ∀ g : G, g • a = a}
  one_mem' := by
    intro g
    exact MulDistribMulAction.smul_one g
  mul_mem' := by
    intro a b ha hb g
    rw [MulDistribMulAction.smul_mul, ha g, hb g]
  inv_mem' := by
    intro a ha g
    calc
      g • a⁻¹ = (g • a)⁻¹ := smul_inv' g a
      _ = a⁻¹ := by rw [ha g]

/-- The multiplicative induced module from the trivial subgroup, represented
as functions on `G` with the right-regular action. This is the concrete model
used in the low-degree Herbrand comparison. -/
@[reducible] def rightRegularFunctionMulDistribMulAction
    {G : Type uG} {B : Type uB} [Group G] [CommGroup B] :
    MulDistribMulAction G (G → B) where
  smul g f := fun x => f (x * g)
  one_smul := by
    intro f
    change (fun x => f (x * 1)) = f
    funext x
    rw [mul_one]
  mul_smul := by
    intro g h f
    change (fun x => f (x * (g * h))) = fun x => f ((x * g) * h)
    funext x
    rw [mul_assoc]
  smul_mul := by
    intro g f h
    funext x
    rfl
  smul_one := by
    intro g
    funext x
    rfl

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
