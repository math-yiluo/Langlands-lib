/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions

/-!
# Low-degree Herbrand quotients: right-regular cyclic primitives and transport data

Modified by Worker 5086: extract M113.058, M113.080, M113.085, M113.089,
M113.101 and M113.103 from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`
(lines 701–707, 1029–1036, 1090–1098, 1137–1146, 1466–1497 and 1521–1557),
prefix the namespace with `Langlands.NYLL`, and write the section-variable
telescope that each declaration includes after its `omit` (source lines 62–64)
as explicit binders in the same order and binder kinds. The source's nine
Mathlib imports and `tateNorm`, `sigmaMinusOne`, `fixedSubgroup` and
`rightRegularFunctionMulDistribMulAction` come from the sibling `Definitions`
module through the import above. The declarations, their universes,
attributes and bodies, including every proof field, are otherwise unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- Fixed subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionFixedSubgroup
    {G : Type uG} {B : Type uB} [Group G] [CommGroup B] : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact fixedSubgroup G (G → B)

/-- The partial primitive along the cyclic powers of `σ`.  This is the
candidate used to solve `b (x * σ) * (b x)⁻¹ = f x` on the right-regular
induced module. -/
def rightRegularCyclicPartialProduct
    {G : Type uG} {B : Type uB} [Group G] [CommGroup B]
    (σ : G) (f : G → B) (i : ℕ) : B :=
  (Finset.range i).prod (fun k => f (σ ^ k))

/-- The canonical `ZMod |G|` index of a group element with respect to a chosen
cyclic generator. -/
noncomputable def rightRegularCyclicIndex
    {G : Type uG} [Group G] [Fintype G]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : G) :
    ZMod (Fintype.card G) :=
  Classical.choose (IsCyclic.unique_zpow_zmod (a := σ) hgen x)

/-- The group-element-indexed primitive candidate obtained from the cyclic
partial products. -/
noncomputable def rightRegularCyclicPrimitive
    {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B) : G → B :=
  fun x =>
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f
      (rightRegularCyclicIndex (G := G) σ hgen x).val

/-- A distributive action on an additive group induces a multiplicative action
on its `Multiplicative` wrapper. -/
@[reducible] def multiplicativeMulDistribMulActionOfDistribMulAction
    (G : Type uG) (M : Type uA) [Group G] [AddCommGroup M]
    [DistribMulAction G M] :
    MulDistribMulAction G (Multiplicative M) where
  smul g m := Multiplicative.ofAdd (g • Multiplicative.toAdd m)
  one_smul := by
    intro m
    change Multiplicative.ofAdd (1 • Multiplicative.toAdd m) =
      Multiplicative.ofAdd (Multiplicative.toAdd m)
    rw [one_smul]
  mul_smul := by
    intro g h m
    change Multiplicative.ofAdd ((g * h) • Multiplicative.toAdd m) =
      Multiplicative.ofAdd (g • h • Multiplicative.toAdd m)
    rw [mul_smul]
  smul_mul := by
    intro g m n
    change Multiplicative.ofAdd (g • Multiplicative.toAdd (m * n)) =
      Multiplicative.ofAdd
        (g • Multiplicative.toAdd m + g • Multiplicative.toAdd n)
    rw [show Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n from rfl]
    rw [smul_add]
  smul_one := by
    intro g
    change Multiplicative.ofAdd (g • (0 : M)) = Multiplicative.ofAdd (0 : M)
    rw [smul_zero]

/-- Convert an additive equivalence with a function space into the
multiplicative right-regular function model used by the Herbrand quotient API. -/
def mulEquivRightRegularFunctionOfAddEquiv
    (G : Type uG) {M : Type uA} {D : Type uB}
    [AddCommGroup M] [AddCommGroup D] (e : M ≃+ (G → D)) :
    Multiplicative M ≃* (G → Multiplicative D) where
  toFun m := fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd m) x)
  invFun f := Multiplicative.ofAdd (e.symm (fun x => Multiplicative.toAdd (f x)))
  left_inv := by
    intro m
    change Multiplicative.ofAdd
        (e.symm (e (Multiplicative.toAdd m))) =
      Multiplicative.ofAdd (Multiplicative.toAdd m)
    exact congrArg Multiplicative.ofAdd (e.left_inv (Multiplicative.toAdd m))
  right_inv := by
    intro f
    funext x
    change Multiplicative.ofAdd
        (e (e.symm (fun y : G => Multiplicative.toAdd (f y))) x) =
      Multiplicative.ofAdd (Multiplicative.toAdd (f x))
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun q : G → D => q x)
        (e.right_inv (fun y : G => Multiplicative.toAdd (f y))))
  map_mul' := by
    intro m n
    funext x
    change Multiplicative.ofAdd (e (Multiplicative.toAdd (m * n)) x) =
      Multiplicative.ofAdd
        (e (Multiplicative.toAdd m) x + e (Multiplicative.toAdd n) x)
    rw [show Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n from rfl]
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun q : G → D => q x)
        (e.map_add (Multiplicative.toAdd m) (Multiplicative.toAdd n)))

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
