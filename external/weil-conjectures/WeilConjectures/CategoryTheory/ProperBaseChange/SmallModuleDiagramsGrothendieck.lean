/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Small diagrams of module sheaves form a Grothendieck category

Source: Stacks Project, Injectives, Tags 05AB, 079B and 079Q; extension to small diagrams
(blueprint: lem-weil-pbc-small-module-diagrams-grothendieck).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

/-- Small diagrams of left module sheaves over an arbitrary ring sheaf are Grothendieck abelian.
Source: Stacks Project, Injectives, Tags 05AB, 079B and 079Q, with the small-diagram extension
(blueprint: lem-weil-pbc-small-module-diagrams-grothendieck).

Proof plan:
1. By `lem-weil-pbc-ring-sheaves-grothendieck`, module sheaves are abelian, have small
colimits and exact filtered colimits, and have a generator `G`.
2. By `lem-weil-pbc-functor-abelian-colimits`, the functor category is abelian and has
small colimits, computed pointwise.
3. By `lem-weil-pbc-functor-exact-colimits`, filtered colimits in the functor category
preserve finite limits, since this holds in module sheaves.
4. By `lem-weil-pbc-evaluation-free-diagram-adjunction`, evaluation at each `j` has a
left adjoint `L_j`, whose value at `k` is the coproduct indexed by morphisms `j ⟶ k`.
Form the small coproduct `H` of all `L_j(G)`.
5. Distinct natural transformations differ at some `j`. The generator `G` detects this
difference; the evaluation adjunction gives a detecting map from `L_j(G)`. Extend it to
`H` by zero on the other summands. Thus `H` is a generator. For an empty diagram category,
all parallel morphisms agree, so the empty coproduct is a generator vacuously.
6. Abelianness, small colimits, exact filtered colimits and a generator give exactly
`def-sp-grothendieck-abelian`. -/
theorem smallModuleDiagrams_isGrothendieckAbelian
    {C : Type u} [SmallCategory C] (τ : GrothendieckTopology C)
    (R : Sheaf τ RingCat.{u}) (J : Type u) [SmallCategory J] :
    IsGrothendieckAbelian.{u} (J ⥤ ringedSiteModules.{u} R) := by
  let : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
    SheafOfModules.isGrothendieckAbelian R
  let G := separator (ringedSiteModules.{u} R)
  have hG := isSeparator_separator (ringedSiteModules.{u} R)
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : J ↦ (evaluationLeftAdjoint (ringedSiteModules.{u} R) j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight (ringedSiteModules.{u} R) j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (J ⥤ ringedSiteModules.{u} R) :=
    ⟨_, hS.isSeparator_coproduct⟩
  let : Limits.HasFilteredColimitsOfSize.{u, u} (J ⥤ ringedSiteModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u, u} (J ⥤ ringedSiteModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

end CategoryTheory
