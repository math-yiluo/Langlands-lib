/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence

/-!
# Realizing injective constant-coefficient sheaves as ringed-site modules

Source: Stacks Project, Modules on Sites, Sections 093I and 03CV;
Cohomology on Sites, Tags 03FC and 03FD.
(blueprint: lem-weil-pbc-injective-etale-constant-ring-module)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An injective sheaf of constant-coefficient modules has an injective ringed-site
module realization with the same underlying abelian presheaf.

Source: Stacks Project, Modules on Sites, Sections 093I and 03CV; Sites Example 0H7J;
Cohomology on Sites, Tags 03FC and 03FD. This is the constant-coefficient interface
in step 1 of lem-weil-pbc-injective-etale-module-cech-h1.
(blueprint: lem-weil-pbc-injective-etale-constant-ring-module)

Proof: Sheafify the constant presheaf of rings with value Λ to obtain R.
The underlying-set identification uses lem-weil-pbc-ring-sheafification-underlying-sets;
local representatives and local equality use lem-weil-pbc-site-sheafification-sections-local
(Stacks Sites 00YR and 00WK).
Every section of R is locally the image of a constant scalar. Given such a local representative a
and a section x of J, define a*x using the Λ-action after restriction. The local
sections agree on overlaps: equality of representatives in the sheafification is
local equality, and the restrictions of J are Λ-linear. The sheaf axiom glues these
sections uniquely. Refining representatives proves independence of the choice, the
module laws and compatibility with restriction. This makes J a sheaf M of R-modules
without changing its abelian presheaf. Conversely restrict any R-module along the
constant scalar map Λ → R. The same local description and uniqueness of gluing show
these operations are inverse on objects and on morphisms. Thus they give an equivalence
between Λ-module sheaves and R-module sheaves. Equivalences preserve monomorphisms
and transport extensions across monomorphisms, so injectivity of J implies injectivity
of M. The identity on local sections supplies the displayed presheaf isomorphism.
The argument also applies to Λ = 0 and the empty scheme: all relevant sections and
module laws are then forced, and no nonempty covering or nonzero scalar is assumed. -/
theorem exists_injective_etale_ring_module
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    ∃ (R : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (M : SheafOfModules.{u + 1} R), Injective M ∧
        Nonempty (M.val.presheaf ≅ J.obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  let F := etaleConstantModuleFunctor Y Λ
  let : F.IsEquivalence := etaleConstantModuleFunctor_isEquivalence Y Λ
  refine ⟨etaleConstantModuleRing Y Λ, F.obj J, ?_,
    ⟨etaleConstantModuleUnderlyingIso Y Λ J⟩⟩
  exact (F.asEquivalence.map_injective_iff J).mpr inferInstance

end AlgebraicGeometry.Scheme
