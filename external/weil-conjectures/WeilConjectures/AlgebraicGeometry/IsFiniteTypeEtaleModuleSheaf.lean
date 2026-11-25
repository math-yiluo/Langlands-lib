/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-!
# Finite type sheaves of modules on the small etale site

Source: Stacks Project, Tags 03DE(4), 03DL(5), and 03DF
(blueprint: def-weil-pbc-etale-module-finite-type).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module-valued etale sheaf is of finite type if an etale covering makes it generated
by finitely many global sections. On the site localized at each cover member, this means
an epimorphism from the constant sheaf of a finite free module. The constant sheaf of
`Fin n → Λ` is the direct sum of `n` copies of the constant ring sheaf, and its morphisms
to the restriction correspond to `n` global sections by the constant-sheaf adjunction.
The terminal-object covering formulation is equivalent to the all-objects formulation
by base change of covers. No local constancy is required in this definition.
Source: Stacks Project, Tags 03DE(4), 03DL(5), and 03DF
(blueprint: def-weil-pbc-etale-module-finite-type). -/
def IsFiniteTypeEtaleModuleSheaf {Y : Scheme.{v}} {Λ : Type (v + 1)} [CommRing Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{v} etalePrecoverage Y, ∀ i : 𝒰.I₀, ∃ n : ℕ,
    ∃ π : (constantSheaf (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
      (ModuleCat.{v + 1} Λ)).obj (ModuleCat.of Λ (Fin n → Λ)) ⟶
        F.over (𝒰.etalePrecoverageToEtale i), Epi π

end AlgebraicGeometry.Scheme
