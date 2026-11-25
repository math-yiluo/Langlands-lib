/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Blueprint statements

def-weil-pbc-constructible-complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A sheaf `F` of `Λ`-modules on the small étale site of `T`, for a finite ring `Λ`, is
constructible if there is a stratification of `T` such that on each stratum the pullback of
`F` is, locally on an étale cover, isomorphic to the constant sheaf on a finite `Λ`-module.

This is `Scheme.IsConstructibleSheaf` for `A = ModuleCat Λ`, phrased with explicit finite
constant values instead of finitely generated stalks; the two agree by
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`. Used for
def-weil-pbc-constructible-complexes. -/
def IsConstructibleEtaleModuleSheaf {T : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] [Finite Λ] (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ S : Stratification T, ∀ k : Fin S.n,
    let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F
    ∃ d : LocallyConstantDatum G, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            ((S.domain k).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M)

end AlgebraicGeometry.Scheme
