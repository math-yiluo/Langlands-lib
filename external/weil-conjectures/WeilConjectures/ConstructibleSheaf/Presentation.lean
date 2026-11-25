/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs

/-!
# Constructible sheaves are quotients of sums of `j_{V!} Λ_V`

On a quasi-compact quasi-separated scheme `X` and for a commutative ring `Λ`, every
constructible sheaf of `Λ`-modules on `X_ét` is a quotient of a finite coproduct `∐ j_{V!} Λ_V`
of extensions by zero of constant sheaves along étale maps `j_V : V ⟶ X` from affine schemes
[Stacks 095M; SGA 4½, Rapport, 4.6].

## Main statements

- `AlgebraicGeometry.Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]

/-- **Constructible sheaves are quotients of sums of `j_{V!} Λ_V`** [Stacks 095M; SGA 4½,
Rapport, 4.6]. This is an input to blueprint `lemma-flat-models-generators`.

On a quasi-compact quasi-separated scheme `X`, every constructible sheaf `F` of `Λ`-modules on
`X_ét` is a quotient of a finite coproduct `∐ j_{V!} Λ_V`, with `j_V : V ⟶ X` étale and `V`
affine. Here `j_{V!}` is the extension by zero along the étale map `j_V`, the left adjoint
`AlgebraicGeometry.Etale.etaleLowerShriek` of `j_V^*`; `j_{V!} Λ_V` is the free sheaf on the
étale `X`-scheme `V` (`AlgebraicGeometry.Scheme.free_etale_module_shriek_comparison`), so it is
flat, and it is constructible (Stacks 03SA,
`AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerShriekUnit_of_isAffine_source`).

This is `AlgebraicGeometry.Etale.exists_epi_sigma_lowerShriekUnit`. -/
@[stacks 095M]
theorem exists_epi_sigma_lowerShriek_constantSheaf [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (j : ∀ i, V i ⟶ X) (hj : ∀ i, Etale (j i)),
      (∀ i, IsAffine (V i)) ∧
      ∃ φ : (∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (j i) (hj i)).obj
          ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ⟶ F, Epi φ := by
  obtain ⟨n, V, j, hj, hV, φ, hφ⟩ := Etale.exists_epi_sigma_lowerShriekUnit (Λ := Λ) F
  exact ⟨n, V, j, hj, hV, φ, hφ⟩

end AlgebraicGeometry.Scheme
