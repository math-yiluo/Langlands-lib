/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-!
# Repleteness of the pro-étale topos for abelian sheaves

The abelian-sheaf version of `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`, which treats
sheaves of modules: on the pro-étale site of a scheme, the projection `lim Fₙ ⟶ F₀` of a tower of
epimorphisms of abelian sheaves is an epimorphism
(`AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_ab`), and countable products of abelian
sheaves are exact (`AlgebraicGeometry.Scheme.ProEt.countableAB4Star_ab`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- On the affine pro-étale site, the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of
abelian sheaves is an epimorphism. -/
lemma epi_π_app_zero_of_epi_ab : EpiπAppZeroOfEpi (Sheaf (topology S) Ab.{u + 1}) := by
  intro F c hc hF
  have h {M N : Sheaf (topology S) Ab.{u + 1}} (φ : M ⟶ N) :
      Sheaf.IsLocallySurjective φ ↔ Epi φ :=
    Sheaf.isLocallySurjective_iff_epi' _ φ
  simp_rw [← h] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- On the pro-étale site, the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of abelian
sheaves is an epimorphism (repleteness of the pro-étale topos, Bhatt–Scholze, Proposition 3.1.10
and 4.2.8), transported from the affine pro-étale site. -/
lemma epi_π_app_zero_of_epi_ab : EpiπAppZeroOfEpi (Sheaf (topology S) Ab.{u + 1}) := by
  intro F c hc hF
  let e := (AffineProEt.toProEt S).sheafPushforwardContinuous Ab.{u + 1}
    (AffineProEt.topology S) (topology S)
  have : HasLimitsOfSize.{u, u + 1} Ab.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  apply e.epi_of_epi_map
  exact AffineProEt.epi_π_app_zero_of_epi_ab (F := F ⋙ e) (isLimitOfPreserves e hc)
    fun n ↦ e.map_epi _

/-- **Repleteness of the pro-étale topos** for abelian sheaves: countable products are exact. -/
instance countableAB4Star_ab : CountableAB4Star (Sheaf (topology S) Ab.{u + 1}) :=
  .of_epi_π_app_zero epi_π_app_zero_of_epi_ab

end AlgebraicGeometry.Scheme.ProEt
