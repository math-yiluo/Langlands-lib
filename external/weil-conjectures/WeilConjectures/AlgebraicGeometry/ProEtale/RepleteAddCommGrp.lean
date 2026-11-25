/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-!
# Repleteness of the pro-étale topos for abelian sheaves

The pro-étale topos of a scheme `S` is replete (Bhatt–Scholze, Proposition 4.2.8), see
`WeilConjectures.AlgebraicGeometry.ProEtale.Replete` for sheaves of modules over a ring. This
file records the statement for abelian sheaves
(`AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat`): the projection
`lim Fₙ ⟶ F₀` of a tower of epimorphisms of abelian sheaves on the pro-étale site is an
epimorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- On the affine pro-étale site, the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of
abelian sheaves is an epimorphism. -/
lemma AffineProEt.epi_π_app_zero_of_epi_addCommGrpCat :
    EpiπAppZeroOfEpi (Sheaf (AffineProEt.topology S) AddCommGrpCat.{u + 1}) := by
  intro F c hc hF
  have h {M N : Sheaf (AffineProEt.topology S) AddCommGrpCat.{u + 1}} (φ : M ⟶ N) :
      Sheaf.IsLocallySurjective φ ↔ Epi φ :=
    Sheaf.isLocallySurjective_iff_epi' _ φ
  simp_rw [← h] at hF ⊢
  exact AffineProEt.isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF

/-- On the pro-étale site, the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of abelian
sheaves is an epimorphism, by transport from the affine pro-étale site. -/
lemma ProEt.epi_π_app_zero_of_epi_addCommGrpCat :
    EpiπAppZeroOfEpi (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) := by
  intro F c hc hF
  let e := (AffineProEt.toProEt S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (AffineProEt.topology S) (ProEt.topology S)
  apply e.epi_of_epi_map
  exact AffineProEt.epi_π_app_zero_of_epi_addCommGrpCat (F := F ⋙ e) (isLimitOfPreserves e hc)
    fun n ↦ e.map_epi _

end AlgebraicGeometry.Scheme
