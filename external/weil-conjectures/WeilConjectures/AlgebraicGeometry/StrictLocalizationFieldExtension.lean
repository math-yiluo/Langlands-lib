/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.Mathlib.CategoryTheory.Elements

/-!
# The strict localization does not see extensions of the separably closed field

Let `s : Spec Ω ⟶ S` be a geometric point (`Ω` separably closed) and `a : Spec Ω' ⟶ Spec Ω` an
extension of separably closed fields. Precomposition with `a` identifies the pointed étale
neighbourhoods of `s` and of `a ≫ s` (`AlgebraicGeometry.Scheme.isIso_pointSmallEtalePrecomp_hom`),
hence their limits: the strict localizations `S_(a ≫ s)` and `S_(s)` are isomorphic over `S`
(Stacks, Tag 03PN). This reduces statements about strict localizations at geometric points with
separably closed field to the case of an algebraically closed field (blueprint
`lemma-punctured-surface-punctured-curve--1`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_strictLocalization_iso_of_precomp`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **The strict localization at an enlarged geometric point.** For a geometric point
`s : Spec Ω ⟶ S` and an extension `a : Spec Ω' ⟶ Spec Ω` of separably closed fields, the
strict localizations of `S` at `a ≫ s` and at `s` are isomorphic over `S` (Stacks, Tag 03PN). -/
theorem exists_strictLocalization_iso_of_precomp {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω]
    [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω) ⟶ S)
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) :
    ∃ σ : strictLocalization (a ≫ s) ≅ strictLocalization s,
      σ.hom ≫ strictLocalizationToBase s = strictLocalizationToBase (a ≫ s) := by
  let E := NatIso.mapElements (asIso (pointSmallEtalePrecomp s a).hom)
  let e : E.functor ⋙ neighborhoodDiagram (a ≫ s) ≅ neighborhoodDiagram s := Iso.refl _
  have hc : IsLimit ((Cone.postcompose e.hom).obj
      ((strictLocalizationConeAll (a ≫ s)).whisker E.functor)) :=
    (IsLimit.postcomposeHomEquiv e _).symm
      ((Functor.Initial.isLimitWhiskerEquiv E.functor _).symm
        (isLimitStrictLocalizationConeAll (a ≫ s)))
  refine ⟨hc.conePointUniqueUpToIso (isLimitStrictLocalizationConeAll s), ?_⟩
  rw [strictLocalizationToBase, IsLimit.conePointUniqueUpToIso_hom_comp]
  simp [e, strictLocalizationToBase]
  rfl

end AlgebraicGeometry.Scheme
