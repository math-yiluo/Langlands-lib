/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GmHigherVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.AlgebraicGeometry.Sites.GmTransport
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# The cohomology of `𝔾ₘ` on a smooth curve

Let `C` be a smooth separated curve of finite type over an algebraically closed field `k`. Then

`H¹(C, 𝔾ₘ) = Pic(C)`, `Hᵠ(C, 𝔾ₘ) = 0` for `q ≥ 2`,

both on the small étale site and, for the classical multiplicative sheaf `ν^* 𝔾ₘ`, on the small
pro-étale site. In particular the Brauer group of `C` vanishes. The identification in degree
one is natural under pullback, for instance under restriction to open subschemes and under
extension of the algebraically closed ground field.

## Main statements

- `AlgebraicGeometry.IsCurve.sheafH_gmSheaf_of_smooth`: the étale statement.
- `AlgebraicGeometry.IsCurve.rightDerived_globalSections_comparisonUpperStar_gmSheaf`: the
  pro-étale statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- Blueprint `lemma-cohomology-multiplicative-group`: the cohomology of `𝔾ₘ` on a smooth curve,
étale version.

Let `C` be a smooth separated curve of finite type over an algebraically closed field `k`. Then
the canonical map `Pic(C) → H¹(C_ét, 𝔾ₘ)`, `L ↦ [Isom(𝒪_C, L)]`
(`AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroupAddEquiv`), is an isomorphism of
groups, and `Hᵠ(C_ét, 𝔾ₘ) = 0` for `q ≥ 2`; in particular `Br(C) = 0`. The identification in
degree one is natural under restriction to open subschemes `U ⊆ C`, and more generally under
pullback along any morphism `h : X ⟶ C`, for instance the projection `C_{k'} ⟶ C` for an
extension `k ⊆ k'` of algebraically closed fields (in degrees `q ≥ 2` both sides vanish).

The vanishing is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_gmSheaf_of_smooth` (blueprint
`lemma-cohomology-multiplicative-group--2`), the identification in degree one is Hilbert 90
(blueprint `lemma-cohomology-multiplicative-group--3`) and its naturality is
`AlgebraicGeometry.Scheme.etaleRestrictionH_toCohomologicalPicardGroup` and
`AlgebraicGeometry.Scheme.gmCohomologyMap_toCohomologicalPicardGroup`. -/
theorem sheafH_gmSheaf_of_smooth (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f] :
    (∀ L : C.Pic, Scheme.Pic.toCohomologicalPicardGroupAddEquiv C (.ofMul L) =
        Scheme.Pic.toCohomologicalPicardGroup C L) ∧
      (∀ (U : C.Opens) (L : C.Pic),
        Scheme.etaleRestrictionH U.ι C.gmSheaf 1 (Scheme.Pic.toCohomologicalPicardGroup C L) =
          Scheme.Pic.toCohomologicalPicardGroup U (Scheme.Pic.map U.ι L)) ∧
      (∀ {X : Scheme.{u}} (h : X ⟶ C) (L : C.Pic),
        Scheme.gmCohomologyMap h 1 (Scheme.Pic.toCohomologicalPicardGroup C L) =
          Scheme.Pic.toCohomologicalPicardGroup X (Scheme.Pic.map h L)) ∧
      ∀ q : ℕ, 2 ≤ q → Subsingleton (Sheaf.H C.gmSheaf q) :=
  ⟨fun _ ↦ rfl, fun U L ↦ Scheme.etaleRestrictionH_toCohomologicalPicardGroup U.ι L,
    fun h L ↦ Scheme.gmCohomologyMap_toCohomologicalPicardGroup h L,
    subsingleton_sheafH_gmSheaf_of_smooth f⟩

/-- The `q`-th right derived functor of the global sections of the small étale site of a scheme
`X`, evaluated at `F`, is `Hᵠ(X_ét, F)`. -/
lemma nonempty_rightDerived_sectionsFunctor_iso_sheafH (X : Scheme.{u}) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (((Etale.sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived q).obj F ≅
      AddCommGrpCat.of (Sheaf.H F q)) :=
  Sheaf.nonempty_rightDerived_sections_obj_iso_functorH X.smallEtaleTopology
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X) q F

/-- Blueprint `lemma-cohomology-multiplicative-group`: the cohomology of the classical
multiplicative sheaf on a smooth curve, pro-étale version.

Let `C` be a smooth separated curve of finite type over an algebraically closed field `k` and
`𝒢ₘ^cl = ν^* 𝔾ₘ` the classical multiplicative sheaf on the small pro-étale site of `C`. Then
`H¹(C_proét, 𝒢ₘ^cl) ≅ Pic(C)` and `Hᵠ(C_proét, 𝒢ₘ^cl) = 0` for `q ≥ 2`: the comparison
`RΓ(C_proét, ν^* F) ≅ RΓ(C_ét, F)`
(`ProEtale.rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso`)
transports `AlgebraicGeometry.IsCurve.sheafH_gmSheaf_of_smooth`. -/
theorem rightDerived_globalSections_comparisonUpperStar_gmSheaf (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] :
    Nonempty (((ProEtale.globalSectionsFunctor AddCommGrpCat.{u + 1} C).rightDerived 1).obj
        ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} C).obj C.gmSheaf) ≅
          AddCommGrpCat.of (Additive C.Pic)) ∧
      ∀ q : ℕ, 2 ≤ q →
        IsZero (((ProEtale.globalSectionsFunctor AddCommGrpCat.{u + 1} C).rightDerived q).obj
          ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} C).obj C.gmSheaf)) := by
  refine ⟨?_, fun q hq ↦ ?_⟩
  · let e₁ := ProEtale.rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ C
      C.gmSheaf 1
    obtain ⟨e₂⟩ := nonempty_rightDerived_sectionsFunctor_iso_sheafH C 1 C.gmSheaf
    exact ⟨e₁ ≪≫ e₂ ≪≫
      (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm.toAddCommGrpIso⟩
  · let e₁ := ProEtale.rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ C
      C.gmSheaf q
    obtain ⟨e₂⟩ := nonempty_rightDerived_sectionsFunctor_iso_sheafH C q C.gmSheaf
    have := subsingleton_sheafH_gmSheaf_of_smooth f q hq
    exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso (e₁ ≪≫ e₂)

end AlgebraicGeometry.IsCurve
