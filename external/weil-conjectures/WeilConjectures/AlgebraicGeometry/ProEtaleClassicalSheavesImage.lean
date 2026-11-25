/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections

/-! # The essential image of the comparison inverse image

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-thm-pe-classical-sheaves/sk-thm-pe-classical-sheaves-image.md`
(blueprint: det-pe-classical-sheaves-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] uliftCategory

private theorem relativeContinuity_of_classical (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (hF : AlgebraicGeometry.ProEtale.IsClassical F) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  constructor
  intro I _ _ K c hc
  let e := ULiftHomULiftCategory.equiv.{u + 1, u + 1, u, u} I
  let c' := (AffineProEt.toProEt X).mapCone c
  have hcOver : IsLimit ((ProEt.forget X).mapCone c') :=
    isLimitOfReflects (Over.forget X)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone c').symm)
  let P : AlgebraicGeometry.ProEtale.AffinePresentation X
      (ULiftHom.{u + 1} (ULift.{u + 1} I)) :=
    { diagram := e.inverse ⋙ (K ⋙ AffineEtale.toAffineProEt X) ⋙ AffineProEt.toProEt X
      affine := fun i ↦ inferInstanceAs
        (IsAffine ((AffineEtale.toAffineProEt X).obj (K.obj (e.inverse.obj i))).left)
      etale := fun i ↦ inferInstanceAs
        (Etale ((AffineEtale.toAffineProEt X).obj (K.obj (e.inverse.obj i))).hom)
      cone := c'.whisker e.inverse
      affineVertex := inferInstanceAs (IsAffine c.pt.left)
      isLimit := hcOver.whiskerEquivalence e.symm }
  have : IsIso (AlgebraicGeometry.ProEtale.continuityMap P F.obj) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (hF P)
  have hIso : IsIso ((colimit.isColimit _).desc
      (AlgebraicGeometry.ProEtale.sectionCocone P F.obj)) := by exact this
  have h : IsColimit (AlgebraicGeometry.ProEtale.sectionCocone P F.obj) :=
    IsColimit.ofPointIso (colimit.isColimit _)
  exact ⟨by exact h.whiskerEquivalence e.op⟩

/-- A pro-étale sheaf of sets is classical exactly when it comes from the étale site,
and exactly when the comparison counit is invertible.
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-thm-pe-classical-sheaves/sk-thm-pe-classical-sheaves-image.md`,
following Bhatt--Scholze, Lemma 5.1.2 (blueprint: theorem-classical-sheaves-essential-image--1).

Proof:
1. For (1) implies (2), choose an isomorphism from G to the inverse image of F.
   On every affine presentation, the scheme-general continuity theorem
   `theorem-classical-sheaves-essential-image--1` makes the canonical restriction
   cocone for the inverse image a colimit. Naturality of the chosen isomorphism
   identifies its continuity map with that of G, through the bijections on the
   limit object and on the colimit of stage sections. The inverse isomorphism
   induces the inverse colimit map. Thus every continuity map for G is bijective.
2. For (2) implies (3), `IsClassical` says that the specified restriction cocone
   on each affine etale presentation is a colimit. Apply
   `theorem-classical-sheaves-essential-image--1`: the section formula identifies
   the counit on such a limit object with exactly this restriction map, and
   affine ind-etale basis coverings detect isomorphisms of sheaves. This gives
   invertibility of the counit on the arbitrary scheme X.
3. For (3) implies (1), take F to be the direct image of G under the recorded
   comparison adjunction. The inverse of its invertible counit supplies the
   isomorphism from G to the inverse image of F. These three implications give
   the two displayed equivalences. -/
theorem proEtaleClassicalSheavesImage (X : Scheme.{u})
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
    ((∃ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Nonempty (G ≅
        (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj F)) ↔
      AlgebraicGeometry.ProEtale.IsClassical G) ∧
      (AlgebraicGeometry.ProEtale.IsClassical G ↔
        IsIso ((proEtaleSiteComparison X).counit.app G)) := by
  let L := Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)
  have hL (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
      AlgebraicGeometry.ProEtale.IsClassical (L.obj F) := by
    intro I _ _ P
    obtain ⟨h⟩ := AlgebraicGeometry.ProEtale.affinePresentation_sectionCocone_isColimit
      (L.obj F) (proEtaleComparisonSets_continuous X F) P
    have : IsIso (AlgebraicGeometry.ProEtale.continuityMap P (L.obj F).obj) := by
      change IsIso (((colimit.isColimit _).coconePointUniqueUpToIso h).hom)
      infer_instance
    exact (CategoryTheory.isIso_iff_bijective _).mp inferInstance
  have hCounit (hG : AlgebraicGeometry.ProEtale.IsClassical G) :
      IsIso ((proEtaleSiteComparison X).counit.app G) :=
    proEtaleComparisonCounitSets_isIso_of_continuous X G
      (relativeContinuity_of_classical X G hG)
  have hImage (h : IsIso ((proEtaleSiteComparison X).counit.app G)) :
      ∃ F : Sheaf X.smallEtaleTopology (Type (u + 1)), Nonempty (G ≅ L.obj F) := by
    exact ⟨_, ⟨(asIso ((proEtaleSiteComparison X).counit.app G)).symm⟩⟩
  have hClassical (h : ∃ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Nonempty (G ≅ L.obj F)) : AlgebraicGeometry.ProEtale.IsClassical G := by
    obtain ⟨F, ⟨e⟩⟩ := h
    exact (AlgebraicGeometry.ProEtale.isClassical_iso_iff e).mpr (hL F)
  exact ⟨⟨hClassical, fun h ↦ hImage (hCounit h)⟩,
    ⟨hCounit, fun h ↦ hClassical (hImage h)⟩⟩

end AlgebraicGeometry.Scheme
