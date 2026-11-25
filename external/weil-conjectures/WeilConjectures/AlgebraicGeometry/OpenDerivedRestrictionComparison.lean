/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero

/-! # Comparison of the two derived restrictions to an open subscheme

Source: Stacks Project, Tags 079W and 0A9A.
(blueprint: lem-pc-open-derived-restriction-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exact open restriction, expressed on the localized site or on the open subscheme,
identifies quasi-coherent cohomology, support, shifted orthogonality and zero objects.
Source: Stacks Project, Tag 079W, Lemma cohomology-lemma-adjoint, and Tag 0A9A,
Lemma perfect-lemma-supported-generator, induction paragraph.
(blueprint: lem-pc-open-derived-restriction-comparison).

Proof: Obtain the localizations from `nonempty_hasDerivedCategory_openSubscheme` and
`nonempty_derivedOpenLocalization`, and the adjunction from
`open_derived_localization_adjunction`. Let e be the exact canonical module equivalence
`Modules.overEquiv U`. The composition isomorphism identifies M with L followed by the derived
equivalence D(e). The existing quasi-coherent restriction criterion and quasi-coherence of
restriction prove the first clause in each degree. Exactness identifies homology
with restriction of homology; the restriction stalk isomorphism identifies the
stalk at x with the original stalk at x.val. Transporting zero additive groups
along this isomorphism proves support. Full faithfulness of D(e) and the canonical
shift isomorphism identify the Hom types in the orthogonality clause, and full
faithfulness also reflects zero objects. None of these arguments requires
compactness, a closed support, or a detector. For the empty open the module
categories are zero categories, so the same comparisons apply. -/
theorem open_derived_restriction_comparison
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
    letI := hD
    ∃ hO : ∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W)),
    letI := hO
    let L := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let M := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)).mapDerivedCategory
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X) (_ : L ⊣ R),
      (∀ K : schemeDerivedCategory X, schemeDerivedQCohProperty X K →
        schemeDerivedQCohProperty U.toScheme (M.obj K)) ∧
      (∀ (T : Set X) (K : schemeDerivedCategory X),
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) →
        ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj
              (M.obj K)).val.presheaf x))) ∧
      (∀ (Q K : schemeDerivedCategory X) (n : ℤ),
        Subsingleton (L.obj (Q⟦n⟧) ⟶ L.obj K) →
        Subsingleton ((M.obj Q)⟦n⟧ ⟶ M.obj K)) ∧
      (∀ K : schemeDerivedCategory X, IsZero (M.obj K) → IsZero (L.obj K)) := by
  obtain ⟨hD⟩ := nonempty_hasDerivedCategory_openSubscheme.{u, w} X U
  let := hD
  obtain ⟨R, ⟨adj⟩⟩ := open_derived_localization_adjunction X U
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  -- Reuse exactness instances across the derived functors and their comparison maps.
  have : PreservesFiniteLimits r := inferInstance
  have : PreservesFiniteColimits r := inferInstance
  have : r.Additive := Functor.additive_of_preserves_binary_products r
  have : e.IsEquivalence := inferInstance
  have : PreservesFiniteLimits e := inferInstance
  have : PreservesFiniteColimits e := inferInstance
  have : e.Additive := Functor.additive_of_preserves_binary_products e
  let F := r ⋙ e
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits r e
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits r e
  have : F.Additive := inferInstance
  let M := F.mapDerivedCategory
  let L := r.mapDerivedCategory
  let c : M ≅ L ⋙ e.mapDerivedCategory := (Functor.mapDerivedCategoryCompIso r e).symm
  refine ⟨hD, (nonempty_derivedOpenLocalization.{u, w} U.toScheme).some, R, adj,
    ?_, ?_, ?_, ?_⟩
  · intro K hK
    apply (schemeDerivedQCoh_openRestriction_iff X U K).mpr
    intro n
    have := hK n
    exact SheafOfModules.isQuasicoherent_over _ U
  · intro T K hK n x hx
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n
    let HU := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n
    let d : HU.obj (M.obj K) ≅ (Scheme.Modules.restrictFunctor U.ι).obj (H.obj K) :=
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm ≪≫
        (Scheme.Modules.overFunctorEquiv U).app (H.obj K)
    let st := SheafOfModules.toSheaf.{u} (moduleRings U.toScheme.toRingedSpace) ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} U.toScheme.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let dS := st.mapIso d ≪≫ (Scheme.Modules.restrictStalkNatIso U.ι x).app (H.obj K)
    have hS : IsZero (TopCat.Presheaf.stalk (H.obj K).val.presheaf x.val) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr (hK n x.val hx)
    exact AddCommGrpCat.subsingleton_of_isZero (hS.of_iso dS)
  · intro Q K n h
    let a : M.obj (Q⟦n⟧) ≅ (M.obj Q)⟦n⟧ := M.commShiftIso n |>.app Q
    have hc : Subsingleton (M.obj (Q⟦n⟧) ⟶ M.obj K) := by
      apply Equiv.subsingleton_congr
        (Iso.homCongr (c.app (Q⟦n⟧)) (c.app K)) |>.mpr
      have he : e.mapDerivedCategory.FullyFaithful := .ofFullyFaithful _
      exact Equiv.subsingleton_congr he.homEquiv |>.mp h
    exact Equiv.subsingleton_congr (Iso.homCongr a (Iso.refl _)) |>.mp hc
  · intro K hK
    have hE : IsZero (e.mapDerivedCategory.obj (L.obj K)) :=
      hK.of_iso (c.app K).symm
    exact IsZero.of_full_of_faithful_of_isZero e.mapDerivedCategory (L.obj K) hE

end AlgebraicGeometry
