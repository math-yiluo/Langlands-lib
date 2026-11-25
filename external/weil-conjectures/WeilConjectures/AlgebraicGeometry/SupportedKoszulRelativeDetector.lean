/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffine
import WeilConjectures.AlgebraicGeometry.SupportedOpenExtension
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import Mathlib.CategoryTheory.Localization.LocallySmall
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.SupportedDerivedRestrictionZero
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # A supported Koszul relative detector

Source: Stacks Project, Tag 0A9A, induction step.
(blueprint: lem-pc-supported-koszul-relative-detector).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem open_scheme_derived_localization (X : Scheme.{u}) (V : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))] :
    Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))) := by
  let D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)
  let := HasDerivedCategory.standard D
  let e := CategoryTheory.Equivalence.symm
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (D := D) (Scheme.Modules.overEquiv V)
  let : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let F := e.mapDerivedCategory.functor
  let : LocallySmall.{w} (DerivedCategory D) := locallySmall_of_faithful F
  exact ⟨MorphismProperty.hasLocalizationOfLocallySmall.{w}
    (HomologicalComplex.quasiIso D (.up ℤ)) DerivedCategory.Q⟩

private noncomputable def open_homology_stalk_iso
    (X : Scheme.{u}) (V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X) (n : ℤ) (x : V.toScheme) :
    TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) n).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj K)).val.presheaf x ≅
      TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x.val := by
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
  let F := schemeOpenRestriction X V
  let H := Scheme.Modules.toPresheaf V.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  exact H.mapIso ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app K ≪≫
    (Scheme.Modules.overFunctorEquiv V).app M) ≪≫
      (Scheme.Modules.restrictStalkNatIso V.ι x).app M

private theorem stalk_subsingleton_of_restriction_zero
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedCategory X)
    (hz : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K))
    (n : ℤ) (x : X) (hx : x ∈ U) :
    Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x)) := by
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have hzM : IsZero (R.obj M) :=
    ((DerivedCategory.homologyFunctor _ n).map_isZero hz).of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso n).app K)
  let e := CategoryTheory.Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor _ (⟨x, hx⟩ : U.toScheme)
  let : e.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let : (Scheme.Modules.toPresheaf U.toScheme).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hzG := H.map_isZero (e.map_isZero hzM)
  let i := H.mapIso ((Scheme.Modules.overFunctorEquiv U).app M) ≪≫
    (Scheme.Modules.restrictStalkNatIso U.ι ⟨x, hx⟩).app M
  exact AddCommGrpCat.subsingleton_of_isZero (hzG.of_iso i.symm)

/-- The Koszul object on the affine complement detects supported objects zero on U.
Source: Stacks Project, Tag 0A9A, affine and supported Koszul construction paragraphs.
(blueprint: lem-pc-supported-koszul-relative-detector).

Proof: Put S = T intersect (X minus U), closed in X and contained in V. Its complement
in V is W = (U intersect V) union (V minus T), quasi-compact by quasi-separatedness,
compactness of U, and compactness of X minus T. Apply the already stated affine
supported perfect detector on V with support S to obtain B, perfect and quasi-coherent.
Its extension by zero A
is isomorphic to derived open pushforward, hence perfect and supported on S by supported
open pushforward. Quasi-compactness of the affine inclusion and quasi-separatedness
of X make its direct image preserve quasi-coherent cohomology. Restriction of A to U
is zero because S is disjoint from U. For C supported on T with C restricted to U zero,
its cohomology on V is supported on S. Exact extension-by-zero adjunction transfers
orthogonality to all shifts of A to orthogonality of C restricted to V to all shifts
of B. The affine Koszul detector therefore makes C restricted to V zero. Since C is
zero on U already, stalkwise homology detection on the cover U,V makes C zero globally.
If U is top take the zero Koszul object; if U is empty this is affine detection.
If T is empty, every supported object is already zero. No right adjoint is used here. -/
theorem exists_supported_koszul_relative_detector
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (V : X.affineOpens) (hU : IsCompact (U : Set X))
    (hcover : U ⊔ (V : X.Opens) = ⊤) :
    ∃ A : schemeDerivedQCohCategory X, Scheme.IsPerfect X A.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj A.obj).val.presheaf x))) ∧
      IsZero ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj A.obj) ∧
      ∀ C : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj C.obj).val.presheaf x))) →
        IsZero ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj C.obj) →
        (∀ n : ℤ, Subsingleton (A.obj⟦n⟧ ⟶ C.obj)) → IsZero C.obj := by
  classical
  let S : Set X := T ∩ (U : Set X)ᶜ
  have hS : IsClosed S := hT.inter U.isOpen.isClosed_compl
  have hSV : S ⊆ (V : X.Opens) := by
    intro x hx
    have hxcover : x ∈ U ⊔ (V : X.Opens) := by rw [hcover]; trivial
    exact hxcover.resolve_left hx.2
  obtain ⟨hD⟩ := open_scheme_derived_localization X (V : X.Opens)
  let := hD
  obtain ⟨hO⟩ := nonempty_derivedOpenLocalization (V : X.Opens).toScheme
  let := hO
  let Y := (V : X.Opens).toScheme
  let : IsAffine Y := V.property
  let : QuasiSeparatedSpace Y :=
    (V : X.Opens).isOpenEmbedding.quasiSeparatedSpace
  let S' : Set Y := Subtype.val ⁻¹' S
  have hS' : IsClosed S' := hS.preimage continuous_subtype_val
  have hSc' : IsCompact S'ᶜ := by
    have hUV := QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X)
      U.isOpen hU V.1.isOpen V.2.isCompact
    have hTV := QuasiSeparatedSpace.inter_isCompact Tᶜ (V : Set X)
      hT.isOpen_compl hTc V.1.isOpen V.2.isCompact
    apply (V : X.Opens).isOpenEmbedding.isEmbedding.isCompact_iff.mpr
    change IsCompact (Subtype.val '' S'ᶜ)
    have heq : Subtype.val '' S'ᶜ =
        (Tᶜ ∩ (V : Set X)) ∪ ((U : Set X) ∩ (V : Set X)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases ht : y.val ∈ T
        · exact Or.inr ⟨not_not.mp (fun hu ↦ hy ⟨ht, hu⟩), y.property⟩
        · exact Or.inl ⟨ht, y.property⟩
      · rintro (⟨ht, hv⟩ | ⟨hu, hv⟩)
        · exact ⟨⟨x, hv⟩, fun h ↦ ht h.1, rfl⟩
        · exact ⟨⟨x, hv⟩, fun h ↦ h.2 hu, rfl⟩
    rw [heq]
    exact hTV.union hUV
  let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  obtain ⟨B, hB, hsB, hdetect⟩ := supported_perfect_detector_affine Y {W}
    (by simp [W]) (by simp) S' hS' hSc'
  obtain ⟨A, hA, hsA, hhom⟩ := supported_open_extension X V S hS hSV B hB hsB
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro n x hx
    exact hsA n x (fun h ↦ hx h.1)
  · exact supported_derived_restriction_zero X S U (by
      intro x hx h
      exact h.2 hx) A.obj hsA
  · intro C hsC hzU horth
    have hqC : schemeDerivedQCohProperty Y
        ((schemeOpenRestriction X (V : X.Opens)).mapDerivedCategory.obj C.obj) := by
      apply (schemeDerivedQCoh_openRestriction_iff X (V : X.Opens) C.obj).2
      intro n
      let := C.property n
      exact SheafOfModules.isQuasicoherent_over
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj C.obj) (V : X.Opens)
    let CV : schemeDerivedQCohCategory Y :=
      ⟨(schemeOpenRestriction X (V : X.Opens)).mapDerivedCategory.obj C.obj, hqC⟩
    have hsCV : ∀ (n : ℤ) (x : Y), x ∉ S' →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj CV.obj).val.presheaf x)) := by
      intro n x hx
      let i := open_homology_stalk_iso X (V : X.Opens) C.obj n x
      have hs : Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj C.obj).val.presheaf
            x.val)) := by
        by_cases ht : x.val ∈ T
        · have hu : x.val ∈ U := not_not.mp (fun hu ↦ hx ⟨ht, hu⟩)
          exact stalk_subsingleton_of_restriction_zero X U C.obj hzU n x.val hu
        · exact hsC n x.val ht
      exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr hs
    have hzV : IsZero CV.obj := hdetect CV hsCV (fun n ↦
      (hhom C.obj n).some.subsingleton_congr.mp (horth n))
    have hzV' : IsZero ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (V : X.Opens)).mapDerivedCategory.obj C.obj) := by
      let E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (V : X.Opens)) ≌
          SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
        Scheme.Modules.overEquiv (V : X.Opens)
      let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
      let : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
      let e := E.mapDerivedCategory
      have hz : IsZero (e.functor.obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) (V : X.Opens)).mapDerivedCategory.obj C.obj)) :=
        hzV.of_iso ((Functor.mapDerivedCategoryCompIso _ _).app C.obj)
      apply (IsZero.iff_id_eq_zero _).mpr
      apply e.functor.map_injective
      exact hz.eq_of_src _ _
    have hi : IsIso (0 : C.obj ⟶ C.obj) :=
      Scheme.derived_restriction_isIso_open_cover X U (V : X.Opens) hcover 0
        (IsZero.isIso hzU hzU _) (IsZero.isIso hzV' hzV' _)
    apply (IsZero.iff_id_eq_zero _).mpr
    have h := IsIso.hom_inv_id (0 : C.obj ⟶ C.obj)
    rw [zero_comp] at h
    exact h.symm

end AlgebraicGeometry
