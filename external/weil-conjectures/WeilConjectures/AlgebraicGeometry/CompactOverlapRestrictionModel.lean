/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # A compact open model for transported overlap restriction

Source: Stacks Project, Tag 09IM, overlap setup; explicit open-range comparison.
(blueprint: lem-sc-compact-overlap-restriction-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Derived restriction transport elaborates across several chosen localizations.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Transported overlap restriction is ordinary compact-open restriction followed by
an equivalence. No perfect object or morphism lifting is asserted.
Source: Stacks Project, Tag 09IM, overlap setup. The comparison below is an explicit
construction from the exact restriction and equivalence APIs of Mathlib.
(blueprint: lem-sc-compact-overlap-restriction-model).

Proof: Take U to be the inverse image of W under V.ι. The compact-open intersection
criterion in a quasi-separated space makes W intersect V compact, since affine V is
compact. The open embedding V.ι identifies U with this intersection, so U is compact.
The induced inclusion U.toScheme to (W intersect V).toScheme is a scheme isomorphism.
Its exact module-sheaf equivalence transports the supplied derived localization on the
ambient overlap to one on U, in the same Hom universe w. Derive that equivalence to
obtain e. At the module-sheaf level, Modules.overMapCompOverEquiv identifies transported
restriction from V with restriction along the inclusion of the ambient overlap into V.
Factor this inclusion through U and the preceding scheme isomorphism; the restriction
composition isomorphism and Modules.overFunctorEquiv identify it with ordinary open
restriction followed by the equivalence. Derive this natural isomorphism using
mapDerivedCategoryCompIso and mapDerivedCategoryNatIso. This proves the displayed
comparison on every object and morphism. If the overlap is empty, the same empty-open
isomorphism and exact equivalence apply. -/
theorem exists_compact_overlap_restriction_model
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))] :
    ∃ U : V.toScheme.Opens, IsCompact (U : Set V.toScheme) ∧
      ∃ hD : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hD
      ∃ e : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory (W ⊓ V).toScheme,
        Nonempty ((schemeOpenRestriction V.toScheme U).mapDerivedCategory ⋙ e.functor ≅
          (schemeOpenOverlapRestriction X
            (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory) := by
  classical
  let i : W ⊓ V ⟶ V := homOfLE inf_le_right
  let f : (W ⊓ V).toScheme ⟶ V.toScheme := X.homOfLE inf_le_right
  let U := f.opensRange
  have hU : IsCompact (U : Set V.toScheme) := by
    rw [V.ι.isOpenEmbedding.isCompact_iff]
    have hu : (V.ι ''ᵁ U) = W ⊓ V := by
      dsimp [U, f]
      rw [Scheme.opensRange_homOfLE, Scheme.Hom.image_preimage_eq_opensRange_inf]
      simp only [Scheme.Opens.opensRange_ι, inf_eq_right.mpr inf_le_right]
    change IsCompact (V.ι ''ᵁ U : Set X)
    rw [hu]
    exact hW.inter_of_isOpen hV.isCompact W.isOpen V.isOpen
  let s := f.isoOpensRange
  let e₀ : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace) :=
    CategoryTheory.Equivalence.mk (Modules.restrictFunctor s.hom) (Modules.restrictFunctor s.inv)
      ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
        Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId).symm
      ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
        Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId)
  have hD : Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) := by
    let C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
    let : HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
    let ed := e₀.mapDerivedCategory
    let : LocallySmall.{w} (DerivedCategory C) :=
      (locallySmall_congr ed).mpr inferInstance
    exact ⟨(HomologicalComplex.quasiIso C (.up ℤ)).hasLocalizationOfLocallySmall
      DerivedCategory.Q⟩
  obtain ⟨hD⟩ := hD
  let := hD
  let e := e₀.mapDerivedCategory
  let theta : schemeOpenOverlapRestriction X i ≅ Modules.restrictFunctor f :=
    Functor.isoWhiskerLeft (Modules.overEquiv V).inverse
        (Modules.overMapCompOverEquiv i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Modules.overEquiv V).counitIso _ ≪≫
      Functor.leftUnitor _
  let rho : schemeOpenRestriction V.toScheme U ⋙ e₀.functor ≅
      schemeOpenOverlapRestriction X i :=
    Functor.isoWhiskerRight (Modules.overFunctorEquiv U) _ ≪≫
      (Modules.restrictFunctorComp s.hom U.ι).symm ≪≫
      Modules.restrictFunctorCongr f.isoOpensRange_hom_ι ≪≫ theta.symm
  refine ⟨U, hU, hD, e, ⟨?_⟩⟩
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso rho

end AlgebraicGeometry.Scheme
