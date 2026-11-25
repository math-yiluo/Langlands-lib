/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Topology.OpenModuleDerivedSections
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Detecting zero direct-image cohomology on the affine basis

Source: Stacks Project, Tag 08D5, proof of (2); Tag 079V, K-injective computation.
(blueprint: lem-pc-direct-image-homology-affine-detection).
-/

@[expose] public section

universe u wX wS wAb

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem homology_zero_of_affine_sections (S : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) (m : ℤ)
    (h : ∀ (U : S.Opens), IsAffineOpen U → IsZero
      ((((RingedSpace.openModuleSections S.toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology m)) : IsZero (K.homology m) := by
  let R := moduleRings S.toRingedSpace
  let F := SheafOfModules.toSheaf R
  let G := F ⋙ sheafToPresheaf (Opens.grothendieckTopology S)
    AddCommGrpCat.{u}
  let L := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let P := L.homology m
  have hP (U : S.Opens) (hU : IsAffineOpen U) : IsZero (P.obj (Opposite.op U)) := by
    let V := (evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
    have hz := h U hU
    exact hz.of_iso ((L.sc m).mapHomologyIso V).symm
  have hstalk (x : S) : IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj P) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    suffices hh : ∀ t : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj P, t = 0 from
      ⟨fun a b ↦ (hh a).trans (hh b).symm⟩
    intro t
    obtain ⟨U, hx, hU, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis S.isBasis_affineOpens P x t
    have hs := AddCommGrpCat.subsingleton_of_isZero (hP U hU)
    rw [show s = 0 from Subsingleton.elim _ _]
    exact map_zero _
  have hz (x : S) : IsZero
      ((F ⋙ sheafToPresheaf (Opens.grothendieckTopology S)
        AddCommGrpCat.{u} ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
          (K.homology m)) := by
    let V := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : PreservesFiniteLimits V := by
      unfold V TopCat.Presheaf.stalkFunctor
      have : PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
            (OpenNhds.inclusion x).op) := ⟨fun J _ _ ↦ inferInstance⟩
      exact comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits V := by
      unfold V TopCat.Presheaf.stalkFunctor
      have : PreservesFiniteColimits
          ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
            (OpenNhds.inclusion x).op) := ⟨fun J _ _ ↦ inferInstance⟩
      exact comp_preservesFiniteColimits _ _
    have : PreservesFiniteLimits (G ⋙ V) := by
      change PreservesFiniteLimits
        (F ⋙ (sheafToPresheaf _ _ ⋙ V))
      infer_instance
    have : PreservesFiniteColimits F := by dsimp [F]; infer_instance
    have : PreservesFiniteColimits
        (TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙ V) := by
      change PreservesFiniteColimits
        (TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      infer_instance
    have : PreservesFiniteColimits (G ⋙ V) := by
      change PreservesFiniteColimits
        (F ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} S.toTopCat ⋙ V))
      exact comp_preservesFiniteColimits _ _
    have hh := (hstalk x).of_iso ((L.sc m).mapHomologyIso V)
    exact hh.of_iso ((K.sc m).mapHomologyIso (G ⋙ V)).symm
  have hF : IsZero (F.obj (K.homology m)) :=
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2 hz
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  simpa using hF.eq_of_src (F.map (𝟙 (K.homology m))) (F.map 0)

/-- Vanishing of derived sections on every inverse image of an affine open detects
vanishing of the corresponding cohomology sheaf of derived direct image. No
quasi-coherence or support hypothesis on the derived object is required.
Source: Stacks Project, Tag 08D5, proof of (2); Tag 079V.
(blueprint: lem-pc-direct-image-homology-affine-detection).

Proof:
1. Represent E by a complex and take a K-injective resolution I. The unbounded
right derived functor of sections on any open V is computed by the complex of
sections I(V). Derived direct image is represented by the termwise direct image
f_*I, by its K-injective computation. Sections of f_*I on U are termwise I(f⁻¹U).
2. The hypothesis says the degree m cohomology of those complexes is zero on
all affine opens U. The cohomology sheaf H^m(f_*I) is the sheafification of the
presheaf U ↦ H^m(I(f⁻¹U)): module sheafification is exact, hence commutes with
kernels, images and their quotient in homology.
3. Affine opens are a basis, so a presheaf zero on every affine open has zero
sheafification: every germ has a representative on an affine neighborhood and
is therefore zero. All stalks of H^m(f_*I) vanish, hence the sheaf is zero.
Transport along the resolution comparison gives the conclusion. This argument
works in every integer degree, for unbounded E, and also for the empty scheme. -/
theorem isZero_schemeHigherDirectImage_of_affine_sections
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wAb} AddCommGrpCat.{u}]
    (f : X ⟶ S) (E : schemeDerivedCategory X) (m : ℤ)
    (h : ∀ (U : S.Opens), IsAffineOpen U → IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
        ((RingedSpace.openModuleDerivedSections X.toRingedSpace (f ⁻¹ᵁ U)).obj E))) :
    IsZero ((schemeHigherDirectImage f m).obj E) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective E
  let : I.IsKInjective := hI
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let K := (D.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hK : IsZero (K.homology m) := by
    apply homology_zero_of_affine_sections S K m
    intro U hU
    let F := RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ U)
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} m
    let c := F.rightDerivedFunctor.mapIso e ≪≫ F.rightDerivedFunctorObjQIso I
    have hz := (h U hU).of_iso
      (H.mapIso c ≪≫ (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} m).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm
    exact hz
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) m
  let c := D.rightDerivedFunctor.mapIso e ≪≫ D.rightDerivedFunctorObjQIso I
  exact hK.of_iso
    (H.mapIso c ≪≫ (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) m).app K)

end AlgebraicGeometry
