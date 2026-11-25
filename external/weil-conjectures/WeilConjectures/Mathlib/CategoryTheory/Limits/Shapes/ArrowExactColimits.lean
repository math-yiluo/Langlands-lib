/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Comma

/-! # Kernels and cokernels commute with exact colimits
Source: blueprint proposition-ind-constructible-sheaves, final paragraph.
(blueprint: lem-sfb-arrow-exact-colimits) -/

@[expose] public section

set_option autoImplicit false

universe u v j h

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Kernels and cokernels of diagrams of arrows commute with exact colimits.
Source: blueprint sk-prop-ind-heart-kernels-cokernels.proof.md, final paragraph.
(blueprint: lem-sfb-arrow-exact-colimits)

Proof: write a diagram of arrows as a natural transformation between its source and
 target diagrams. Its pointwise kernel is a kernel in the functor category, by the
 pointwise limit universal property. Exactness of colimits says that the colimit
 functor preserves that kernel. The source and target colimit universal properties
 identify the colimit arrow, and the resulting kernel comparison is the canonical
 comparison on every leg. Thus ker maps any colimit cocone to a colimit cocone.
 For cokernels, the same argument uses the pointwise cokernel and the fact that
 colimits preserve colimits. No filteredness or smallness beyond existence and
 exactness of the specified colimits is needed. -/
theorem arrow_exact_colimits (M : Type u) [Category.{v} M] [Abelian M]
    (J : Type j) [Category.{h} J] [HasColimitsOfShape J M]
    [HasExactColimitsOfShape J M] :
    PreservesColimitsOfShape J (ker (C := M)) ∧
      PreservesColimitsOfShape J (coker (C := M)) := by
  classical
  constructor
  · constructor
    intro F
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    let c := colimit.cocone F
    let φ := whiskerLeft F (Arrow.leftToRight (C := M))
    let α := whiskerLeft F (ker.ι M)
    let s : KernelFork φ := KernelFork.ofι α (by
      ext j
      exact kernel.condition (F.obj j).hom)
    have hs : IsLimit s := evaluationJointlyReflectsLimits _ (fun j ↦
      (KernelFork.isLimitMapConeEquiv ..).2
        ((kernelIsKernel (F.obj j).hom).ofIsoLimit (Fork.ext (Iso.refl _))))
    let eL := (colimit.isColimit (F ⋙ Arrow.leftFunc)).coconePointUniqueUpToIso
      (isColimitOfPreserves Arrow.leftFunc (colimit.isColimit F))
    let eR := (colimit.isColimit (F ⋙ Arrow.rightFunc)).coconePointUniqueUpToIso
      (isColimitOfPreserves Arrow.rightFunc (colimit.isColimit F))
    have hw : eL.hom ≫ c.pt.hom = colim.map φ ≫ eR.hom := by
      apply colimit.hom_ext
      intro j
      have hL : colimit.ι (F ⋙ Arrow.leftFunc) j ≫ eL.hom = (c.ι.app j).left :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      have hR : colimit.ι (F ⋙ Arrow.rightFunc) j ≫ eR.hom = (c.ι.app j).right :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      rw [← Category.assoc, hL]
      rw [← Category.assoc, colimit.ι_map, Category.assoc, hR]
      exact (c.ι.app j).w
    let i : Arrow.mk (colim.map φ) ≅ Arrow.mk c.pt.hom := Arrow.isoMk eL eR hw
    let e := KernelFork.mapIsoOfIsLimit (kf' := KernelFork.ofι (kernel.ι c.pt.hom)
      (kernel.condition c.pt.hom)) (s.mapIsLimit hs colim)
      (kernelIsKernel c.pt.hom) i
    apply (colimit.isColimit (F ⋙ ker M)).ofIsoColimit
      (Cocone.ext (c' := (ker M).mapCocone c) e (fun j ↦ ?_))
    apply (cancel_mono (kernel.ι c.pt.hom)).1
    have he : e.hom ≫ kernel.ι c.pt.hom = colim.map α ≫ eL.hom :=
      KernelFork.mapOfIsLimit_ι (s.map colim) (kernelIsKernel c.pt.hom) i.hom
    simp only [Functor.mapCocone_ι_app, ker_map, kernel.lift_ι]
    change (colimit.ι (F ⋙ ker M) j ≫ e.hom) ≫ kernel.ι c.pt.hom =
      kernel.ι (F.obj j).hom ≫ (c.ι.app j).left
    rw [Category.assoc, he, ← Category.assoc, colimit.ι_map, Category.assoc]
    have hL : colimit.ι (F ⋙ Arrow.leftFunc) j ≫ eL.hom = (c.ι.app j).left :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
    rw [hL]
    rfl
  · constructor
    intro F
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    let c := colimit.cocone F
    let φ := whiskerLeft F (Arrow.leftToRight (C := M))
    let α := whiskerLeft F (coker.π M)
    let s : CokernelCofork φ := CokernelCofork.ofπ α (by
      ext j
      exact cokernel.condition (F.obj j).hom)
    have hs : IsColimit s := evaluationJointlyReflectsColimits _ (fun j ↦
      (CokernelCofork.isColimitMapCoconeEquiv ..).2
        ((cokernelIsCokernel (F.obj j).hom).ofIsoColimit (Cofork.ext (Iso.refl _))))
    let eL := (colimit.isColimit (F ⋙ Arrow.leftFunc)).coconePointUniqueUpToIso
      (isColimitOfPreserves Arrow.leftFunc (colimit.isColimit F))
    let eR := (colimit.isColimit (F ⋙ Arrow.rightFunc)).coconePointUniqueUpToIso
      (isColimitOfPreserves Arrow.rightFunc (colimit.isColimit F))
    have hw : eL.hom ≫ c.pt.hom = colim.map φ ≫ eR.hom := by
      apply colimit.hom_ext
      intro j
      have hL : colimit.ι (F ⋙ Arrow.leftFunc) j ≫ eL.hom = (c.ι.app j).left :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      have hR : colimit.ι (F ⋙ Arrow.rightFunc) j ≫ eR.hom = (c.ι.app j).right :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      rw [← Category.assoc, hL]
      rw [← Category.assoc, colimit.ι_map, Category.assoc, hR]
      exact (c.ι.app j).w
    let i : Arrow.mk (colim.map φ) ≅ Arrow.mk c.pt.hom := Arrow.isoMk eL eR hw
    let e := CokernelCofork.mapIsoOfIsColimit
      (cc' := CokernelCofork.ofπ (cokernel.π c.pt.hom) (cokernel.condition c.pt.hom))
      (s.mapIsColimit hs colim) (cokernelIsCokernel c.pt.hom) i
    apply (colimit.isColimit (F ⋙ coker M)).ofIsoColimit
      (Cocone.ext (c' := (coker M).mapCocone c) e (fun j ↦ ?_))
    apply (cancel_epi (cokernel.π (F.obj j).hom)).1
    have he : colim.map α ≫ e.hom = eR.hom ≫ cokernel.π c.pt.hom :=
      CokernelCofork.π_mapOfIsColimit (s.mapIsColimit hs colim)
        (CokernelCofork.ofπ (cokernel.π c.pt.hom) (cokernel.condition c.pt.hom))
        i.hom
    change cokernel.π (F.obj j).hom ≫ (colimit.ι (F ⋙ coker M) j ≫ e.hom) =
      cokernel.π (F.obj j).hom ≫ (coker M).map (c.ι.app j)
    rw [← Category.assoc]
    have hα : cokernel.π (F.obj j).hom ≫ colimit.ι (F ⋙ coker M) j =
        colimit.ι (F ⋙ Arrow.rightFunc) j ≫ colim.map α :=
      (colimit.ι_map α j).symm
    rw [hα, Category.assoc, he, ← Category.assoc]
    have hR : colimit.ι (F ⋙ Arrow.rightFunc) j ≫ eR.hom = (c.ι.app j).right :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
    rw [hR]
    simp [coker_map]

end CategoryTheory.Limits
