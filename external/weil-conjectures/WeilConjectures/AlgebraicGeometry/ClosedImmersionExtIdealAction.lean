/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.AlgebraicGeometry.HomComplexSingle
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The immersion ideal annihilates scalar Ext

Source: Stacks Project, Duality for Schemes, Tag 0BQZ, and the internal Hom
algebra action in Section 48.11, Tag 0BUZ.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem idealAction_zero_of_sections {Y : Scheme.{u}}
    (J : Y.IdealSheafData) (F : Y.Modules)
    (hF : ∀ (V : Y.Opens) (a : Γ(Y, V)), a ∈ J.idealOfOpens V →
      ∀ s : Γ(F, V), a • s = 0) :
    J.toModulesι ▷ F ≫ (λ_ F).hom = 0 := by
  open Scheme.Modules in
    let μ : J.toModules ⊗ F ⟶ F := J.toModulesι ▷ F ≫ (λ_ F).hom
    let adj := sheafificationAdjunction Y
    apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification J.toModules F).inv).mp
    apply (adj.homEquiv (J.toModules.val ⊗ F.val) F).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply PresheafOfModules.hom_ext
    intro U
    ext t
    change μ.val.app U
      ((SheafOfModules.tensorObjIsoSheafification J.toModules F).inv.val.app U
        (((adj.unit.app (J.toModules.val ⊗ F.val)).app U) t)) = _
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [map_add, ht, hs]
    | tmul a s =>
      change μ.app U.unop (tmulSection a s) = 0
      dsimp only [μ]
      rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
      erw [leftUnitor_hom_app_tmulSection']
      exact hF U.unop (J.toModulesι.app U.unop a)
        ((J.range_toModulesι_app_eq_idealOfOpens U.unop).subset ⟨a, rfl⟩) s

set_option backward.isDefEq.respectTransparency false in
private theorem idealAction_zero_of_iso {Y : Scheme.{u}}
    (J : Y.IdealSheafData) {F G : Y.Modules} (e : F ≅ G)
    (hG : J.toModulesι ▷ G ≫ (λ_ G).hom = 0) :
    J.toModulesι ▷ F ≫ (λ_ F).hom = 0 := by
  apply (cancel_mono e.hom).mp
  rw [zero_comp, Category.assoc, ← leftUnitor_naturality]
  erw [← whisker_exchange_assoc]
  erw [hG]
  exact comp_zero


/-- Every scalar Ext sheaf from the pushed-forward structure sheaf is annihilated
by the closed-immersion ideal, without regularity or finite-presentation assumptions.

Source: Stacks Project, Tag 0BUZ (precomposition algebra action), and Tag 0BQZ.
(blueprint: lem-sc-closed-immersion-ext-ideal-action).

Proof: Represent O_Y by a K-injective complex J. Since the first argument is
concentrated in degree zero, the Hom complex is the complex of sheaves
Hom(i_* O_Z, J^p). A local section a of the immersion ideal acts as zero on
these sheaves: for any local O_Y-linear map t, a t(b) = t(ab) = t(0) = 0,
because the structure map O_Y -> i_* O_Z kills a. This equality holds after
all further restrictions and therefore is an equality of sheaf multiplication
maps. It passes to kernels, images and cokernels defining cohomology, so the
ideal acts by zero on every cohomology sheaf of this complex. The derived Hom
representation and the homology comparison are O_Y-linear, so they transport
this equality to the displayed Ext sheaf. Multiplication on the sheaf tensor
product is the sheafification of a tensor b |-> ab, so vanishing of every such
local product is exactly the stated zero morphism. If Z is empty, the first
argument and the Hom complex are zero; for the identity immersion the ideal
itself is zero. Negative degrees cause no change to the argument. -/
theorem closedImmersion_ext_idealAction_eq_zero
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (q : ℤ) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    i.ker.toModulesι ▷ F ≫ (λ_ F).hom = 0 := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let P : A := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let L : A := SheafOfModules.unit Y.ringCatSheaf
  let B : Y.CommAlgebraSheaf := Under.mk (⟨i.c⟩ : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat i.base).obj Z.sheaf)
  let T := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map B.hom)
  let : HasDerivedCategory (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := HasDerivedCategory.standard _
  let S := sheafAlgebraHom Y B
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := injectiveResolution L
  have : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let C := (S.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex
  have : PreservesFiniteLimits T := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits T := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  obtain ⟨eR⟩ := derivedInternalHom_obj_iso
    (Opens.grothendieckTopology Y) Y.sheaf
    ((DerivedCategory.singleFunctor A 0).obj P)
    ((DerivedCategory.singleFunctor A 0).obj L)
    ((CochainComplex.singleFunctor A 0).obj P) I.cochainComplex
    (Iso.refl _) ((asIso (DerivedCategory.Q.map I.ι')).symm)
  obtain ⟨h⟩ := homComplex_single_iso Y P I.cochainComplex
  let eC := h ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (sheafAlgebraHomUnderlyingIso Y B) (ComplexShape.up ℤ)).app I.cochainComplex).symm
  let eH := (DerivedCategory.homologyFunctor A q).mapIso eR ≪≫
    (DerivedCategory.homologyFunctorFactors A q).app _ ≪≫
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).mapIso eC ≪≫
    (C.sc q).mapHomologyIso T
  apply idealAction_zero_of_iso i.ker eH
  apply idealAction_zero_of_sections
  intro V a ha s
  have hz : (i.app V).hom a = 0 := by
    have hz := (Scheme.IdealSheafData.mem_idealOfOpens_iff i.ker).mp ha
    rw [← i.toImage_imageι, Scheme.Hom.comp_app]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hz, map_zero]
  change (B.hom.hom.app (op V)).hom a •
    (show (C.homology q).val.obj (op V) from s) = 0
  change (i.app V).hom a •
    (show (C.homology q).val.obj (op V) from s) = 0
  rw [hz, zero_smul]

end AlgebraicGeometry
