/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
/-! # Open restriction and the direct-image counit.

## References

* Stacks Project, pro-etale functoriality (09A5), Sites (00XZ, 03CB, 03CF), and Modules on Sites
  (03D3, 04J0)
* Stacks Sites, Tag 03CB
* Stacks Sites, Tag 00XZ
* Stacks Sites, Tag 03CF
-/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProEtaleOpenRestriction

/-- The inverse-image coefficient ring on X. -/
noncomputable abbrev RX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R

/-- The inverse-image coefficient ring on W. -/
noncomputable abbrev RW {Y W : Scheme.{u}} (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R

/-- The inverse-image coefficient ring on the fibre product X_W. -/
noncomputable abbrev RXW {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage (pullback.fst f h) CommRingCat.{u + 1}).obj (RX f R)

/-- The type of coefficient comparisons; `coefficientIso` fixes the canonical one. -/
noncomputable abbrev CoeffCmp {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  RW (pullback.snd f h) (RW h R) ≅ RXW f h R

/-- Base-change associativity around the cartesian square, with its canonical projections. -/
noncomputable def squareSiteIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y) :
    proEtaleBaseChange f ⋙ proEtaleBaseChange (pullback.fst f h) ≅
      proEtaleBaseChange h ⋙ proEtaleBaseChange (pullback.snd f h) :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (pullback.fst f h) f).symm ≪≫
  eqToIso (congrArg (fun k ↦ proEtaleBaseChange k) (pullback.condition (f := f) (g := h))) ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (pullback.snd f h) h

/-- The inverse-image comparison is the mate of the projection-preserving site isomorphism. -/
noncomputable def ringSquareIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y) :
    proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage (pullback.fst f h) CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage h CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage (pullback.snd f h) CommRingCat.{u + 1} :=
  letI := Functor.isContinuous_comp (proEtaleBaseChange h)
    (proEtaleBaseChange (pullback.snd f h)) (ProEt.topology Y) (ProEt.topology W)
      (ProEt.topology (pullback f h))
  ((conjugateIsoEquiv
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.fst f h) CommRingCat.{u + 1}))
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.snd f h) CommRingCat.{u + 1}))).symm
    ((Functor.sheafPushforwardContinuousComp' (eFG := squareSiteIso f h)
      CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X)
        (ProEt.topology (pullback f h))) ≪≫
      (Functor.sheafPushforwardContinuousComp (proEtaleBaseChange h)
        (proEtaleBaseChange (pullback.snd f h)) CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology W)
            (ProEt.topology (pullback f h))).symm)).symm

/-- The coefficient comparison is fixed, not an existentially supplied automorphism. -/
noncomputable def coefficientIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) : CoeffCmp f h R :=
  (ringSquareIso f h).symm.app R

/-- Composition sends an object over the source of a weakly etale map to the target site. -/
abbrev objectComposition {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map (f := h) ⊤ (inferInstance : WeaklyEtale h)

/-- The canonical fibre-product arrow `(E ×[W] X_W → X) → (E ×[Y] X → X)`.
The map is the identity on E and the first projection on X_W; thus it is the specified
fibre-product identification, rather than a freely supplied section equivalence. -/
noncomputable def sectionArrow {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (E : W.ProEt) :
    (objectComposition (pullback.fst f h)).obj
        ((proEtaleBaseChange (pullback.snd f h)).obj E) ⟶
      (proEtaleBaseChange f).obj ((objectComposition h).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.map E.hom (pullback.snd f h) (E.hom ≫ h) f
      (𝟙 E.left) (pullback.fst f h) h (Category.id_comp _).symm (pullback.condition ..).symm)
    (pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem pullback_eqToIso {A B : Scheme.{u}} {i j : A ⟶ B} (e : i = j) :
    eqToIso (congrArg (fun k ↦ proEtaleBaseChange k) e) =
      MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e := by
  subst e
  apply Iso.ext
  apply NatTrans.ext
  funext V
  apply MorphismProperty.Over.Hom.ext
  simp [MorphismProperty.Over.pullbackCongr, proEtaleBaseChange]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleMap_isIso_of_bijective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} A}
    (z : M ⟶ N) (hz : ∀ E, Function.Bijective (z.val.app E)) : IsIso z := by
  have hzi (E) : IsIso (z.val.app E) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hz E)
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun E ↦ asIso (z.val.app E)) (by intro U V g; exact z.val.naturality g)
  have : IsIso z.val := show IsIso e.hom from inferInstance
  have : IsIso ((SheafOfModules.forget A).map z) := ‹IsIso z.val›
  exact isIso_of_reflects_iso z (SheafOfModules.forget A)

end AlgebraicGeometry.Scheme.ProEtaleOpenRestriction
