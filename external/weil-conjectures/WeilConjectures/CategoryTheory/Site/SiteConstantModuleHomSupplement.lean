/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SiteConstantModuleHom

/-! # Internal Hom of constant module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T (1), and Tag 0E8H
(blueprint: lem-pur-site-constant-module-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
private instance homUnit_surjective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallySurjective J (constantModuleHomUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private instance homUnit_injective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallyInjective J (constantModuleHomUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private lemma homUnit_naturality {M N : ModuleCat.{max u v} Λ} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M) :
    ((constantModuleHomFunctor J Λ).map f).val.app U
      ((constantModuleHomUnit J Λ M).app U x) =
        (constantModuleHomUnit J Λ N).app U (f x) := by
  have h := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) Λ).map f))
  exact (ConcreteCategory.congr_hom (congr_app h U) x).symm

private def homMap (M N : ModuleCat.{max u v} Λ) (f : M →ₗ[Λ] N) :
    (constantModuleHomFunctor J Λ).obj M ⟶ (constantModuleHomFunctor J Λ).obj N :=
  (constantModuleHomFunctor J Λ).map (show M ⟶ N from ModuleCat.ofHom f)

private lemma homMap_unit (M N : ModuleCat.{max u v} Λ) (f : M →ₗ[Λ] N)
    (U : Cᵒᵖ) (x : M) :
    (homMap J Λ M N f).val.app U ((constantModuleHomUnit J Λ M).app U x) =
      (constantModuleHomUnit J Λ N).app U (f x) :=
  homUnit_naturality J Λ (show M ⟶ N from ModuleCat.ofHom f) U x

private abbrev homCommRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ)

private abbrev homRing :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    (homCommRing J Λ)

private def homRingUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ (homRing J Λ).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) ≫
    (constantModuleHomRingIso J Λ).hom.hom

set_option backward.isDefEq.respectTransparency false in
private def homUnitLinear (M : ModuleCat.{max u v} Λ) :
    (siteConstantModulePresheafGeneral (C := C) Λ).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
        ((constantModuleHomFunctor J Λ).obj M).val :=
  PresheafOfModules.homMk (constantModuleHomUnit J Λ M) (fun U r x ↦ by
    have hi := congrArg
      (fun f ↦ f.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r))
      (constantModuleHomRingIso J Λ).hom_inv_id
    change (constantModuleHomRingIso J Λ).inv.hom.app U
      ((constantModuleHomRingIso J Λ).hom.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r at hi
    change (constantModuleHomUnit J Λ M).app U (r • x) =
      (constantModuleHomRingIso J Λ).inv.hom.app U
        ((constantModuleHomRingIso J Λ).hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r)) •
        (show ((siteConstantModuleFunctorGeneral J Λ).obj M).val.obj U from
          (constantModuleHomUnit J Λ M).app U x)
    rw [hi]
    exact (((PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).unit.app
        ((siteConstantModulePresheafGeneral (C := C) Λ).obj M)).app U).hom.map_smul r x)

private lemma homUnit_ext (M N : ModuleCat.{max u v} Λ) (U : C)
    (a b : (PresheafOfModules.restrictOver (homCommRing J Λ).obj U).obj
        ((constantModuleHomFunctor J Λ).obj M).val ⟶
      (PresheafOfModules.restrictOver (homCommRing J Λ).obj U).obj
        ((constantModuleHomFunctor J Λ).obj N).val)
    (h : ∀ (V : Over U) (x : M),
      a.app (op V) ((constantModuleHomUnit J Λ M).app (op V.left) x) =
        b.app (op V) ((constantModuleHomUnit J Λ M).app (op V.left) x)) : a = b := by
  let FM := (constantModuleHomFunctor J Λ).obj M
  let FN := (constantModuleHomFunctor J Λ).obj N
  let η := constantModuleHomUnit J Λ M
  ext V s
  apply FN.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η s)
  intro W f hf
  obtain ⟨x, hx⟩ := hf
  let V' : Over U := Over.mk (f ≫ V.unop.hom)
  have ha := PresheafOfModules.naturality_apply a
    (Over.homMk f : V' ⟶ V.unop).op s
  have hb := PresheafOfModules.naturality_apply b
    (Over.homMk f : V' ⟶ V.unop).op s
  change a.app (op V') (FM.val.map f.op s) = FN.val.map f.op (a.app V s) at ha
  change b.app (op V') (FM.val.map f.op s) = FN.val.map f.op (b.app V s) at hb
  change η.app (op W) x = FM.val.map f.op s at hx
  change FN.val.map f.op (a.app V s) = FN.val.map f.op (b.app V s)
  rw [← ha, ← hb, ← hx]
  exact h V' x

set_option backward.isDefEq.respectTransparency false in
private def homConstMap (M N : ModuleCat.{max u v} Λ) :
    (siteConstantModulePresheafGeneral (C := C) Λ).obj
        (ModuleCat.of Λ (M →ₗ[Λ] N)) ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
        (SheafOfModules.homObj (R := homCommRing J Λ)
          ((constantModuleHomFunctor J Λ).obj M)
          ((constantModuleHomFunctor J Λ).obj N)).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
      (SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M)
        ((constantModuleHomFunctor J Λ).obj N)).val).obj U)
    { toFun f := (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
        ((homMap J Λ M N f).val)
      map_add' f g := by
        apply homUnit_ext J Λ M N U.unop
        intro V x
        change (homMap J Λ M N (f + g)).val.app _
            ((constantModuleHomUnit J Λ M).app _ x) =
          (homMap J Λ M N f).val.app _
              ((constantModuleHomUnit J Λ M).app _ x) +
            (homMap J Λ M N g).val.app _
              ((constantModuleHomUnit J Λ M).app _ x)
        erw [homMap_unit J Λ M N,
          homMap_unit J Λ M N,
          homMap_unit J Λ M N]
        exact ((constantModuleHomUnit J Λ N).app (op V.left)).hom.map_add (f x) (g x)
      map_smul' r f := by
        change (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
            ((homMap J Λ M N (r • f)).val) =
          (show (homCommRing J Λ).obj.obj (op U.unop) from (homRingUnit J Λ).app U r) •
            (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
              ((homMap J Λ M N f).val)
        apply homUnit_ext J Λ M N U.unop
        intro V x
        change (homMap J Λ M N (r • f)).val.app _
            ((constantModuleHomUnit J Λ M).app _ x) =
          (homRing J Λ).obj.map V.hom.op ((homRingUnit J Λ).app U r) •
            (show ((constantModuleHomFunctor J Λ).obj N).val.obj (op V.left) from
              (homMap J Λ M N f).val.app _
                ((constantModuleHomUnit J Λ M).app _ x))
        erw [homMap_unit J Λ M N,
          homMap_unit J Λ M N]
        have hn := NatTrans.naturality_apply (homRingUnit J Λ) V.hom.op r
        change (homRingUnit J Λ).app (op V.left) r =
          (homRing J Λ).obj.map V.hom.op ((homRingUnit J Λ).app U r) at hn
        rw [← hn]
        exact ((homUnitLinear J Λ N).app (op V.left)).hom.map_smul r (f x) }
  naturality {U V} g := by
    ext f
    rfl

private instance homRingUnit_surjective : Presheaf.IsLocallySurjective J (homRingUnit J Λ) := by
  unfold homRingUnit
  infer_instance

private instance homUnitLinear_surjective (M : ModuleCat.{max u v} Λ) :
    PresheafOfModules.IsLocallySurjective J (homUnitLinear J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private instance homUnitLinear_injective (M : ModuleCat.{max u v} Λ) :
    PresheafOfModules.IsLocallyInjective J (homUnitLinear J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private def homComparison (M N : ModuleCat.{max u v} Λ) :
    (constantModuleHomFunctor J Λ).obj (ModuleCat.of Λ (M →ₗ[Λ] N)) ⟶
      SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M) ((constantModuleHomFunctor J Λ).obj N) where
  val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective (homRingUnit J Λ)
      (SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M)
        ((constantModuleHomFunctor J Λ).obj N)).isSheaf).symm
    ((PresheafOfModules.homEquivOfIsLocallyBijective
      (homUnitLinear J Λ (ModuleCat.of Λ (M →ₗ[Λ] N)))
      (SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M)
        ((constantModuleHomFunctor J Λ).obj N)).isSheaf).symm (homConstMap J Λ M N))

private lemma homComparison_unit (M N : ModuleCat.{max u v} Λ)
    (U : Cᵒᵖ) (f : M →ₗ[Λ] N) :
    (homComparison J Λ M N).val.app U
        ((constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))).app U f) =
      (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
        (((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom f)).val) := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective
    (homUnitLinear J Λ (ModuleCat.of Λ (M →ₗ[Λ] N)))
    (SheafOfModules.homObj (R := homCommRing J Λ)
      ((constantModuleHomFunctor J Λ).obj M)
      ((constantModuleHomFunctor J Λ).obj N)).isSheaf).apply_symm_apply
        (homConstMap J Λ M N)
  change (homComparison J Λ M N).val.app U
      ((constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))).app U f) =
    (homConstMap J Λ M N).app U f
  exact congrArg (fun t ↦ t.app U f) h

private lemma homComparison_naturality
    (M M' N N' : ModuleCat.{max u v} Λ) (a : M' ⟶ M) (b : N ⟶ N') :
    (constantModuleHomFunctor J Λ).map (ModuleCat.ofHom
      ((LinearMap.llcomp Λ M' N N' b.hom).comp (LinearMap.lcomp Λ N a.hom))) ≫
        homComparison J Λ M' N' =
      homComparison J Λ M N ≫ SheafOfModules.homObjMap
        (R := homCommRing J Λ) ((constantModuleHomFunctor J Λ).map a)
        ((constantModuleHomFunctor J Λ).map b) := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext J _ _
    (SheafOfModules.homObj (R := homCommRing J Λ)
      ((constantModuleHomFunctor J Λ).obj M')
      ((constantModuleHomFunctor J Λ).obj N')).isSheaf
  apply NatTrans.ext
  funext U
  ext f
  change (homComparison J Λ M' N').val.app U
      (((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom
        ((LinearMap.llcomp Λ M' N N' b.hom).comp (LinearMap.lcomp Λ N a.hom)))).val.app U
        ((constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))).app U f)) = _
  rw [homUnit_naturality, homComparison_unit]
  change (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
      (((constantModuleHomFunctor J Λ).map (a ≫ ModuleCat.ofHom f ≫ b)).val) = _
  rw [Functor.map_comp, Functor.map_comp]
  change (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
      (((constantModuleHomFunctor J Λ).map a).val ≫
        ((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom f)).val ≫
        ((constantModuleHomFunctor J Λ).map b).val) = _
  rw [Functor.map_comp, Functor.map_comp]
  change _ =
    (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
      (((constantModuleHomFunctor J Λ).map a).val) ≫
    (homComparison J Λ M N).val.app U
      ((constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))).app U f) ≫
    (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
      (((constantModuleHomFunctor J Λ).map b).val)
  rw [homComparison_unit]

private lemma homConstMap_injective (M N : ModuleCat.{max u v} Λ) [Module.Finite Λ M] :
    PresheafOfModules.IsLocallyInjective J (homConstMap J Λ M N) where
  equalizerSieve_mem {U} a b hab := by
    classical
    change M →ₗ[Λ] N at a b
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
    let η := constantModuleHomUnit J Λ N
    have he (x : M) : η.app U (a x) = η.app U (b x) := by
      have h := congrArg
        (fun z ↦ z.app (op (Over.mk (𝟙 U.unop)))
          ((constantModuleHomUnit J Λ M).app U x)) hab
      change ((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom a)).val.app U
          ((constantModuleHomUnit J Λ M).app U x) =
        ((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom b)).val.app U
          ((constantModuleHomUnit J Λ M).app U x) at h
      rw [homUnit_naturality J Λ (M := M) (N := N),
        homUnit_naturality J Λ (M := M) (N := N)] at h
      exact h
    let S (x : M) : Sieve U.unop :=
      Presheaf.equalizerSieve (F := (Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj N)) (X := U) (a x) (b x)
    have hS (x : M) : S x ∈ J U.unop :=
      Presheaf.equalizerSieve_mem J η (a x) (b x) (he x)
    apply J.superset_covering _ (J.finsetInf_mem s S hS)
    intro V f hf
    change a = b
    apply LinearMap.ext_on hs
    intro x hx
    exact Finset.inf_le hx (f := S) f hf

private def homSections (M : ModuleCat.{max u v} Λ) : Cᵒᵖ ⥤ ModuleCat.{max u v} Λ where
  obj U := ((PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
    ((constantModuleHomFunctor J Λ).obj M).val).obj U
  map f := ((PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
    ((constantModuleHomFunctor J Λ).obj M).val).map f
  map_id U := by ext x; simp; rfl
  map_comp f g := by ext x; simp; rfl

private def homSectionsUnit (M : ModuleCat.{max u v} Λ) :
    (Functor.const Cᵒᵖ).obj M ⟶ homSections J Λ M where
  app U := (homUnitLinear J Λ M).app U
  naturality {U V} f := by
    ext x
    exact NatTrans.naturality_apply (constantModuleHomUnit J Λ M) f x

private instance homSectionsUnit_injective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallyInjective J (homSectionsUnit J Λ M) where
  equalizerSieve_mem x y h :=
    Presheaf.equalizerSieve_mem J (constantModuleHomUnit J Λ M) x y h

private instance homSectionsUnit_surjective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallySurjective J (homSectionsUnit J Λ M) where
  imageSieve_mem x := Presheaf.imageSieve_mem J (constantModuleHomUnit J Λ M) x

private lemma homConstMap_surjective (M N : ModuleCat.{max u v} Λ)
    [Module.FinitePresentation Λ M] :
    PresheafOfModules.IsLocallySurjective J (homConstMap J Λ M N) where
  imageSieve_mem {U} x := by
    let F := constantModuleHomFunctor J Λ
    let φ : M ⟶ (homSections J Λ N).obj (op U) :=
      (homSectionsUnit J Λ M).app (op U) ≫
        (ModuleCat.restrictScalars ((homRingUnit J Λ).app (op U)).hom).map
          (x.app (op (Over.mk (𝟙 U))))
    have hS := finitePresentation_linearLiftSieve_mem (J := J) (homSectionsUnit J Λ N) φ
    apply J.superset_covering _ hS
    intro V f hf
    obtain ⟨g, hg⟩ := hf
    refine ⟨g, ?_⟩
    apply homUnit_ext J Λ M N V
    intro W m
    change ((F.map (ModuleCat.ofHom g)).val.app (op W.left))
        ((constantModuleHomUnit J Λ M).app (op W.left) m) =
      x.app (op ((Over.map f).obj W))
        ((constantModuleHomUnit J Λ M).app (op W.left) m)
    rw [homUnit_naturality J Λ (M := M) (N := N)]
    have ha := PresheafOfModules.naturality_apply x
      (Over.homMk (W.hom ≫ f) :
        (Over.map f).obj W ⟶ Over.mk (𝟙 U)).op
      ((constantModuleHomUnit J Λ M).app (op U) m)
    have hn := NatTrans.naturality_apply (constantModuleHomUnit J Λ M) (W.hom ≫ f).op m
    change (constantModuleHomUnit J Λ M).app (op W.left) m =
      (F.obj M).val.map (W.hom ≫ f).op
        ((constantModuleHomUnit J Λ M).app (op U) m) at hn
    change x.app (op ((Over.map f).obj W))
        ((F.obj M).val.map (W.hom ≫ f).op
          ((constantModuleHomUnit J Λ M).app (op U) m)) =
      (F.obj N).val.map (W.hom ≫ f).op
        (x.app (op (Over.mk (𝟙 U)))
          ((constantModuleHomUnit J Λ M).app (op U) m)) at ha
    rw [← hn] at ha
    have hgm := hg m
    change (constantModuleHomUnit J Λ N).app (op V) (g m) =
      (F.obj N).val.map f.op
        (x.app (op (Over.mk (𝟙 U)))
          ((constantModuleHomUnit J Λ M).app (op U) m)) at hgm
    have hn' := NatTrans.naturality_apply (constantModuleHomUnit J Λ N) W.hom.op (g m)
    change (constantModuleHomUnit J Λ N).app (op W.left) (g m) =
      (F.obj N).val.map W.hom.op ((constantModuleHomUnit J Λ N).app (op V) (g m)) at hn'
    change (constantModuleHomUnit J Λ N).app (op W.left) (g m) = _
    rw [hn', hgm]
    exact (congrArg (fun z ↦ z) (by
      rw [op_comp, PresheafOfModules.map_comp_apply] : (F.obj N).val.map (W.hom ≫ f).op
        (x.app (op (Over.mk (𝟙 U)))
          ((constantModuleHomUnit J Λ M).app (op U) m)) =
        (F.obj N).val.map W.hom.op ((F.obj N).val.map f.op
          (x.app (op (Over.mk (𝟙 U)))
            ((constantModuleHomUnit J Λ M).app (op U) m))))).symm.trans ha.symm

private lemma homComparison_isIso (M N : ModuleCat.{max u v} Λ)
    [Module.FinitePresentation Λ M] : IsIso (homComparison J Λ M N) := by
  let η := constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))
  let γ := (PresheafOfModules.toPresheaf _).map (homComparison J Λ M N).val
  have hfac : η ≫ γ = (PresheafOfModules.toPresheaf _).map (homConstMap J Λ M N) := by
    ext U f
    exact homComparison_unit J Λ M N U f
  have := homConstMap_injective J Λ M N
  have := homConstMap_surjective J Λ M N
  have hi : Presheaf.IsLocallyInjective J γ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J _ hfac
  have hs : Presheaf.IsLocallySurjective J γ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have : IsIso ((SheafOfModules.toSheaf _).map (homComparison J Λ M N)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hi, hs⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- The canonical Hom comparison for constant module sheaves, together with its naturality
and the same-map rule on each localized site.

Source: Stacks Project, Modules on Sites, Tag 093T (1), and Tag 0E8H
(blueprint: lem-pur-site-constant-module-hom).

Proof plan:
1. The local module Hom presheaf is a sheaf by lem-sf-local-module-hom-sheaf.
Send a constant linear map to its constant module sheaf map on each slice. The
sheafification unit formula proves additivity and compatibility with constant scalars.
2. A finite presentation implies finite generation, also in rank zero. Apply
lem-sf-constant-module-hom-locally-injective and
lem-sf-constant-module-hom-locally-surjective to the same constant-map comparison.
3. Apply lem-weil-pbc-site-sheafification-iso-locally-bijective and the universal
property of def-weil-pbc-sheafification. Since the local Hom is already a sheaf,
this gives the canonical additive comparison and its isomorphism assertion.
4. Use lem-sf-constant-module-unit-locally-bijective for local constant Hom sections,
lem-pc-sites-sheafification-underlying-sets and
lem-weil-pbc-site-sheafification-sections-local for local constant ring sections.
Refine both coverings, compute scalar compatibility on constants and use separatedness.
The inverse is linear by injectivity. Empty covering sieves give unique sections.
5. On constants the naturality square is functoriality applied to v f u. Local
constant representatives and separatedness extend it to all sections. For localization,
lem-weil-pbc-site-constant-restriction preserves the units and constant maps. The
recorded internal Hom and relocalization have the same slice morphisms and restrictions,
so both comparisons send a constant f to the same restricted sheaf map. -/
theorem siteConstantModule_hom
    (P Q : ModuleCat.{max u v} Λ) [Module.FinitePresentation Λ P] :
    ∃ comparison : ∀ M N : ModuleCat.{max u v} Λ,
      (constantModuleHomFunctor J Λ).obj (ModuleCat.of Λ (M →ₗ[Λ] N)) ⟶
        SheafOfModules.homObj (R := (constantSheaf J CommRingCat.{max u v}).obj
          (CommRingCat.of Λ))
          ((constantModuleHomFunctor J Λ).obj M) ((constantModuleHomFunctor J Λ).obj N),
      (∀ (M N : ModuleCat.{max u v} Λ) (U : Cᵒᵖ) (f : M →ₗ[Λ] N),
        (comparison M N).val.app U
            ((constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))).app U f) =
          (PresheafOfModules.restrictOver
            ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ)).obj U.unop).map
            (((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom f)).val)) ∧
      IsIso (comparison P Q) ∧
      (∀ (M M' N N' : ModuleCat.{max u v} Λ) (a : M' ⟶ M) (b : N ⟶ N'),
        (constantModuleHomFunctor J Λ).map (ModuleCat.ofHom
          ((LinearMap.llcomp Λ M' N N' b.hom).comp (LinearMap.lcomp Λ N a.hom))) ≫
            comparison M' N' =
          comparison M N ≫ SheafOfModules.homObjMap
            (R := (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ))
            ((constantModuleHomFunctor J Λ).map a)
            ((constantModuleHomFunctor J Λ).map b)) ∧
      (∀ (U : C) (V : Over U) (f : P →ₗ[Λ] Q),
        (((comparison P Q).over U).val.app (op V)
          ((constantModuleHomUnit J Λ (ModuleCat.of Λ (P →ₗ[Λ] Q))).app (op V.left) f)).app
            (op (Over.mk (𝟙 V.left))) =
          (((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom f)).over U).val.app (op V)) := by
  refine ⟨homComparison J Λ, homComparison_unit J Λ, homComparison_isIso J Λ P Q,
    homComparison_naturality J Λ, ?_⟩
  intro U V f
  exact congrArg (fun a ↦ a.app (op (Over.mk (𝟙 V.left))))
    (homComparison_unit J Λ P Q (op V.left) f)

end CategoryTheory
