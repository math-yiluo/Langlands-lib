/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import Mathlib.LinearAlgebra.Dual.Defs
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Descent of scalar evaluation into the internal dual sheaf

Source: Stacks Project, Cohomology on Sites, Tag 08JJ, final evaluation comparison;
Modules on Sites, Tags 03CY, 0GMW, 03EL, 04TT and 03DH.
(blueprint: lem-sfb-scalar-dual-evaluation-descent).

The scalar realization is the existing change of rings of the recorded constant module
functor, transported along its existing canonical coefficient-ring isomorphism.
Generators use the two existing sheafification units. Internal Hom sections are actual
linear maps on localized sites, so quantifying over `a : T ⟶ U` records evaluation after
every restriction. No finite generation, projectivity or flatness assumption is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] (B : Sheaf J CommRingCat.{max u v})
  (α : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

/-- The node's `C_B(V) = B ⊗_{R̲} V̲`, using the recorded constant module functor and
ordinary change of rings. The canonical coefficient transport is already defined in
`constantModuleHomFunctor`; no second constant module or tensor construction is made.
Source: Stacks Tags 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
abbrev scalarConstantRealization (V : ModuleCat.{max u v} R) :
    ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  changeOfRingsOfUniverses.{v, u, max u v, max u v} α
    ((constantModuleHomFunctor J R).obj V)

/-- The existing change-of-rings map applied to the constant module map `f`.
Source: Stacks Tags 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
def scalarConstantRealizationMap {V W : ModuleCat.{max u v} R} (f : V ⟶ W) :
    scalarConstantRealization J R B α V ⟶ scalarConstantRealization J R B α W :=
  changeOfRingsHomOfUniverses α ((constantModuleHomFunctor J R).obj V)
    ((constantModuleHomFunctor J R).map f)

/-- The generator `b ⊗ v` in scalar realization: first insert the constant module section,
then insert its scalar tensor using the existing change-of-rings sheafification unit.
Source: Stacks Tags 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
def scalarConstantGenerator (V : ModuleCat.{max u v} R) (U : Cᵒᵖ)
    (b : B.obj.obj U) (x : V) : (scalarConstantRealization J R B α V).val.obj U :=
  scalarExtensionRingIsoTmul α ((constantModuleHomFunctor J R).obj V) U
    ((constantModuleHomUnit J R V).app U x) b

/-- The internal dual of the specified scalar realization, with the actual unit module
sheaf as target. Source: Stacks Tag 04TT
(blueprint: lem-sfb-scalar-dual-evaluation-descent). -/
abbrev scalarDualEvaluationTarget (V : ModuleCat.{max u v} R) :=
  homObj (R := B) (scalarConstantRealization J R B α V)
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

private abbrev baseRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

private abbrev coeffRing :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj B

private def scalarExtend (M : ringedSiteModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :
    changeOfRingsOfUniverses.{v, u, max u v, max u v} α M ⟶ N :=
  scalarExtensionLift α M N f

private lemma scalarExtend_tmul
    (M : ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N)
    (U : Cᵒᵖ) (x : M.val.obj U) (b : B.obj.obj U) :
    (scalarExtend J R B α M N f).val.app U (scalarExtensionRingIsoTmul α M U x b) =
      b • (show N.val.obj U from f.val.app U x) := by
  exact scalarExtensionLift_tmul α M N f U b x

private def scalarRingUnit : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
    (coeffRing J B).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ≫
    (constantModuleHomRingIso J R).hom.hom ≫
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α).hom

private lemma scalarRingUnit_apply (U : Cᵒᵖ) (r : R) :
    (scalarRingUnit J R B α).app U r = α.hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U r) := by
  have h := sheafComposeNatTrans_fac J (forget₂ CommRingCat RingCat)
    (sheafificationAdjunction J CommRingCat) (sheafificationAdjunction J RingCat)
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))
  exact congrArg (fun t ↦ α.hom.app U (t.app U r)) h

private def constantLift (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val) :
    (constantModuleHomFunctor J R).obj M ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N := by
  let c := constantModuleHomRingIso J R
  let a := c.hom ≫ (sheafCompose J (forget₂ CommRingCat RingCat)).map α
  let g : (siteConstantModuleFunctorGeneral J R).obj M ⟶ (restrictScalars a).obj N :=
    (PresheafOfModules.sheafificationHomEquiv
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).symm f
  refine ⟨PresheafOfModules.homMk ((SheafOfModules.toSheaf _).map g).hom ?_⟩
  intro U r x
  have hg := (g.val.app U).hom.map_smul (c.inv.hom.app U r) x
  change g.val.app U (c.inv.hom.app U r •
      (show ((siteConstantModuleFunctorGeneral J R).obj M).val.obj U from x)) =
    α.hom.app U r • (show N.val.obj U from g.val.app U x)
  change g.val.app U (c.inv.hom.app U r •
      (show ((siteConstantModuleFunctorGeneral J R).obj M).val.obj U from x)) =
    α.hom.app U (c.hom.hom.app U (c.inv.hom.app U r)) •
      (show N.val.obj U from g.val.app U x) at hg
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.hom.app U) c.inv_hom_id) r
  change c.hom.hom.app U (c.inv.hom.app U r) = r at hc
  rwa [hc] at hg

private lemma constantLift_unit (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val)
    (U : Cᵒᵖ) (x : M) :
    (constantLift J R B α M N f).val.app U ((constantModuleHomUnit J R M).app U x) =
      f.app U x := by
  let a := (constantModuleHomRingIso J R).hom ≫
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α
  have h := (PresheafOfModules.sheafificationHomEquiv.{max u v}
    (R := (constantSheaf J RingCat.{max u v}).obj (RingCat.of R))
    (F := (restrictScalars a).obj N)
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).apply_symm_apply f
  exact congrArg (fun t ↦ t.app U (show
    ((siteConstantModulePresheafGeneral (C := C) R).obj M).obj U from x)) h

private def scalarLift (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val) :
    scalarConstantRealization J R B α M ⟶ N :=
  scalarExtend J R B α _ N (constantLift J R B α M N f)

private lemma scalarLift_generator (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (scalarRingUnit J R B α)).obj N.val)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : M) :
    (scalarLift J R B α M N f).val.app U (scalarConstantGenerator J R B α M U b x) =
      b • (show N.val.obj U from f.app U x) := by
  change (scalarExtend J R B α _ N _).val.app U
    (scalarExtensionRingIsoTmul α _ U ((constantModuleHomUnit J R M).app U x) b) = _
  rw [scalarExtend_tmul, constantLift_unit]

private lemma scalarTmul_restrict
    (M : ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    {U T : Cᵒᵖ} (a : U ⟶ T) (x : M.val.obj U) (b : B.obj.obj U) :
    (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a
        (scalarExtensionRingIsoTmul α M U x b) =
      scalarExtensionRingIsoTmul α M T (M.val.map a x) (B.obj.map a b) := by
  exact scalarExtensionSection_naturality α M a b x

private lemma rawScalarOver_ext
    (M : ringedSiteModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (baseRing J R)))
    (N : ringedSiteModules.{max u v} (coeffRing J B)) (U : C)
    (f g : (PresheafOfModules.restrictOver B.obj U).obj
        (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val ⟶
      (PresheafOfModules.restrictOver B.obj U).obj N.val)
    (h : ∀ (W : Over U) (b : B.obj.obj (op W.left)) (x : M.val.obj (op W.left)),
      f.app (op W) (scalarExtensionRingIsoTmul α M (op W.left) x b) =
        g.app (op W) (scalarExtensionRingIsoTmul α M (op W.left) x b)) : f = g := by
  let E := changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (coeffRing J B).obj)).unit.app E
  let τ := (PresheafOfModules.toPresheaf _).map η
  have : Presheaf.IsLocallySurjective J τ :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J E.presheaf))
  ext W s
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J τ s)
  intro T a ha
  obtain ⟨z, hz⟩ := ha
  let W' : Over U := Over.mk (a ≫ W.unop.hom)
  have hf := PresheafOfModules.naturality_apply f
    (Over.homMk a : W' ⟶ W.unop).op s
  have hg := PresheafOfModules.naturality_apply g
    (Over.homMk a : W' ⟶ W.unop).op s
  change η.app (op T) z =
    (changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a.op s at hz
  change f.app (op W') ((changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a.op s) =
    N.val.map a.op (f.app W s) at hf
  change g.app (op W') ((changeOfRingsOfUniverses.{v, u, max u v, max u v} α M).val.map a.op s) =
    N.val.map a.op (g.app W s) at hg
  change N.val.map a.op (f.app W s) = N.val.map a.op (g.app W s)
  rw [← hf, ← hg, ← hz]
  have he : η.app (op T) ≫ f.app (op W') = η.app (op T) ≫ g.app (op W') := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact h W' 1 x
  exact ConcreteCategory.congr_hom he z

private lemma scalarOver_ext (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B)) (U : C)
    (f g : (PresheafOfModules.restrictOver B.obj U).obj
        (scalarConstantRealization J R B α M).val ⟶
      (PresheafOfModules.restrictOver B.obj U).obj N.val)
    (h : ∀ (W : Over U) (b : B.obj.obj (op W.left)) (x : M),
      f.app (op W) (scalarConstantGenerator J R B α M (op W.left) b x) =
        g.app (op W) (scalarConstantGenerator J R B α M (op W.left) b x)) : f = g := by
  apply rawScalarOver_ext J R B α _ N U f g
  intro W b x
  let η := constantModuleHomUnit J R M
  have : Presheaf.IsLocallySurjective J η :=
    inferInstanceAs (Presheaf.IsLocallySurjective J
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf))
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η x)
  intro T a ha
  obtain ⟨m, hm⟩ := ha
  let W' : Over U := Over.mk (a ≫ W.hom)
  have hf := PresheafOfModules.naturality_apply f
    (Over.homMk a : W' ⟶ W).op (scalarExtensionRingIsoTmul α _ (op W.left) x b)
  have hg := PresheafOfModules.naturality_apply g
    (Over.homMk a : W' ⟶ W).op (scalarExtensionRingIsoTmul α _ (op W.left) x b)
  change η.app (op T) m =
    ((constantModuleHomFunctor J R).obj M).val.map a.op x at hm
  change f.app (op W') ((scalarConstantRealization J R B α M).val.map a.op
      (scalarExtensionRingIsoTmul α _ (op W.left) x b)) =
    N.val.map a.op (f.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b)) at hf
  change g.app (op W') ((scalarConstantRealization J R B α M).val.map a.op
      (scalarExtensionRingIsoTmul α _ (op W.left) x b)) =
    N.val.map a.op (g.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b)) at hg
  change N.val.map a.op (f.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b)) =
    N.val.map a.op (g.app (op W) (scalarExtensionRingIsoTmul α _ (op W.left) x b))
  rw [← hf, ← hg]
  erw [scalarTmul_restrict, ← hm]
  exact h W' (B.obj.map a.op b) m

private lemma scalarHom_ext (M : ModuleCat.{max u v} R)
    (N : ringedSiteModules.{max u v} (coeffRing J B))
    (f g : scalarConstantRealization J R B α M ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (x : M),
      f.val.app U (scalarConstantGenerator J R B α M U b x) =
        g.val.app U (scalarConstantGenerator J R B α M U b x)) : f = g := by
  ext U x
  have he := scalarOver_ext J R B α M N U.unop
    ((PresheafOfModules.restrictOver B.obj U.unop).map f.val)
    ((PresheafOfModules.restrictOver B.obj U.unop).map g.val)
    (fun W b x ↦ h (op W.left) b x)
  exact congrArg (fun t ↦ t.app (op (Over.mk (𝟙 U.unop))) x) he

private lemma scalarMap_generator {V W : ModuleCat.{max u v} R} (f : V ⟶ W)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : V) :
    (scalarConstantRealizationMap J R B α f).val.app U
      (scalarConstantGenerator J R B α V U b x) =
        scalarConstantGenerator J R B α W U b (f x) := by
  have h := scalarExtension_map_tmul α ((constantModuleHomFunctor J R).map f) U b
    ((constantModuleHomUnit J R V).app U x)
  have hn := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) R).map f))
  have hx := (ConcreteCategory.congr_hom (congr_app hn U) x).symm
  change ((constantModuleHomFunctor J R).map f).val.app U
      ((constantModuleHomUnit J R V).app U x) =
    (constantModuleHomUnit J R W).app U (f x) at hx
  exact h.trans (congrArg (fun z ↦ scalarExtensionSection α
    ((constantModuleHomFunctor J R).obj W) U b z) hx)

end SheafOfModules
