/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Flat-term successive quotient tensor sequences

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks Project, Modules on Sites, Tags 03DA, 03EK, 03ER.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r wB wR wS wPrev wN wOne
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

section SheafificationAPI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}] {R : Sheaf J RingCat.{r}}

private theorem moduleSheafification_unit_naturality
    {P Q : PresheafOfModules.{r} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫
        ((PresheafOfModules.sheafification.{r} (𝟙 R.obj)).map f).val =
      f ≫ (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app Q := by
  exact ((PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 R.obj)).unit.naturality f).symm

private theorem moduleSheafification_hom_ext
    (P : PresheafOfModules.{r} R.obj) (A : SheafOfModules.{r} R)
    {f g : (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj P ⟶ A}
    (h : (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫ f.val =
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫ g.val) : f = g := by
  exact (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 R.obj)).injective h

end SheafificationAPI

section

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]

section Models
variable {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

end Models

section FlatTensorData

variable {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

end FlatTensorData

end

namespace SuccessiveQuotientCoefficients

variable {R : Type*} [CommRing R] (t : R) (n : ℕ) (hn : 1 ≤ n)
private abbrev I (k : ℕ) : Ideal R := Ideal.span {t ^ k}
include hn
private theorem mul_mem (x : R) (hx : x ∈ I t (n - 1)) : t * x ∈ I t n := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hx
  apply Ideal.mem_span_singleton.2
  refine ⟨y, ?_⟩
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
private def a : R ⧸ I t (n - 1) →ₗ[R] R ⧸ I t n :=
  (I t (n - 1)).mapQ (I t n) (LinearMap.mulLeft R t) (mul_mem t n hn)
private theorem ideal_le : I t n ≤ I t 1 := by
  apply Ideal.span_le.2
  intro x hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact Ideal.mem_span_singleton.2 (pow_dvd_pow t hn)
private def b : R ⧸ I t n →ₗ[R] R ⧸ I t 1 :=
  (I t n).mapQ (I t 1) LinearMap.id (ideal_le t n hn)
private theorem zero_comp : (b t n hn).comp (a t n hn) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (I t 1) (t * x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.2 (by simp)
end SuccessiveQuotientCoefficients

section LeftTensorAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {B : Sheaf J CommRingCat.{r}}

private def leftTensorPresheaf
    (N : PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat) where
  obj M := siteTensorPresheaf N M
  map f := siteTensorSecondMap N f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl

private def leftTensorSheaf
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  forget _ ⋙ leftTensorPresheaf N.val ⋙ PresheafOfModules.sheafification.{r} (𝟙 _)

private def leftTensorSheafMap
    {N N' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    (f : N ⟶ N') : leftTensorSheaf N ⟶ leftTensorSheaf N' where
  app M := (siteSheafTensorRight M).map f
  naturality {_M _M'} g := (siteSheafTensorSecondMap_naturality f g).symm

private theorem leftTensorSheafMap_comp
    {N N' N'' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    (f : N ⟶ N') (g : N' ⟶ N'') :
    leftTensorSheafMap (f ≫ g) = leftTensorSheafMap f ≫ leftTensorSheafMap g := by
  apply NatTrans.ext
  funext M
  exact (siteSheafTensorRight M).map_comp f g

private theorem leftTensorSheafMap_zero
    (N N' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    leftTensorSheafMap (0 : N ⟶ N') = 0 := by
  apply NatTrans.ext
  funext M
  exact (siteSheafTensorRight M).map_zero N N'

private theorem tensorMap_tmul
    {N N' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    (f : N ⟶ N')
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (U : Cᵒᵖ) (y : N.val.obj U) (x : M.val.obj U) :
    ((siteSheafTensorRight M).map f).val.app U (siteSheafTensorTmul N M U y x) =
      siteSheafTensorTmul N' M U (f.val.app U y) x := by
  exact congrArg (fun k ↦ (k.app U) (y ⊗ₜ[B.obj.obj U] x))
    (moduleSheafification_unit_naturality
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      (siteTensorHom f.val M.val))

end LeftTensorAuxiliary

section RestrictedTensorAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

private def restrictedTensorPresheafIso {R S : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    siteTensorPresheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let e :
        (siteTensorPresheaf
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val M.val).obj V ≃ₗ[
              R.obj.obj V]
          ((PresheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
              (changeOfRingsPresheaf φ M)).obj V :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro b z
          induction z using TensorProduct.inductionOn with
          | tmul s x => rfl
          | add z z' hz hz' => simpa only [smul_add] using congrArg₂ (· + ·) hz hz' }
    exact e.toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      let : Module (R.obj.obj W)
          ((ModuleCat.restrictScalars
            (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
              (M.val.obj W)) := inferInstanceAs (Module (R.obj.obj W) (M.val.obj W))
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem sheafificationComparison {R : Sheaf J RingCat.{r}}
    (P : PresheafOfModules.{r} R.obj) (A : SheafOfModules.{r} R)
    (φ : P ⟶ A.val)
    [hinj : PresheafOfModules.IsLocallyInjective J φ]
    [hsurj : PresheafOfModules.IsLocallySurjective J φ] :
    ∃ e : (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj P ≅ A,
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫
        e.hom.val = φ := by
  let S := (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj P
  let η : P ⟶ S.val := (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P
  let g : S ⟶ A := (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 R.obj)).symm φ
  have hg : η ≫ g.val = φ := by
    exact (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 R.obj)).apply_symm_apply φ
  let f : A ⟶ S := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
    (f := φ) S.isSheaf).symm η⟩
  have hf : φ ≫ f.val = η := by
    exact (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := φ) S.isSheaf).apply_symm_apply η
  have hfg : f ≫ g = 𝟙 A := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := φ) A.isSheaf).injective
    change φ ≫ (f.val ≫ g.val) = φ ≫ 𝟙 A.val
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 S := by
    apply moduleSheafification_hom_ext P S
    change η ≫ (g.val ≫ f.val) = η ≫ 𝟙 S.val
    rw [← Category.assoc, hg, hf, Category.comp_id]
  exact ⟨⟨g, f, hgf, hfg⟩, hg⟩

end RestrictedTensorAuxiliary

section OrdinaryExtensionAuxiliary

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

private def ordinaryExtensionPresheaf (a : R ⟶ S) :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S).obj where
  obj := changeOfRingsPresheaf a
  map f :=
    { app U := (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality a _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private def ordinaryExtension (a : R ⟶ S) :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S) :=
  ordinaryExtensionPresheaf a ⋙ PresheafOfModules.sheafification.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)

variable [HasSheafify J AddCommGrpCat.{r}]

end OrdinaryExtensionAuxiliary

section TensorExtensionNaturalityAuxiliary

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]

private def tensorExtensionUnit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
        leftTensorPresheaf
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⟶
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)) ⋙
          forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  app M := (restrictedTensorPresheafIso a M).hom ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
          (changeOfRingsPresheaf a M))
  naturality {M N} f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s x
    change S.obj.obj U at s
    exact (congrArg (fun k ↦ (k.app U)
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
        ((PresheafOfModules.sheafificationAdjunction.{r}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.naturality
            ((ordinaryExtensionPresheaf a).map f)))

private instance tensorExtensionUnit_injective {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PresheafOfModules.IsLocallyInjective J ((tensorExtensionUnit a).app M) := by
  change Presheaf.IsLocallyInjective J
    ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom ≫
      toSheafify J (changeOfRingsPresheaf a M).presheaf)
  have : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom) :=
    inferInstance
  have : Presheaf.IsLocallyInjective J
      (toSheafify J (changeOfRingsPresheaf a M).presheaf) := inferInstance
  infer_instance

private instance tensorExtensionUnit_surjective {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PresheafOfModules.IsLocallySurjective J ((tensorExtensionUnit a).app M) := by
  change Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom ≫
      toSheafify J (changeOfRingsPresheaf a M).presheaf)
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom) :=
    inferInstance
  have : Presheaf.IsLocallySurjective J
      (toSheafify J (changeOfRingsPresheaf a M).presheaf) := inferInstance
  infer_instance

private theorem exists_extensionTensorIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (leftTensorSheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))).obj M ≅
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj M,
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
          e.hom.val = (tensorExtensionUnit a).app M := by
  exact sheafificationComparison
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    _ _ ((tensorExtensionUnit a).app M)
    (hinj := tensorExtensionUnit_injective a M)
    (hsurj := tensorExtensionUnit_surjective a M)

private def extensionTensorIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (leftTensorSheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))).obj M ≅
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj M :=
  (exists_extensionTensorIso a M).choose

private theorem extensionTensorIso_unit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
        (extensionTensorIso a M).hom.val = (tensorExtensionUnit a).app M :=
  (exists_extensionTensorIso a M).choose_spec

private def tensorExtensionIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    leftTensorSheaf
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≅
      ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) :=
  NatIso.ofComponents (extensionTensorIso a) (by
    intro M N f
    let adj := PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let N₀ := (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    let T := leftTensorPresheaf (B := R) N₀.val
    apply moduleSheafification_hom_ext
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (T.obj M.val) _
    have hη : adj.unit.app (T.obj M.val) ≫ (leftTensorSheaf N₀ |>.map f).val =
        T.map f.val ≫ adj.unit.app (T.obj N.val) :=
      moduleSheafification_unit_naturality
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (T.map f.val)
    change adj.unit.app (T.obj M.val) ≫
        (leftTensorSheaf N₀ |>.map f).val ≫ (extensionTensorIso a N).hom.val =
      adj.unit.app (T.obj M.val) ≫ (extensionTensorIso a M).hom.val ≫
        ((ordinaryExtension a ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).map f).val
    have hM := extensionTensorIso_unit a M
    have hN := extensionTensorIso_unit a N
    change adj.unit.app (T.obj M.val) ≫ (extensionTensorIso a M).hom.val = _ at hM
    change adj.unit.app (T.obj N.val) ≫ (extensionTensorIso a N).hom.val = _ at hN
    rw [← Category.assoc, hη, Category.assoc, hN, ← Category.assoc, hM]
    exact (tensorExtensionUnit a).naturality f)

private theorem extensionTensorIso_tmul {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((extensionTensorIso a M).hom.val.app U)
      (siteSheafTensorTmul
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M U s x) =
      (toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) := by
  exact congrArg (fun k ↦ (k.app U)
    (s ⊗ₜ[R.obj.obj U] x)) (extensionTensorIso_unit a M)

variable [EssentiallySmall.{r} C]

variable [HasSheafify J AddCommGrpCat.{r}]

end TensorExtensionNaturalityAuxiliary

section ExactRestrictionAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

-- This is the general-ring version of systemScalarRestriction_exact. Both composites
-- with toSheaf retain the same underlying abelian sheaf and every morphism.
private theorem restriction_exact {R S : Sheaf J RingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{r} a) ∧
      PreservesFiniteColimits (restrictScalars.{r} a) := by
  let F := restrictScalars.{r} a
  have : PreservesFiniteLimits (F ⋙ toSheaf R) := by
    change PreservesFiniteLimits (toSheaf S)
    infer_instance
  have : PreservesFiniteColimits (F ⋙ toSheaf R) := by
    change PreservesFiniteColimits (toSheaf S)
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf R)⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem restriction_faithful {R S : Sheaf J RingCat.{r}} (a : R ⟶ S) :
    (restrictScalars.{r} a).Faithful := by
  let F := restrictScalars.{r} a
  have : (F ⋙ toSheaf R).Faithful := by
    change (toSheaf S).Faithful
    infer_instance
  exact Functor.Faithful.of_comp F (toSheaf R)

private def liftRestrictedHom {R S : Sheaf J RingCat.{r}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective J a.hom] {M N : SheafOfModules.{r} S}
    (f : (restrictScalars a).obj M ⟶ (restrictScalars a).obj N) : M ⟶ N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a.hom N.isSheaf).symm f.val⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem restrict_liftRestrictedHom {R S : Sheaf J RingCat.{r}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective J a.hom] {M N : SheafOfModules.{r} S}
    (f : (restrictScalars a).obj M ⟶ (restrictScalars a).obj N) :
    (restrictScalars a).map (liftRestrictedHom a f) = f := by
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem restriction_full {R S : Sheaf J RingCat.{r}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective J a.hom] : (restrictScalars.{r} a).Full where
  map_surjective f := ⟨liftRestrictedHom a f, restrict_liftRestrictedHom a f⟩

private def restrictionComp {R S T : Sheaf J RingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    restrictScalars.{r} b ⋙ restrictScalars a ≅ restrictScalars c := by
  have hU (U : Cᵒᵖ) : (b.hom.app U).hom.comp (a.hom.app U).hom =
      (c.hom.app U).hom :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (b.hom.app U).hom
        (c.hom.app U).hom (hU U).symm (M.val.obj U)).symm) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

end ExactRestrictionAuxiliary

section EndpointModelAuxiliary

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

end EndpointModelAuxiliary

section CochainAuxiliary

variable {A : Type*} [Category A] [Abelian A]
  {D : Type*} [Category D] [Abelian D]
  (E₁ E₂ E₃ : A ⥤ D) [E₁.Additive] [E₂.Additive] [E₃.Additive]
  (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (wab : a ≫ b = 0)
  (P : CochainComplex A ℤ)

end CochainAuxiliary

private theorem lift_shortExact
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    (F : A ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X₁ X₂ X₃ : A} (a : F.obj X₁ ⟶ F.obj X₂) (b : F.obj X₂ ⟶ F.obj X₃)
    (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) :
    ∃ (α : X₁ ⟶ X₂) (β : X₂ ⟶ X₃) (hαβ : α ≫ β = 0),
      (ShortComplex.mk α β hαβ).ShortExact ∧ F.map α = a ∧ F.map β = b := by
  let α := F.preimage a
  let β := F.preimage b
  have hαβ : α ≫ β = 0 := by
    apply F.map_injective
    simpa only [α, β, Functor.map_comp, Functor.map_preimage, Functor.map_zero] using hab
  let S := ShortComplex.mk α β hαβ
  have hSF : (S.map F).ShortExact := by
    change (ShortComplex.mk (F.map α) (F.map β) _).ShortExact
    simpa only [α, β, Functor.map_preimage] using hS
  have hSA : S.ShortExact := by
    exact { exact := (S.exact_map_iff_of_faithful F).1 hSF.exact
            mono_f := F.mono_of_mono_map hSF.mono_f
            epi_g := F.epi_of_epi_map hSF.epi_g }
  exact ⟨α, β, hαβ, hSA, F.map_preimage a, F.map_preimage b⟩

section FlatTensorAssembly

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

end FlatTensorAssembly

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (B : Sheaf J CommRingCat.{r})
  (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)

private instance quotientLocallyBijectiveCommRing :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r}
      (CategoryTheory.forget CommRingCat.{r}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

end SheafOfModules
