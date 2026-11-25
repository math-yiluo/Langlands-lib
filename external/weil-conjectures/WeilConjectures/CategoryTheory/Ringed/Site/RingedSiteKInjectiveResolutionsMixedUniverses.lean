/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # K-injective resolutions with independent site universes

Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).
The ring universe is r, while module sections live in max c v r.
The free lifted Yoneda sheaves are precisely the sheafifications of the localized
rank-one extension presheaves. Their use preserves the generator in the source statement.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Forgetting commutativity preserves the sheaf condition, independently of the
size of the site. This supplies the underlying ring sheaf used in Mod(O).
Source: Stacks, Modules on Sites 03D7, and Sites 00VR
(blueprint: prop-pur-kinjective-resolutions-exist).
Proof: a compatible family of ring maps has the same underlying functions as a
compatible family of commutative-ring maps when its test ring is commutative. For
an arbitrary test ring, glue the images of its elements in the commutative sheaf;
uniqueness and restriction test the ring laws locally. Thus the glued function
is a ring map. Equivalently, the fully faithful inclusion of commutative rings
preserves every existing limit, including the limits of covering diagrams. -/
@[instance] theorem hasSheafCompose_commRingToRing {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by
  let F := forget₂ CommRingCat.{r} RingCat.{r}
  let G := forget RingCat.{r}
  have : PreservesLimitsOfSize.{v, max c v} F := by
    constructor
    intro K _
    constructor
    intro D
    constructor
    intro t ht
    have : PreservesLimit D (forget CommRingCat.{r}) :=
      CommRingCat.adj.rightAdjoint_preservesLimits.preservesLimitsOfShape.preservesLimit
    have htypes := isLimitOfPreserves (forget CommRingCat.{r}) ht
    have : HasLimit (D ⋙ forget CommRingCat.{r}) := ⟨⟨_, htypes⟩⟩
    have : Small.{r} (D ⋙ forget CommRingCat.{r}).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    have : Small.{r} ((D ⋙ F) ⋙ G).sections := ‹_›
    have : HasLimit (D ⋙ F) := inferInstance
    have : PreservesLimit (D ⋙ F) G :=
      preservesLimit_of_preserves_limit_cone (RingCat.limitConeIsLimit _)
        (Types.Small.limitConeIsLimit _)
    have : ReflectsLimit (D ⋙ F) G := reflectsLimit_of_reflectsIsomorphisms (D ⋙ F) G
    exact ⟨isLimitOfReflects G htypes⟩
  exact hasSheafCompose_of_preservesLimitsOfSize J

end CategoryTheory

namespace PresheafOfModules

/-- Canonical sectionwise universe transport of a module presheaf. Restrictions are
conjugated by ULift.up/down; the coefficient presheaf is unchanged.
Source: Stacks size convention 000H, used for the generator of 03EW
(blueprint: prop-pur-kinjective-resolutions-exist). -/
noncomputable def sectionUniverseLift {C : Type c} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{r}) :
    PresheafOfModules.{s} R ⥤ PresheafOfModules.{max c v r s} R where
  obj M :=
    { obj V := (ModuleCat.uliftFunctor.{max c v r s} _).obj (M.obj V)
      map {V W} f := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
          ((ModuleCat.uliftFunctor.{max c v r s} _).obj (M.obj W)))
        { toFun := fun m ↦ ULift.up (M.map f m.down)
          map_add' := fun m n ↦ congrArg ULift.up (map_add (M.map f).hom m.down n.down)
          map_smul' := fun a m ↦ congrArg ULift.up (M.map_smul f a m.down) }
      map_id V := by ext m; exact congrArg ULift.up (by simp)
      map_comp f g := by ext m; exact congrArg ULift.up (M.map_comp_apply f g m.down) }
  map f :=
    { app V := (ModuleCat.uliftFunctor.{max c v r s} _).map (f.app V)
      naturality {V W} g := by
        ext m
        exact congrArg ULift.up (CategoryTheory.congr_fun (f.naturality g) m.down) }
  map_id M := by ext V m; rfl
  map_comp f g := by ext V m; rfl

end PresheafOfModules

namespace SheafOfModules

open Classical in
private noncomputable def liftedExtensionDesc
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) (M : PresheafOfModules.{max c v r} R.obj)
    (m : M.obj (Opposite.op U)) :
    (PresheafOfModules.sectionUniverseLift R.obj).obj
      ((extensionByZeroPresheaf R U).obj (unit (R.over U))) ⟶ M where
  app V := ModuleCat.ofHom
    ((DirectSum.toModule (R.obj.obj V) (V.unop ⟶ U) (M.obj V)
      (fun φ ↦ LinearMap.toSpanSingleton _ _ (M.map φ.op m))).comp
        ULift.moduleEquiv.toLinearMap)
  naturality {V W} a := by
    ext x
    symm
    change M.map a ((DirectSum.toModule (R.obj.obj V) (V.unop ⟶ U) (M.obj V)
      (fun φ ↦ LinearMap.toSpanSingleton _ _ (M.map φ.op m))) x.down) =
      (DirectSum.toModule (R.obj.obj W) (W.unop ⟶ U) (M.obj W)
        (fun φ ↦ LinearMap.toSpanSingleton _ _ (M.map φ.op m)))
          (extensionByZeroPresheafRestrictAdd R U (unit (R.over U)) a x.down)
    induction x.down using DirectSum.induction_on with
    | zero => simp
    | of φ t =>
      change R.obj.obj V at t
      change M.map a ((DirectSum.toModule (R.obj.obj V) (V.unop ⟶ U) (M.obj V)
        (fun ψ ↦ LinearMap.toSpanSingleton _ _ (M.map ψ.op m)))
          (DirectSum.lof (R.obj.obj V) (V.unop ⟶ U)
            (fun _ ↦ R.obj.obj V) φ t)) = _
      rw [DirectSum.toModule_lof]
      dsimp [extensionByZeroPresheafRestrictAdd]
      erw [DirectSum.toAddMonoid_of]
      change M.map a (t • (M.map φ.op m : M.obj V)) =
        (DirectSum.toModule (R.obj.obj W) (W.unop ⟶ U) (M.obj W)
          (fun ψ ↦ LinearMap.toSpanSingleton _ _ (M.map ψ.op m)))
          (DirectSum.lof (R.obj.obj W) (W.unop ⟶ U)
            (fun _ ↦ R.obj.obj W) (a.unop ≫ φ) (R.obj.map a t))
      rw [DirectSum.toModule_lof]
      change M.map a (t • (M.map φ.op m : M.obj V)) =
        R.obj.map a t • (M.map (a.unop ≫ φ).op m : M.obj W)
      rw [M.map_smul, ← M.map_comp_apply]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Grothendieck abelianness, the specified free-sheaf generator, and functorial
K-injective resolutions with injective terms, without equating site universes.
Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).
Proof:
1. Form the free module on the lifted representable at each site object. Its
sections are finite linear combinations of arrows into that object, exactly the
extension-by-zero presheaf of the localized unit. Sheafification makes these a
separating family, by the free-Yoneda/sheafification adjunction. Their coproduct
is a separator. Kernels and filtered colimits are computed on underlying abelian
sheaves, where filtered colimits are exact. All index sets fit max c v r.
2. Apply the small-object construction of the source library to this Grothendieck
abelian category: factor each map M→0 functorially by the monomorphic
quasi-isomorphisms. The resulting target is K-injective, and its terms are
injective by the degreewise lifting criterion. The first factor supplies the
natural quasi-isomorphism; the construction is functorial on chain maps. -/
theorem grothendieckAbelian_and_functorial_kInjective_resolutionsMixedUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) :
    IsGrothendieckAbelian.{max c v r}
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ∧
    IsSeparator (∐ fun U : C ↦
      (PresheafOfModules.sheafification.{max c v r} (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).obj
        ((PresheafOfModules.sectionUniverseLift (((sheafCompose J
          (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).obj
          ((extensionByZeroPresheaf ((sheafCompose J
            (forget₂ CommRingCat.{r} RingCat.{r})).obj R) U).obj
              (unit (((sheafCompose J
                (forget₂ CommRingCat.{r} RingCat.{r})).obj R).over U))))) ∧
    ∃ (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤
        CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) ⟶ I),
      ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ,
        QuasiIso (C := SheafOfModules.{max c v r} ((sheafCompose J
          (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (η.app M) ∧ (I.obj M).IsKInjective ∧
          ∀ n : ℤ, Injective ((I.obj M).X n) := by
  classical
  let S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let A := SheafOfModules.{max c v r} S
  let P := fun U : C ↦ (PresheafOfModules.sectionUniverseLift S.obj).obj
    ((extensionByZeroPresheaf S U).obj (unit (S.over U)))
  have hsep : ObjectProperty.IsSeparating (.ofObj fun U : C ↦
      (PresheafOfModules.sheafification.{max c v r} (𝟙 S.obj)).obj (P U)) := by
    intro M N f g h
    apply (SheafOfModules.forget S).map_injective
    apply PresheafOfModules.hom_ext
    intro V
    obtain ⟨U⟩ := V
    let V := Opposite.op U
    ext m
    change f.val.app V m = g.val.app V m
    let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 S.obj)
    let m' : M.val.obj (Opposite.op V.unop) := m
    let a : P V.unop ⟶ (PresheafOfModules.restrictScalars (𝟙 S.obj)).obj M.val :=
      liftedExtensionDesc S V.unop _ m'
    have he := h _ (ObjectProperty.ofObj_apply _ V.unop) ((adj.homEquiv _ _).symm a)
    have he' := congrArg (adj.homEquiv _ _) he
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply] at he'
    let x : (P V.unop).obj V :=
      ULift.up (DirectSum.of (fun _ : V.unop ⟶ V.unop ↦ S.obj.obj V) (𝟙 _) 1)
    have hm := CategoryTheory.congr_fun (congrArg (fun k ↦ k.app V) he') x
    have ha : a.app V x = m := by
      change (DirectSum.toModule (S.obj.obj V) (V.unop ⟶ V.unop) (M.val.obj V)
        (fun φ ↦ LinearMap.toSpanSingleton _ _ (M.val.map φ.op m')))
          (DirectSum.lof (S.obj.obj V) (V.unop ⟶ V.unop)
            (fun _ ↦ S.obj.obj V) (𝟙 _) 1) = m
      rw [DirectSum.toModule_lof]
      simp [LinearMap.toSpanSingleton_apply, m']
    change f.val.app V (a.app V x) = g.val.app V (a.app V x) at hm
    simpa only [ha] using hm
  have hgen := hsep.isSeparator_coproduct
  have : HasFilteredColimitsOfSize.{max c v r, max c v r} A :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{max c v r, max c v r} A :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (toSheaf.{max c v r} S)⟩
  have : HasSeparator A := ⟨_, hgen⟩
  have hGroth : IsGrothendieckAbelian.{max c v r} A := {}
  let _ := hGroth
  refine ⟨hGroth, hgen, CochainComplex.kInjectiveResolutionFunctor.{max c v r} A,
    CochainComplex.toKInjectiveResolution.{max c v r} A, ?_⟩
  intro M
  exact ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2,
    inferInstance, fun n ↦ inferInstance⟩

end SheafOfModules
