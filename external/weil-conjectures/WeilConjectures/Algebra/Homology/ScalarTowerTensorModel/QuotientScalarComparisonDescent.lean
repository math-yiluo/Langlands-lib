/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.CompatibleCoefficientTower
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.Strict.StrictRoosHomotopyFunctor
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Scalar augmentation and its derived descent

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks Project, Tags 03EK, 014E, 08TC, 06YS, 06YT, 06XN and 05S9.
(blueprint: lem-pur-quotient-scalar-comparison-descent)

The tensor factors in the change-of-rings API are written scalar first. Natural index
`n` denotes positive level `n + 1`. Presentation isomorphisms fix the actual sheafified
tensors and their maps; they are not additional hypotheses in the existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]

namespace SheafOfModules.ScalarComparisonProof

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]

private noncomputable abbrev res {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

variable {R S T : Sheaf J CommRingCat.{u}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
include hq in
private theorem coefficient_comp (U : Cᵒᵖ) (x : R.obj.obj U) :
    q.hom.app U (f.hom.app U x) = g.hom.app U x :=
  ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hq) x

private noncomputable def sectionMap (U : Cᵒᵖ) :
    (changeOfRingsPresheaf f M).obj U ⟶
      (ModuleCat.restrictScalars (q.hom.app U).hom).obj
        ((changeOfRingsPresheaf g M).obj U) := by
  letI : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (f.hom.app U).hom
  letI : Module (R.obj.obj U) (T.obj.obj U) := Module.compHom _ (g.hom.app U).hom
  let h : S.obj.obj U →ₗ[R.obj.obj U] T.obj.obj U :=
    { toFun := q.hom.app U
      map_add' := map_add _
      map_smul' := fun x s ↦ by
        change q.hom.app U (f.hom.app U x * s) = g.hom.app U x * q.hom.app U s
        rw [map_mul, coefficient_comp f g q hq] }
  exact ModuleCat.ofHom
    (X := (changeOfRingsPresheaf f M).obj U)
    (Y := (ModuleCat.restrictScalars (q.hom.app U).hom).obj
      ((changeOfRingsPresheaf g M).obj U))
    { toFun := TensorProduct.map h (LinearMap.id : M.val.obj U →ₗ[R.obj.obj U] M.val.obj U)
      map_add' := map_add _
      map_smul' := fun s z ↦ by
        induction z using TensorProduct.inductionOn with
        | tmul t x =>
          change S.obj.obj U at t
          change q.hom.app U (s * t) ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x =
            (q.hom.app U s * q.hom.app U t) ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x
          rw [map_mul]
        | add z w hz hw => simp only [smul_add, map_add, hz, hw] }

private theorem sectionMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionMap f g q hq M U (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x) =
      (show (changeOfRingsPresheaf g M).obj U from
        q.hom.app U s ⊗ₜ[R.obj.obj U,(g.hom.app U).hom] x) := rfl

section

local instance {A : Sheaf J CommRingCat.{u}}
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    Module (A.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.map i).hom).obj
          (N.val.obj V)) :=
  inferInstanceAs (Module (A.obj.obj V) (N.val.obj V))

private theorem restriction_tmul {A B : Sheaf J CommRingCat.{u}} (c : A ⟶ B)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : B.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsPresheaf c N).map i (s ⊗ₜ[A.obj.obj U,(c.hom.app U).hom] x) =
      B.obj.map i s ⊗ₜ[A.obj.obj V,(c.hom.app V).hom] N.val.map i x :=
  Classical.choose_spec (exists_changeOfRingsMap c N i) s x

end

private noncomputable def presheafMap :
    changeOfRingsPresheaf f M ⟶
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map q).hom).obj (changeOfRingsPresheaf g M) where
  app := sectionMap f g q hq M
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change sectionMap f g q hq M V ((changeOfRingsPresheaf f M).map i
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) =
      (changeOfRingsPresheaf g M).map i
        (sectionMap f g q hq M U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x))
    rw [restriction_tmul, sectionMap_tmul, sectionMap_tmul, restriction_tmul]
    simp only [map_one]

private noncomputable def sheafMap : changeOfRings f M ⟶ (res q).obj (changeOfRings g M) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).symm
    (presheafMap f g q hq M ≫
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map q).hom).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
              (changeOfRingsPresheaf g M)))

private noncomputable def tensorSection (c : R ⟶ S)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRings c N).val.obj U :=
  (toSheafify J (changeOfRingsPresheaf c N).presheaf).app U
    (s ⊗ₜ[R.obj.obj U,(c.hom.app U).hom] x)

include f g q hq M in
private theorem sheafMap_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (sheafMap f g q hq M).val.app U (tensorSection f M U s x) =
      tensorSection g M U (q.hom.app U s) x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (F := (res q).obj (changeOfRings g M))
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).apply_symm_apply
      (presheafMap f g q hq M ≫
        (PresheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat RingCat)).map q).hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
                (changeOfRingsPresheaf g M)))
  exact congrArg (fun k ↦ k.app U (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) h

private theorem map_tensorSection
    {N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsHom f M a).val.app U (tensorSection f M U s x) =
      tensorSection f N U s (a.val.app U x) := by
  let k : changeOfRingsPresheaf f M ⟶ changeOfRingsPresheaf f N :=
    { app := fun V ↦ (ModuleCat.extendScalars (f.hom.app V).hom).map (a.val.app V)
      naturality := changeOfRingsHom_naturality f M a }
  let z : (changeOfRingsPresheaf f M).presheaf.obj U :=
    s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x
  have hn := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map k)
  have h := congrArg (fun η ↦ (η.app U).hom z) hn
  change (toSheafify J (changeOfRingsPresheaf f N).presheaf).app U
      ((ModuleCat.extendScalars (f.hom.app U).hom).map (a.val.app U)
        (s ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) = _ at h
  erw [ModuleCat.ExtendScalars.map_tmul] at h
  exact h.symm

end SheafOfModules.ScalarComparisonProof

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} {B : ℕ → Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T

/-- Presentations of the two ordinary tensor functors, with their maps fixed on tensors.
Source: Stacks 03EK and the strict tower construction of Stacks 08TC
(blueprint: lem-pur-quotient-scalar-comparison-descent).
These fields package the specified functors, including their canonical transition maps. -/
structure ScalarTowerTensorModel (φ : R ⟶ S) (c : ∀ n, S ⟶ B n)
    (b : ∀ n, B (n + 1) ⟶ B n) where
  E : ringedSiteModules.{u} (𝓡 R) ⥤
    ringedSiteModules.{u} (𝓡 S)
  V : ringedSiteModules.{u} (𝓡 R) ⥤
    (ℕᵒᵖ ⥤ ringedSiteModules.{u} (𝓡 S))
  E_add : E.Additive
  V_add : V.Additive
  eE : ∀ M, E.obj M ≅ changeOfRings φ M
  eV : ∀ M n, (V.obj M).obj (op n) ≅
    (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (c n))).obj
        (changeOfRings (φ ≫ c n) M)
  E_map : ∀ {M N} (f : M ⟶ N),
    (eE M).inv ≫ E.map f ≫ (eE N).hom = changeOfRingsHom φ M f
  V_map : ∀ {M N} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj U) (z : (B n).obj.obj U),
    (((eV M n).inv ≫ (V.map f).app (op n) ≫ (eV N n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf (φ ≫ c n) M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)) =
        (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) N).presheaf).app U
          (z ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] f.val.app U x)
  transition : ∀ M (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U)
    (z : (B (n + 1)).obj.obj U),
    (((eV M (n + 1)).inv ≫ (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫
        (eV M n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf (φ ≫ c (n + 1)) M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U, ((φ ≫ c (n + 1)).hom.app U).hom] x)) =
        (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) M).presheaf).app U
          ((((b n).hom.app U) z) ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)

attribute [instance] ScalarTowerTensorModel.E_add ScalarTowerTensorModel.V_add

namespace ScalarTowerTensorModel

variable {φ : R ⟶ S} {c : ∀ n, S ⟶ B n} {b : ∀ n, B (n + 1) ⟶ B n}
  (M : ScalarTowerTensorModel φ c b)

/-- Ordinary extension of scalars, applied termwise to complexes.
Source: Stacks 03EK (blueprint: lem-pur-quotient-scalar-comparison-descent). -/
abbrev F := M.E.mapHomologicalComplex (ComplexShape.up ℤ)

variable [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]

/-- The actual shifted product cone of the strict coefficient tensor tower.
Source: Stacks 014E and 08TC (blueprint: lem-pur-quotient-scalar-comparison-descent). -/
abbrev G := M.V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ roosF

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]

end ScalarTowerTensorModel

omit [EssentiallySmall.{u} C] in
private lemma tensor_generator_ext (φ : R ⟶ S)
    (A : ringedSiteModules.{u} (𝓡 R)) (N : ringedSiteModules.{u} (𝓡 S))
    (f g : changeOfRings φ A ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : A.val.obj U) (s : S.obj.obj U),
      f.val.app U ((toSheafify J (changeOfRingsPresheaf φ A).presheaf).app U
        (s ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      g.val.app U ((toSheafify J (changeOfRingsPresheaf φ A).presheaf).app U
        (s ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := 𝓡 S) (𝟙 _)
  apply (adj.homEquiv (changeOfRingsPresheaf φ A) N).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U x 1

private def scalarIdPresheafIso (A : ringedSiteModules.{u} (𝓡 R)) :
    A.val ≅ changeOfRingsPresheaf (𝟙 R) A := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (A.val.obj U)).symm) ?_
  intro U V f
  ext x
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (A.val.obj V)
      (A.val.map f x) =
    changeOfRingsMap (𝟙 R) A f
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (A.val.obj U) x)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) A f) (1 : R.obj.obj U) x).symm

private def scalarIdIso (A : ringedSiteModules.{u} (𝓡 R)) :
    changeOfRings (𝟙 R) A ≅ A := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := 𝓡 R) (𝟙 _)
  let e := (scalarIdPresheafIso A).symm
  let a := (adj.homEquiv _ A).symm e.hom
  have ha : adj.homEquiv _ A a = e.hom := Equiv.apply_symm_apply _ _
  refine ⟨a, ⟨e.inv ≫ adj.unit.app _⟩, ?_, ?_⟩
  · apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right, ha]
    change e.hom ≫ (e.inv ≫ adj.unit.app _) = _
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact (adj.homEquiv_id _).symm
  · apply SheafOfModules.hom_ext
    change (e.inv ≫ adj.unit.app _) ≫ a.val = 𝟙 _
    rw [Category.assoc]
    change e.inv ≫ adj.homEquiv _ A a = _
    rw [ha, e.inv_hom_id]

omit [EssentiallySmall.{u} C] in
private lemma scalarIdIso_tmul (A : ringedSiteModules.{u} (𝓡 R))
    (U : Cᵒᵖ) (x : A.val.obj U) (r : R.obj.obj U) :
    (scalarIdIso A).hom.val.app U
      ((toSheafify J (changeOfRingsPresheaf (𝟙 R) A).presheaf).app U
        (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x)) = r • x := by
  have h : (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
      (changeOfRingsPresheaf (𝟙 R) A) ≫ (scalarIdIso A).hom.val =
      (scalarIdPresheafIso A).inv := by
    exact (PresheafOfModules.sheafificationAdjunction (R := 𝓡 R) (𝟙 _)).homEquiv
      (changeOfRingsPresheaf (𝟙 R) A) A |>.apply_symm_apply _
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
    (changeOfRingsPresheaf (𝟙 R) A) ≫ (scalarIdIso A).hom.val).app U
      (r ⊗ₜ[R.obj.obj U,((𝟙 R : R ⟶ R).hom.app U).hom] x) = r • x
  rw [h]
  change (ModuleCat.extendScalarsId (R.obj.obj U)).hom.app (A.val.obj U)
    (r ⊗ₜ[R.obj.obj U,((𝟙 R : R ⟶ R).hom.app U).hom] x) = r • x
  rfl

omit [EssentiallySmall.{u} C] in
private lemma scalarIdIso_naturality {A N : ringedSiteModules.{u} (𝓡 R)}
    (f : A ⟶ N) :
    changeOfRingsHom (𝟙 R) A f ≫ (scalarIdIso N).hom =
      (scalarIdIso A).hom ≫ f := by
  apply tensor_generator_ext
  intro U x r
  have hn := toSheafify_naturality J
    ((PresheafOfModules.toPresheaf _).map
      ({ app := fun U ↦ (ModuleCat.extendScalars
          ((𝟙 R : R ⟶ R).hom.app U).hom).map (f.val.app U)
         naturality := changeOfRingsHom_naturality (𝟙 R) A f } :
        changeOfRingsPresheaf (𝟙 R) A ⟶ changeOfRingsPresheaf (𝟙 R) N))
  change (scalarIdIso N).hom.val.app U
    ((changeOfRingsHom (𝟙 R) A f).val.app U _) = _
  rw [show (changeOfRingsHom (𝟙 R) A f).val.app U
      ((toSheafify J (changeOfRingsPresheaf (𝟙 R) A).presheaf).app U
        (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x)) =
    (toSheafify J (changeOfRingsPresheaf (𝟙 R) N).presheaf).app U
      (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] f.val.app U x) from by
        exact ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app U) hn).symm _]
  rw [scalarIdIso_tmul]
  change _ = f.val.app U ((scalarIdIso A).hom.val.app U _)
  rw [scalarIdIso_tmul]
  exact ((f.val.app U).hom.map_smul r x).symm

omit [EssentiallySmall.{u} C] in
open ScalarComparisonProof

end SheafOfModules
