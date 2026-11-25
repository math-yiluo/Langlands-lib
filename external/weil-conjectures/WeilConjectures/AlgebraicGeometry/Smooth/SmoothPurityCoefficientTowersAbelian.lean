/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# The abelian category of smooth-purity coefficient towers

Source: blueprint main-20261015, chap-Smooth-purity, prose-09-21,
`sk-def-sp-coefficient-towers-abelian.md`, clauses (1)--(3); Bhatt--Scholze,
The pro-etale topology for schemes, Definition 3.5.3
(blueprint: prose-09-21).

The input category is the recorded `spCoefficientTowers`, not a tower of modules
with one fixed coefficient ring. The equivalence below only uncurries its product-site
module presheaves into the already defined strict semilinear systems. Its four
normalizations fix every section module, restriction, transition and morphism.
The existing scalar models and their normalized associators specify the derived
scalar extensions. All positive levels are represented: index n means level n+1.

## Main statements

- `sp_coefficient_towers_abelian`: Grothendieck abelianness, levelwise kernels,
  cokernels and filtered colimits, exact derived evaluation, and natural reduction
  maps induced by the strict transitions, with identity and composition compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

-- Use the existing larger-coefficient transport while elaborating these declarations.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

attribute [local instance high] SheafOfModules.systemRingHasDerived
attribute [local irreducible] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CoefficientTowerProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v w
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

private abbrev rings := B ⋙ sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})

private abbrev coefficients (R : ℕᵒᵖ ⥤ Sheaf J RingCat.{w}) : (ℕ × C)ᵒᵖ ⥤ RingCat.{w} :=
  (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
    Functor.uncurry.obj (R ⋙ sheafToPresheaf J RingCat.{w})

private def condition (R : ℕᵒᵖ ⥤ Sheaf J RingCat.{w}) :
    ObjectProperty (PresheafOfModules.{w} (coefficients R)) :=
  fun M ↦ ∀ n : ℕ, Presheaf.IsSheaf J ((Prod.sectR n C).op ⋙ M.presheaf)

private abbrev Towers (R : ℕᵒᵖ ⥤ Sheaf J RingCat.{w}) := (condition R).FullSubcategory

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem verticalRingMap (R : ℕᵒᵖ ⥤ Sheaf J RingCat.{w}) (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (coefficients R).map (Prod.mkHom (𝟙 n) f.unop).op =
      (R.obj (op n)).obj.map f := by
  let F := R ⋙ sheafToPresheaf J RingCat.{w}
  change (F.map (𝟙 (op n))).app U ≫ (F.obj (op n)).map f = (F.obj (op n)).map f
  rw [F.map_id]
  simp

set_option backward.defeqAttrib.useBackward true in
@[implicit_reducible]
private def levelVal (R : ℕᵒᵖ ⥤ Sheaf J RingCat.{w}) (M : Towers R) (n : ℕ) :
    PresheafOfModules.{w} (R.obj (op n)).obj where
  obj U := M.obj.obj (op (n, U.unop))
  map {U V} f := ModuleCat.ofHom
    (X := M.obj.obj (op (n, U.unop)))
    (Y := (ModuleCat.restrictScalars ((R.obj (op n)).obj.map f).hom).obj
      (M.obj.obj (op (n, V.unop))))
    { toFun := fun x ↦ M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := by
        intro r x
        change M.obj.map (Prod.mkHom (𝟙 n) f.unop).op (r • x) =
          (R.obj (op n)).obj.map f r • M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x
        rw [M.obj.map_smul]
        exact congrArg (fun a ↦ a • M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x)
          (ConcreteCategory.congr_hom (verticalRingMap R n f) r) }
  map_id := by
    intro U
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x ↦ ?_))
    change M.obj.map (𝟙 (op (n, U.unop))) x = x
    rw [M.obj.map_id]
    rfl
  map_comp := by
    intro U V W f g
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x ↦ ?_))
    change M.obj.map (Prod.mkHom (𝟙 n) (f ≫ g).unop).op x =
      M.obj.map (Prod.mkHom (𝟙 n) g.unop).op
        (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x)
    rw [← M.obj.map_comp_apply]
    apply M.obj.congr_map_apply
    apply Quiver.Hom.unop_inj
    ext <;> simp

@[implicit_reducible]
private def level (M : Towers (rings B)) (n : ℕ) : systemLevel B n where
  val := levelVal (rings B) M n
  isSheaf := by
    let e : (levelVal (rings B) M n).presheaf ≅ (Prod.sectR n C).op ⋙ M.obj.presheaf :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intros
        ext x
        rfl)
    exact (Presheaf.isSheaf_of_iso_iff e).2 (M.property n)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] in
private theorem horizontalRingMap {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
    (coefficients (rings B)).map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      ((rings B).map (homOfLE h).op).hom.app U := by
  let F := rings B ⋙ sheafToPresheaf J RingCat.{w}
  change (F.map (homOfLE h).op).app U ≫
    (F.obj (op m)).map (𝟙 U) = (F.map (homOfLE h).op).app U
  rw [(F.obj (op m)).map_id U, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private def transition (M : Towers (rings B)) {m n : ℕ} (h : m ≤ n) :
    level B M n ⟶ (systemRestriction B h).obj (level B M m) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (level B M n).val.obj U)
        (Y := ((systemRestriction B h).obj (level B M m)).val.obj U)
        { toFun := fun x ↦ M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x
          map_add' := fun x y ↦ map_add _ x y
          map_smul' := by
            intro r x
            change M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op (r • x) =
              ((rings B).map (homOfLE h).op).hom.app U r •
                M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x
            rw [M.obj.map_smul]
            exact congrArg (fun a ↦
              a • M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
              (ConcreteCategory.congr_hom (horizontalRingMap B h U) r) }
      naturality := by
        intro U V f
        ext x
        change M.obj.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
          (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x) =
          M.obj.map (Prod.mkHom (𝟙 m) f.unop).op
            (M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
        rw [← M.obj.map_comp_apply, ← M.obj.map_comp_apply]
        apply M.obj.congr_map_apply
        apply Quiver.Hom.unop_inj
        ext <;> simp }

set_option backward.isDefEq.respectTransparency false in
private def system (M : Towers (rings B)) : StrictRingSystem B where
  level := level B M
  transition := transition B M
  identity := by
    intro n U x
    change M.obj.map (𝟙 (op (n, U.unop))) x = x
    rw [M.obj.map_id]
    rfl
  compose := by
    intro r m n h k U x
    change M.obj.map (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op x =
      M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
        (M.obj.map (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op x)
    rw [← M.obj.map_comp_apply]
    apply M.obj.congr_map_apply
    apply Quiver.Hom.unop_inj
    ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private def curry : Towers (rings B) ⥤ StrictRingSystem B where
  obj := system B
  map f :=
    { app := fun n ↦ ⟨
        { app := fun U ↦ f.hom.app (op (n, U.unop))
          naturality := by
            intro U V a
            ext x
            exact PresheafOfModules.naturality_apply f.hom
              (Prod.mkHom (𝟙 n) a.unop).op x }⟩
      comm := by
        intro m n h
        ext U x
        exact (PresheafOfModules.naturality_apply f.hom
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x).symm }
  map_id M := by rfl
  map_comp f g := by rfl

set_option backward.isDefEq.respectTransparency false in
private def uncurryVal (M : StrictRingSystem B) :
    PresheafOfModules.{w} (coefficients (rings B)) where
  obj X := (M.level X.unop.1).val.obj (op X.unop.2)
  map {X Y} f := ModuleCat.ofHom
    (X := (M.level X.unop.1).val.obj (op X.unop.2))
    (Y := (ModuleCat.restrictScalars ((coefficients (rings B)).map f).hom).obj
      ((M.level Y.unop.1).val.obj (op Y.unop.2)))
    { toFun := fun x ↦ (M.level Y.unop.1).val.map f.unop.2.op
        ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)
      map_add' := by intros; simp
      map_smul' := by
        intro r x
        have h := ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2)).hom.map_smul r x
        change (M.level Y.unop.1).val.map f.unop.2.op
          ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) (r • x)) = _
        rw [h]
        change (M.level Y.unop.1).val.map f.unop.2.op
          (((rings B).map (homOfLE (leOfHom f.unop.1)).op).hom.app (op X.unop.2) r •
            (show (M.level Y.unop.1).val.obj (op X.unop.2) from
              (M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)) = _
        rw [(M.level Y.unop.1).val.map_smul]
        rfl }
  map_id X := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x ↦ ?_))
    change (M.level X.unop.1).val.map (𝟙 (op X.unop.2))
      ((M.transition (Nat.le_refl X.unop.1)).val.app (op X.unop.2) x) = x
    rw [M.identity]
    rw [(M.level X.unop.1).val.map_id]
    rfl
  map_comp {X Y Z} f g := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x ↦ ?_))
    change (M.level Z.unop.1).val.map (f.unop.2.op ≫ g.unop.2.op)
      ((M.transition ((leOfHom g.unop.1).trans (leOfHom f.unop.1))).val.app
        (op X.unop.2) x) =
      (M.level Z.unop.1).val.map g.unop.2.op
        ((M.transition (leOfHom g.unop.1)).val.app (op Y.unop.2)
          ((M.level Y.unop.1).val.map f.unop.2.op
            ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)))
    rw [M.compose (leOfHom g.unop.1) (leOfHom f.unop.1)]
    rw [PresheafOfModules.naturality_apply (M.transition (leOfHom g.unop.1)).val]
    change (M.level Z.unop.1).val.map (f.unop.2.op ≫ g.unop.2.op)
      ((M.transition (leOfHom g.unop.1)).val.app (op X.unop.2)
        ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)) =
      (M.level Z.unop.1).val.map g.unop.2.op
        ((M.level Z.unop.1).val.map f.unop.2.op
          ((M.transition (leOfHom g.unop.1)).val.app (op X.unop.2)
            ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)))
    exact (M.level Z.unop.1).val.map_comp_apply _ _ _

set_option backward.isDefEq.respectTransparency false in
private def uncurryObj (M : StrictRingSystem B) : Towers (rings B) where
  obj := uncurryVal B M
  property n := by
    let e : (Prod.sectR n C).op ⋙ (uncurryVal B M).presheaf ≅
        (M.level n).val.presheaf :=
      NatIso.ofComponents (fun U ↦ Iso.refl _) (by
        intro U V f
        ext x
        change (M.level n).val.map f
          ((M.transition (Nat.le_refl n)).val.app U x) = (M.level n).val.map f x
        rw [M.identity])
    exact (Presheaf.isSheaf_of_iso_iff e).2 (M.level n).isSheaf

set_option backward.isDefEq.respectTransparency false in
private def uncurry : StrictRingSystem B ⥤ Towers (rings B) where
  obj := uncurryObj B
  map {M N} f := ObjectProperty.homMk
    { app := fun X ↦ (f.app X.unop.1).val.app (op X.unop.2)
      naturality := by
        intro X Y a
        ext x
        change (f.app Y.unop.1).val.app (op Y.unop.2)
          ((M.level Y.unop.1).val.map a.unop.2.op
            ((M.transition (leOfHom a.unop.1)).val.app (op X.unop.2) x)) = _
        rw [PresheafOfModules.naturality_apply (f.app Y.unop.1).val]
        have h := congrArg (fun t ↦ t.val.app (op X.unop.2)) (f.comm (leOfHom a.unop.1))
        exact congrArg ((N.level Y.unop.1).val.map a.unop.2.op)
          (ConcreteCategory.congr_hom h x).symm }
  map_id M := by rfl
  map_comp f g := by rfl

private theorem systemHom_ext {M N : StrictRingSystem B} (f g : M ⟶ N)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

private def sheafIso {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    (e : M.val ≅ N.val) : M ≅ N where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id

private def counitLevel (M : StrictRingSystem B) (n : ℕ) :
    ((curry B).obj ((uncurry B).obj M)).level n ≅ M.level n :=
  sheafIso (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    ext x
    change (M.level n).val.map f
      ((M.transition (Nat.le_refl n)).val.app U x) = (M.level n).val.map f x
    rw [M.identity]))

private def counit (M : StrictRingSystem B) :
    (curry B).obj ((uncurry B).obj M) ≅ M where
  hom :=
    { app := fun n ↦ (counitLevel B M n).hom
      comm := by
        intro m n h
        ext U x
        change (M.transition h).val.app U x =
          (M.level m).val.map (𝟙 U) ((M.transition h).val.app U x)
        rw [(M.level m).val.map_id]
        rfl }
  inv :=
    { app := fun n ↦ (counitLevel B M n).inv
      comm := by
        intro m n h
        ext U x
        change (M.level m).val.map (𝟙 U) ((M.transition h).val.app U x) =
          (M.transition h).val.app U x
        rw [(M.level m).val.map_id]
        rfl }
  hom_inv_id := by apply systemHom_ext B; intro n; ext U x; rfl
  inv_hom_id := by apply systemHom_ext B; intro n; ext U x; rfl

private def equivalence : Towers (rings B) ≌ StrictRingSystem B where
  functor := curry B
  inverse := uncurry B
  unitIso := NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk (condition (rings B))
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro X Y f
      ext x
      change M.obj.map f x =
        M.obj.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
          (M.obj.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
      have h : f = (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op ≫
          (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op := by
        apply Quiver.Hom.unop_inj
        ext <;> simp
      exact (M.obj.congr_map_apply h x).trans (M.obj.map_comp_apply _ _ x)))) (by
    intro M N f
    ext X x
    rfl)
  counitIso := NatIso.ofComponents (counit B) (by
    intro M N f
    apply systemHom_ext B
    intro n
    ext U x
    rfl)
  functor_unitIso_comp M := by
    apply systemHom_ext B
    intro n
    ext U x
    rfl

private def rebase {R S : ℕᵒᵖ ⥤ Sheaf J RingCat.{w}} (h : R = S) :
    Towers R ≌ Towers S := by
  subst S
  exact CategoryTheory.Equivalence.refl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem opSequence_comp {D : Type c} [Category.{v} D]
    {E : Type w} [Category E] {X : ℕ → D} (f : ∀ n, X (n + 1) ⟶ X n) (G : D ⥤ E) :
    Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) =
      Functor.ofOpSequence f ⋙ G := by
  let a : Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) ⟶
      Functor.ofOpSequence f ⋙ G := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 (G.obj (X n))) ?_
    intro n
    simp only [Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map]
    exact (Category.comp_id (G.map (f n))).trans (Category.id_comp (G.map (f n))).symm
  let i : Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) ≅
      Functor.ofOpSequence f ⋙ G :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ a.naturality f)
  exact Functor.ext_of_iso i (fun _ ↦ rfl) (fun _ ↦ rfl)

private theorem opSequence_comp_rev {D : Type c} [Category.{v} D]
    {E : Type w} [Category E] {X : ℕ → D} (f : ∀ n, X (n + 1) ⟶ X n) (G : D ⥤ E) :
    Functor.ofOpSequence f ⋙ G =
      Functor.ofOpSequence (X := fun n ↦ G.obj (X n)) (fun n ↦ G.map (f n)) :=
  (opSequence_comp f G).symm

end CoefficientTowerProof

namespace CoefficientReductionProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v w a av
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (S : SystemScalarAssignment (J := J))
  {A : Type a} [Category.{av} A] (F : A ⥤ StrictRingSystem B)

set_option backward.isDefEq.respectTransparency false in
private def ordinary {m n : ℕ} (h : m ≤ n) :
    (F ⋙ systemEvaluation B n) ⋙ systemTensor S B h ⟶ F ⋙ systemEvaluation B m where
  app M := ((systemTensorAdj S B h).homEquiv _ _).symm ((F.obj M).transition h)
  naturality {M N} f := by
    exact (systemTensorAdj S B h).homEquiv_naturality_right_square _ _ _ _
      ((F.map f).comm h)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_one {m n : ℕ} (h : m ≤ n) (M : A) (U : Cᵒᵖ)
    (x : ((F.obj M).level n).val.obj U) :
    ((ordinary B S F h).app M).val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model ((F.obj M).level n) U 1 x) =
      ((F.obj M).transition h).val.app U x := by
  have e := ((systemTensorAdj S B h).homEquiv _ _).apply_symm_apply
    ((F.obj M).transition h)
  rw [Adjunction.homEquiv_unit] at e
  have he := congrArg (fun z ↦ z.val.app U x) e
  change ((ordinary B S F h).app M).val.app U
    (((systemTensorAdj S B h).unit.app ((F.obj M).level n)).val.app U x) = _ at he
  simpa only [SystemScalarModel.unit_normalized] using he

private theorem ordinary_transpose {m n : ℕ} (h : m ≤ n) (M : A) :
    (systemTensorAdj S B h).homEquiv _ _ ((ordinary B S F h).app M) =
      (F.obj M).transition h :=
  ((systemTensorAdj S B h).homEquiv _ _).apply_symm_apply _

attribute [local irreducible] ordinary

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_identity (TC : SystemTensorCoherence S) (n : ℕ) (M : A) :
    (ordinary B S F (Nat.le_refl n)).app M =
      (TC.ordinaryUnit B n).hom.app ((F.obj M).level n) := by
  apply ((systemTensorAdj S B (Nat.le_refl n)).homEquiv _ _).injective
  rw [ordinary_transpose]
  rw [Adjunction.homEquiv_unit]
  ext U x
  change ((F.obj M).transition (Nat.le_refl n)).val.app U x =
    ((TC.ordinaryUnit B n).hom.app ((F.obj M).level n)).val.app U
      (((systemTensorAdj S B (Nat.le_refl n)).unit.app ((F.obj M).level n)).val.app U x)
  rw [(S _).unit_normalized, TC.unit_normalized, one_smul]
  exact (F.obj M).identity n U x

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_comp (TC : SystemTensorCoherence S)
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n) (M : A) :
    (systemTensor S B h).map ((ordinary B S F k).app M) ≫
      (ordinary B S F h).app M =
    (TC.ordinaryAssoc B h k).hom.app ((F.obj M).level n) ≫
      (ordinary B S F (h.trans k)).app M := by
  apply ((systemTensorAdj S B h).homEquiv _ _).injective
  apply ((systemTensorAdj S B k).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [ordinary_transpose]
  simp only [Adjunction.homEquiv_unit]
  ext U x
  change ((F.obj M).transition h).val.app U
      (((ordinary B S F k).app M).val.app U
        (((systemTensorAdj S B k).unit.app ((F.obj M).level n)).val.app U x)) =
    ((ordinary B S F (h.trans k)).app M).val.app U
      (((TC.ordinaryAssoc B h k).hom.app ((F.obj M).level n)).val.app U
        (((systemTensorAdj S B h).unit.app
          ((systemTensor S B k).obj ((F.obj M).level n))).val.app U
          (((systemTensorAdj S B k).unit.app ((F.obj M).level n)).val.app U x)))
  rw [(S _).unit_normalized, (S _).unit_normalized]
  rw [ordinary_one, TC.assoc_normalized, map_one, mul_one, ordinary_one]
  exact ((F.obj M).compose h k U x).symm

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.systemRingHasDerived

private theorem resolve (n : ℕ) (P : CochainComplex (systemLevel B n) ℤ) :
    ∃ (K : CochainComplex (systemLevel B n) ℤ) (q : K ⟶ P),
      systemLevelKFlat B n K ∧ QuasiIso q := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B.obj (op n))
  obtain ⟨K, q, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  exact ⟨K, q, ⟨hk, fun i ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (B.obj (op n)) (K.X i)).symm (hf i)⟩, hq⟩

private theorem natTrans_eq_of_resolution {X : Type c} [Category.{v} X]
    {Y : Type w} [Category Y] {G H : X ⥤ Y} (a b : G ⟶ H) (Good : X → Prop)
    (res : ∀ P, ∃ K, ∃ q : K ⟶ P, Good K ∧ IsIso (G.map q))
    (eq : ∀ K, Good K → a.app K = b.app K) : a = b := by
  apply NatTrans.ext
  funext P
  obtain ⟨K, q, hk, hq⟩ := res P
  let := hq
  apply (cancel_epi (G.map q)).mp
  rw [a.naturality, b.naturality, eq K hk]

private theorem comparison_assoc (TC : SystemTensorCoherence S)
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (P : CochainComplex (systemLevel B n) ℤ) :
    (systemDerivedTensor S B h).map ((S (B.map (homOfLE k).op)).model.ε.app P) ≫
      (S (B.map (homOfLE h).op)).model.ε.app
        (((systemTensor S B k).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (TC.ordinaryAssoc B h k) (.up ℤ)).hom.app P) =
    (TC.derivedAssoc B h k).hom.app (DerivedCategory.Q.obj P) ≫
      (S (B.map (homOfLE (h.trans k)).op)).model.ε.app P := by
  let Ek := (systemTensor S B k).mapHomologicalComplex (.up ℤ)
  let Eh := (systemTensor S B h).mapHomologicalComplex (.up ℤ)
  let Ed := (systemTensor S B (h.trans k)).mapHomologicalComplex (.up ℤ)
  let Tk := systemDerivedTensor S B k
  let Th := systemDerivedTensor S B h
  let Td := systemDerivedTensor S B (h.trans k)
  let εk := (S (B.map (homOfLE k).op)).model.ε
  let εh := (S (B.map (homOfLE h).op)).model.ε
  let εd := (S (B.map (homOfLE (h.trans k)).op)).model.ε
  let α := (NatIso.mapHomologicalComplex (TC.ordinaryAssoc B h k) (.up ℤ)).hom
  let β := (TC.derivedAssoc B h k).hom
  let a : DerivedCategory.Q ⋙ Tk ⋙ Th ⟶ Ed ⋙ DerivedCategory.Q :=
    Functor.whiskerRight εk Th ≫ Functor.whiskerLeft Ek εh ≫
      Functor.whiskerRight α DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ Tk ⋙ Th ⟶ Ed ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q β ≫ εd
  have hab : a = b := natTrans_eq_of_resolution a b (systemLevelKFlat B n)
    (fun P ↦ by
      obtain ⟨K, q, hk, hq⟩ := resolve B n P
      let := hq
      refine ⟨K, q, hk, ?_⟩
      change IsIso (Th.map (Tk.map (DerivedCategory.Q.map q)))
      infer_instance)
    (fun K hk ↦ (TC.derivedAssoc_rep B h k K hk).symm)
  exact congr_app hab P

private theorem comparison_comp (TC : SystemTensorCoherence S)
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (P : CochainComplex (systemLevel B n) ℤ)
    (N : CochainComplex (systemLevel B m) ℤ)
    (L : CochainComplex (systemLevel B r) ℤ)
    (b : ((systemTensor S B k).mapHomologicalComplex (.up ℤ)).obj P ⟶ N)
    (a : ((systemTensor S B h).mapHomologicalComplex (.up ℤ)).obj N ⟶ L)
    (c : ((systemTensor S B (h.trans k)).mapHomologicalComplex (.up ℤ)).obj P ⟶ L)
    (hc : ((systemTensor S B h).mapHomologicalComplex (.up ℤ)).map b ≫ a =
      (NatIso.mapHomologicalComplex (TC.ordinaryAssoc B h k) (.up ℤ)).hom.app P ≫ c) :
    (systemDerivedTensor S B h).map
        ((S (B.map (homOfLE k).op)).model.ε.app P ≫ DerivedCategory.Q.map b) ≫
      (S (B.map (homOfLE h).op)).model.ε.app N ≫ DerivedCategory.Q.map a =
    (TC.derivedAssoc B h k).hom.app (DerivedCategory.Q.obj P) ≫
      (S (B.map (homOfLE (h.trans k)).op)).model.ε.app P ≫ DerivedCategory.Q.map c := by
  let Ek := (systemTensor S B k).mapHomologicalComplex (.up ℤ)
  let Eh := (systemTensor S B h).mapHomologicalComplex (.up ℤ)
  let Th := systemDerivedTensor S B h
  let εk := (S (B.map (homOfLE k).op)).model.ε
  let εh := (S (B.map (homOfLE h).op)).model.ε
  let α := (NatIso.mapHomologicalComplex (TC.ordinaryAssoc B h k) (.up ℤ)).hom
  have hn : Th.map (DerivedCategory.Q.map b) ≫ εh.app N =
      εh.app (Ek.obj P) ≫ DerivedCategory.Q.map (Eh.map b) := εh.naturality b
  change Th.map (εk.app P ≫ DerivedCategory.Q.map b) ≫
      εh.app N ≫ DerivedCategory.Q.map a = _
  rw [Th.map_comp, Category.assoc]
  rw [← Category.assoc (Th.map (DerivedCategory.Q.map b)) (εh.app N)
    (DerivedCategory.Q.map a), hn]
  simp only [← DerivedCategory.Q.map_comp, Category.assoc]
  rw [hc]
  simp only [DerivedCategory.Q.map_comp]
  have he := comparison_assoc B S TC h k P
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ DerivedCategory.Q.map c) he

private theorem comparison_identity (TC : SystemTensorCoherence S) (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) :
    (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (TC.ordinaryUnit B n) (.up ℤ)).hom.app P) =
      (TC.derivedUnit B n).hom.app (DerivedCategory.Q.obj P) := by
  let E := (systemTensor S B (Nat.le_refl n)).mapHomologicalComplex (.up ℤ)
  let T := systemDerivedTensor S B (Nat.le_refl n)
  let ε := (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε
  let α := (NatIso.mapHomologicalComplex (TC.ordinaryUnit B n) (.up ℤ)).hom
  let β := (TC.derivedUnit B n).hom
  obtain ⟨K, q, hk, hq⟩ := resolve B n P
  let := hq
  have hε : T.map (DerivedCategory.Q.map q) ≫ ε.app P =
      ε.app K ≫ DerivedCategory.Q.map (E.map q) := ε.naturality q
  have hα : E.map q ≫ α.app P = α.app K ≫ q := α.naturality q
  have hβ : T.map (DerivedCategory.Q.map q) ≫ β.app (DerivedCategory.Q.obj P) =
      β.app (DerivedCategory.Q.obj K) ≫ DerivedCategory.Q.map q := β.naturality _
  apply (cancel_epi (T.map (DerivedCategory.Q.map q))).mp
  change T.map (DerivedCategory.Q.map q) ≫ (ε.app P ≫ DerivedCategory.Q.map (α.app P)) =
    T.map (DerivedCategory.Q.map q) ≫ β.app (DerivedCategory.Q.obj P)
  calc
    _ = ε.app K ≫ DerivedCategory.Q.map (E.map q ≫ α.app P) := by
      rw [← Category.assoc, hε]
      simp only [DerivedCategory.Q.map_comp, Category.assoc]
    _ = (ε.app K ≫ DerivedCategory.Q.map (α.app K)) ≫ DerivedCategory.Q.map q := by
      rw [hα]
      simp only [DerivedCategory.Q.map_comp, Category.assoc]
    _ = β.app (DerivedCategory.Q.obj K) ≫ DerivedCategory.Q.map q := by
      rw [← TC.derivedUnit_rep B n K hk]
    _ = _ := hβ.symm

section Derived
open CategoryTheory.Functor
universe d
variable [Abelian A] [HasDerivedCategory.{d} A] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private abbrev evaluation (n : ℕ) := F ⋙ systemEvaluation B n

private def representedReduction {m n : ℕ} (h : m ≤ n) :
    DerivedCategory.Q ⋙ ((evaluation B F n).mapDerivedCategory ⋙ systemDerivedTensor S B h) ⟶
      DerivedCategory.Q ⋙ (evaluation B F m).mapDerivedCategory :=
  whiskerRight (evaluation B F n).mapDerivedCategoryFactors.hom (systemDerivedTensor S B h) ≫
    whiskerLeft ((evaluation B F n).mapHomologicalComplex (.up ℤ))
      (S (B.map (homOfLE h).op)).model.ε ≫
    whiskerRight ((ordinary B S F h).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q ≫
    (evaluation B F m).mapDerivedCategoryFactors.inv

attribute [local irreducible] representedReduction

private def reduction {m n : ℕ} (h : m ≤ n) :
    (evaluation B F n).mapDerivedCategory ⋙ systemDerivedTensor S B h ⟶
      (evaluation B F m).mapDerivedCategory :=
  (Localization.whiskeringLeftFunctor' DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _).preimage (representedReduction B S F h)

attribute [local irreducible] reduction

private theorem reduction_rep {m n : ℕ} (h : m ≤ n) (P : CochainComplex A ℤ) :
    (reduction B S F h).app (DerivedCategory.Q.obj P) =
      (systemDerivedTensor S B h).map ((evaluation B F n).mapDerivedCategoryFactors.hom.app P) ≫
        (S (B.map (homOfLE h).op)).model.ε.app
          (((evaluation B F n).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (((ordinary B S F h).mapHomologicalComplex (.up ℤ)).app P) ≫
        (evaluation B F m).mapDerivedCategoryFactors.inv.app P :=
  by
    unfold reduction
    have he := congr_app (CategoryTheory.Functor.map_preimage
      (Localization.whiskeringLeftFunctor' DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) _) (representedReduction B S F h)) P
    change ((Localization.whiskeringLeftFunctor' DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) _).preimage
        (representedReduction B S F h)).app (DerivedCategory.Q.obj P) =
      (representedReduction B S F h).app P at he
    simpa only [representedReduction, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app] using he

private theorem reduction_identity (TC : SystemTensorCoherence S) (n : ℕ)
    (M : DerivedCategory A) :
    (reduction B S F (Nat.le_refl n)).app M =
      (TC.derivedUnit B n).hom.app ((evaluation B F n).mapDerivedCategory.obj M) := by
  have he : reduction B S F (Nat.le_refl n) =
      whiskerLeft (evaluation B F n).mapDerivedCategory (TC.derivedUnit B n).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    let Pn := ((evaluation B F n).mapHomologicalComplex (.up ℤ)).obj P
    let α := (evaluation B F n).mapDerivedCategoryFactors.app P
    let Tn := systemDerivedTensor S B (Nat.le_refl n)
    let ε := (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε
    let b := ((ordinary B S F (Nat.le_refl n)).mapHomologicalComplex (.up ℤ)).app P
    let un := (NatIso.mapHomologicalComplex (TC.ordinaryUnit B n) (.up ℤ)).hom.app Pn
    have hb : b = un := by
      ext i : 1
      exact ordinary_identity B S F TC n (P.X i)
    have hu : ε.app Pn ≫ DerivedCategory.Q.map b =
        (TC.derivedUnit B n).hom.app (DerivedCategory.Q.obj Pn) := by
      rw [hb]
      exact comparison_identity B S TC n Pn
    rw [reduction_rep]
    change Tn.map α.hom ≫ ε.app Pn ≫ DerivedCategory.Q.map b ≫ α.inv =
      (TC.derivedUnit B n).hom.app ((evaluation B F n).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P))
    calc
      _ = Tn.map α.hom ≫
          (TC.derivedUnit B n).hom.app (DerivedCategory.Q.obj Pn) ≫ α.inv := by
        rw [← Category.assoc (ε.app Pn) (DerivedCategory.Q.map b) α.inv, hu]
      _ = _ := by
        have hn : Tn.map α.hom ≫
            (TC.derivedUnit B n).hom.app (DerivedCategory.Q.obj Pn) =
          (TC.derivedUnit B n).hom.app
            ((evaluation B F n).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
              α.hom := (TC.derivedUnit B n).hom.naturality α.hom
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun z ↦ z ≫ α.inv) hn
  exact congr_app he M

private theorem reduction_comp (TC : SystemTensorCoherence S)
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n) (M : DerivedCategory A) :
    (systemDerivedTensor S B h).map ((reduction B S F k).app M) ≫
        (reduction B S F h).app M =
      (TC.derivedAssoc B h k).hom.app ((evaluation B F n).mapDerivedCategory.obj M) ≫
        (reduction B S F (h.trans k)).app M := by
  let Th := systemDerivedTensor S B h
  have he : whiskerRight (reduction B S F k) Th ≫ reduction B S F h =
      whiskerLeft (evaluation B F n).mapDerivedCategory (TC.derivedAssoc B h k).hom ≫
        reduction B S F (h.trans k) := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    let Pn := ((evaluation B F n).mapHomologicalComplex (.up ℤ)).obj P
    let Pm := ((evaluation B F m).mapHomologicalComplex (.up ℤ)).obj P
    let Pr := ((evaluation B F r).mapHomologicalComplex (.up ℤ)).obj P
    let αn := (evaluation B F n).mapDerivedCategoryFactors.app P
    let αm := (evaluation B F m).mapDerivedCategoryFactors.app P
    let αr := (evaluation B F r).mapDerivedCategoryFactors.app P
    let Tk := systemDerivedTensor S B k
    let Td := systemDerivedTensor S B (h.trans k)
    let εk := (S (B.map (homOfLE k).op)).model.ε
    let εh := (S (B.map (homOfLE h).op)).model.ε
    let εd := (S (B.map (homOfLE (h.trans k)).op)).model.ε
    let b := ((ordinary B S F k).mapHomologicalComplex (.up ℤ)).app P
    let a := ((ordinary B S F h).mapHomologicalComplex (.up ℤ)).app P
    let c := ((ordinary B S F (h.trans k)).mapHomologicalComplex (.up ℤ)).app P
    let β := (TC.derivedAssoc B h k).hom
    have hc : ((systemTensor S B h).mapHomologicalComplex (.up ℤ)).map b ≫ a =
        (NatIso.mapHomologicalComplex (TC.ordinaryAssoc B h k) (.up ℤ)).hom.app Pn ≫ c := by
      ext i : 1
      exact ordinary_comp B S F TC h k (P.X i)
    have habc := comparison_comp B S TC h k Pn Pm Pr b a c hc
    have hβ : Th.map (Tk.map αn.hom) ≫ β.app (DerivedCategory.Q.obj Pn) =
        β.app ((evaluation B F n).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
          Td.map αn.hom := β.naturality αn.hom
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [reduction_rep, reduction_rep, reduction_rep]
    change Th.map (Tk.map αn.hom ≫ εk.app Pn ≫ DerivedCategory.Q.map b ≫ αm.inv) ≫
        (Th.map αm.hom ≫ εh.app Pm ≫ DerivedCategory.Q.map a ≫ αr.inv) =
      β.app ((evaluation B F n).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (Td.map αn.hom ≫ εd.app Pn ≫ DerivedCategory.Q.map c ≫ αr.inv)
    calc
      _ = Th.map (Tk.map αn.hom) ≫
          (Th.map (εk.app Pn ≫ DerivedCategory.Q.map b) ≫ εh.app Pm ≫
            DerivedCategory.Q.map a) ≫ αr.inv := by
        simp only [Th.map_comp, Category.assoc]
        rw [← Th.map_comp_assoc αm.inv αm.hom, αm.inv_hom_id,
          Th.map_id, Category.id_comp]
      _ = Th.map (Tk.map αn.hom) ≫
          (β.app (DerivedCategory.Q.obj Pn) ≫ εd.app Pn ≫ DerivedCategory.Q.map c) ≫
            αr.inv := by rw [habc]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ εd.app Pn ≫ DerivedCategory.Q.map c ≫ αr.inv) hβ
  exact congr_app he M

end Derived

end CoefficientReductionProof

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- Retain commutativity in the existing coefficient ring tower. Forgetting commutativity
recovers `spCoefficientRings`: the same constant quotient sheaves and the same reduction
ring homomorphisms are used. This is a change of bundled target category only.
Source: blueprint, coefficient-tower lemma, clause (3)
(blueprint: prose-09-21). -/
def spCoefficientCommRings :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ (constantSheaf (Scheme.ProEt.topology T)
      CommRingCat.{max u (t + 1)}).obj (CommRingCat.of
        (ULift.{t + 1}
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))))
    (fun n ↦ (constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
            ULift.ringEquiv.toRingHom))))

private theorem coefficientRings_eq :
    spCoefficientRings l E T = CoefficientTowerProof.rings (spCoefficientCommRings l E T) := by
  symm
  unfold spCoefficientRings spCoefficientReduction CoefficientTowerProof.rings
    spCoefficientCommRings
  exact CoefficientTowerProof.opSequence_comp_rev _ _

section
attribute [local irreducible] spCoefficientCommRings spCoefficientRings
  CoefficientTowerProof.equivalence CoefficientTowerProof.rebase

private def coefficientEquivalence : spCoefficientTowers l E T ≌
    StrictRingSystem.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) :=
  (CoefficientTowerProof.rebase (coefficientRings_eq l E T)).trans
    (CoefficientTowerProof.equivalence (spCoefficientCommRings l E T))

end

/-- The abelian axioms for the existing componentwise preadditive structure.
Source: blueprint, coefficient-tower lemma, clause (1); Stacks 03DA and 03DB
(blueprint: prose-09-21).
Proof: give ℕ × T.ProEt the vertical topology, whose sheaf condition is exactly the
recorded levelwise condition. The actual varying coefficient presheaf is a ring sheaf:
its restriction to level n is naturally isomorphic to the recorded ring sheaf R_n.
Rebundle each tower as a sheaf of modules over this ring sheaf. The inverse forgets
only the global sheaf proof and retains its levelwise form; the two functors fix all
presheaf modules and all maps, so their unit and counit are identities. Transfer finite
products along this equivalence and use Mathlib's abelianOfEquivalence, which uses the
existing componentwise preadditive structure. Extract normality, finite products,
kernels and cokernels from this abelian structure. -/
theorem sp_coefficient_towers_abelian_axioms :
    IsNormalMonoCategory (spCoefficientTowers l E T) ∧
      IsNormalEpiCategory (spCoefficientTowers l E T) ∧
      HasFiniteProducts (spCoefficientTowers l E T) ∧
      HasKernels (spCoefficientTowers l E T) ∧
      HasCokernels (spCoefficientTowers l E T) := by
  let K := verticalDiagramSiteTopology ℕ T.ProEt (Scheme.ProEt.topology T)
  have hs (M : PresheafOfModules.{max u (t + 1)} (spCoefficientPresheaf l E T)) :
      Presheaf.IsSheaf K M.presheaf ↔ spCoefficientTowerSheafCondition l E T M := by
    exact verticalDiagramSite_isSheaf_iff ℕ T.ProEt (Scheme.ProEt.topology T) M.presheaf
  let R : Sheaf K RingCat.{max u (t + 1)} :=
    ⟨spCoefficientPresheaf l E T, by
      apply (verticalDiagramSite_isSheaf_iff ℕ T.ProEt (Scheme.ProEt.topology T) _).2
      intro n
      let i : (Prod.sectR n T.ProEt).op ⋙ spCoefficientPresheaf l E T ≅
          (spCoefficientRing l E T n).obj :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
          intro U V f
          simp [spCoefficientPresheaf, spCoefficientRings, spCoefficientRing,
            Prod.sectR]
          rfl)
      exact (Presheaf.isSheaf_of_iso_iff i).2 (spCoefficientRing l E T n).property⟩
  let F : spCoefficientTowers l E T ⥤ SheafOfModules.{max u (t + 1)} R :=
    { obj := fun M ↦ ⟨M.obj, (hs M.obj).2 M.property⟩
      map := fun f ↦ ⟨f.hom⟩ }
  let G : SheafOfModules.{max u (t + 1)} R ⥤ spCoefficientTowers l E T :=
    { obj := fun M ↦ ⟨M.val, (hs M.val).1 M.isSheaf⟩
      map := fun f ↦ ObjectProperty.homMk f.val }
  let e : spCoefficientTowers l E T ≌ SheafOfModules.{max u (t + 1)} R :=
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
      counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) }
  have : e.functor.IsEquivalence := e.isEquivalence_functor
  have : HasFiniteProducts (spCoefficientTowers l E T) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  let a : Abelian (spCoefficientTowers l E T) := abelianOfEquivalence e.functor
  exact ⟨a.toIsNormalMonoCategory, a.toIsNormalEpiCategory,
    a.has_finite_products, a.has_kernels, a.has_cokernels⟩

/-- The abelian structure extends the existing componentwise addition of tower maps;
all remaining fields are proofs of the preceding named axioms.
Source: blueprint, coefficient-tower lemma, clause (1)
(blueprint: prose-09-21). -/
instance spCoefficientTowersAbelian : Abelian (spCoefficientTowers l E T) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (sp_coefficient_towers_abelian_axioms l E T).1
  toIsNormalEpiCategory := (sp_coefficient_towers_abelian_axioms l E T).2.1
  has_finite_products := (sp_coefficient_towers_abelian_axioms l E T).2.2.1
  has_kernels := (sp_coefficient_towers_abelian_axioms l E T).2.2.2.1
  has_cokernels := (sp_coefficient_towers_abelian_axioms l E T).2.2.2.2

/-- Evaluation after the sectionwise specified identification of the recorded tower
category with strict semilinear systems. Source: blueprint, coefficient-tower lemma,
clause (2) (blueprint: prose-09-21). -/
abbrev spCoefficientEvaluation
    (e : spCoefficientTowers l E T ≌
      StrictRingSystem.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T))
    (n : ℕ) :=
  e.functor ⋙ systemEvaluation.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n

section
attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.systemRingHasDerived spCoefficientCommRings

/-- The three clauses of the coefficient-tower lemma, with the actual tower category
and all identifications fixed on sections. The scalar and tensor fields are the
existing canonical derived-change models, not arbitrary maps or isomorphisms.
Source: blueprint, coefficient-tower lemma, clauses (1)--(3); Bhatt--Scholze,
Definition 3.5.3 (blueprint: prose-09-21). -/
structure SpCoefficientTowersAbelian where
  /-- Uncurrying into the existing varying-coefficient strict systems. -/
  equivalence : spCoefficientTowers l E T ≌
    StrictRingSystem.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T)
  /-- Uncurrying fixes the module of sections, including its scalar action. -/
  sections : ∀ (M : spCoefficientTowers l E T) (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq (((equivalence.functor.obj M).level n).val.obj U) (M.obj.obj (op (n, U.unop)))
  /-- Uncurrying fixes vertical restriction maps. -/
  restrictions : ∀ (M : spCoefficientTowers l E T) (n : ℕ)
    {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
    HEq (((equivalence.functor.obj M).level n).val.map f)
      (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op)
  /-- Uncurrying fixes every iterated transition, including the identity. -/
  transitions : ∀ (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ),
    HEq (((equivalence.functor.obj M).transition h).val.app U)
      (M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  /-- Uncurrying fixes all components of every linear tower map. -/
  morphisms : ∀ {M N : spCoefficientTowers l E T} (f : M ⟶ N) (n : ℕ)
    (U : T.ProEtᵒᵖ),
    HEq (((equivalence.functor.map f).app n).val.app U) (f.hom.app (op (n, U.unop)))
  /-- Addition is the componentwise addition of linear maps. -/
  [equivalenceAdditive : equivalence.functor.Additive]
  /-- Grothendieck abelianness includes a generator, colimits and exact filtered colimits. -/
  grothendieck : IsGrothendieckAbelian.{max u (t + 1)} (spCoefficientTowers l E T)
  /-- Evaluation preserves finite limits, in particular kernels. -/
  [evaluationLimits : ∀ n : ℕ,
    PreservesFiniteLimits (spCoefficientEvaluation l E T equivalence n)]
  /-- Evaluation preserves finite colimits, in particular cokernels. -/
  [evaluationColimits : ∀ n : ℕ,
    PreservesFiniteColimits (spCoefficientEvaluation l E T equivalence n)]
  /-- Filtered colimits are computed at each coefficient level. -/
  filteredColimits : ∀ (I : Type (max u (t + 1))) [SmallCategory I] [IsFiltered I]
    (n : ℕ), PreservesColimitsOfShape I (spCoefficientEvaluation l E T equivalence n)
  /-- The ordinary unbounded localization of tower complexes, in the standard universe. -/
  [hasDerived : HasDerivedCategory.{max u (t + 1) + 1} (spCoefficientTowers l E T)]
  /-- Existing universal derived scalar extensions, with their normalized adjunctions. -/
  scalar : SystemScalarAssignment.{t + 1, t, max u (t + 1)} (J := Scheme.ProEt.topology T)
  /-- Existing ordinary tensor associators and their canonical K-flat derived comparisons. -/
  tensor : SystemTensorCoherence.{t + 1, t, max u (t + 1)} scalar
  /-- Underived reduction along an actual coefficient transition. -/
  ordinaryReduction : ∀ {m n : ℕ} (h : m ≤ n),
    spCoefficientEvaluation l E T equivalence n ⋙
      systemTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h ⟶
    spCoefficientEvaluation l E T equivalence m
  /-- It is the tensor adjunct of the specified strict semilinear transition;
  on local pure tensors it sends c tensor x to c times t(x). -/
  ordinaryReduction_eq : ∀ {m n : ℕ} (h : m ≤ n) (M : spCoefficientTowers l E T),
    (ordinaryReduction h).app M =
      ((systemTensorAdj.{t + 1, t, max u (t + 1)} scalar
        (spCoefficientCommRings l E T) h).homEquiv _ _).symm
        ((equivalence.functor.obj M).transition h)
  /-- Reduction is a natural transformation on the ordinary derived tower category. -/
  reduction : ∀ {m n : ℕ} (h : m ≤ n),
    (spCoefficientEvaluation l E T equivalence n).mapDerivedCategory ⋙
      systemDerivedTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h ⟶
    (spCoefficientEvaluation l E T equivalence m).mapDerivedCategory
  /-- The derived comparison followed by the actual termwise reduction induces reduction.
  This holds for all complexes, so in particular it fixes every K-flat computation. -/
  reduction_rep : ∀ {m n : ℕ} (h : m ≤ n)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ),
    (reduction h).app (DerivedCategory.Q.obj P) =
      (systemDerivedTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h).map
        ((spCoefficientEvaluation l E T equivalence n).mapDerivedCategoryFactors.hom.app P) ≫
      (scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.ε.app
        (((spCoefficientEvaluation l E T equivalence n).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinaryReduction h)
        (.up ℤ)).app P) ≫
      (spCoefficientEvaluation l E T equivalence m).mapDerivedCategoryFactors.inv.app P
  /-- Equal levels give the canonical tensor unitor, including the first positive level. -/
  reduction_identity : ∀ (n : ℕ) (M : DerivedCategory (spCoefficientTowers l E T)),
    (reduction (Nat.le_refl n)).app M =
      (tensor.derivedUnit (spCoefficientCommRings l E T) n).hom.app
        ((spCoefficientEvaluation l E T equivalence n).mapDerivedCategory.obj M)
  /-- Successive reductions equal direct reduction under the canonical tensor associator. -/
  reduction_comp : ∀ {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (M : DerivedCategory (spCoefficientTowers l E T)),
    (systemDerivedTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h).map
        ((reduction k).app M) ≫ (reduction h).app M =
      (tensor.derivedAssoc (spCoefficientCommRings l E T) h k).hom.app
        ((spCoefficientEvaluation l E T equivalence n).mapDerivedCategory.obj M) ≫
      (reduction (h.trans k)).app M

end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] spCoefficientCommRings spCoefficientRings
  spCoefficientTowerSheafCondition coefficientEquivalence DerivedCategory
  CategoryTheory.Functor.mapDerivedCategory SheafOfModules.systemRingHasDerived

end

end AlgebraicGeometry.ProEtale

-- Preserve the inherited instance environment for importing modules.
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
