/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Data.Int.Interval

/-! # Bounded ordinary evaluation on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X.
(blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly)

## Main statements

- `assembly`: the canonical finite diagonal evaluation and its inverse chain map.
- `IsModuleEvaluation`: the section formula for the termwise comparison.

All tensor and Hom objects below are the recorded sheaf constructions. The
section formulas specify the actual comparison, including its normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace CategoryTheory.RingedSiteBoundedEvaluation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  (R : Sheaf J CommRingCat.{max u v w})

/-- The recorded module category, in a universe containing the site.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
abbrev Modules := ringedSiteModules.{max u v w, max u v w, v, u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

local instance (B : Modules.{u, v, w} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    Module (R.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
          (B.val.obj V)) :=
  inferInstanceAs (Module (R.obj.obj V) (B.val.obj V))

local instance (B : Modules.{u, v, w} R) (U : Cᵒᵖ) (V : (Over U.unop)ᵒᵖ) :
    SMul (((PresheafOfModules.restrictOver R.obj U.unop).obj
      (𝟙_ (Modules.{u, v, w} R)).val).obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map V.unop.hom.op).hom).obj
          (B.val.obj (op V.unop.left))) :=
  inferInstanceAs (SMul (R.obj.obj (op V.unop.left)) (B.val.obj (op V.unop.left)))

/-- The structure sheaf placed in degree zero.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def unitComplex : CochainComplex (Modules.{u, v, w} R) ℤ :=
  (HomologicalComplex.single (Modules.{u, v, w} R) (.up ℤ) 0).obj (𝟙_ (Modules.{u, v, w} R))

/-- The ordinary Hom dual, with its recorded signed differential.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def dual (E : CochainComplex (Modules.{u, v, w} R) ℤ) : CochainComplex (Modules.{u, v, w} R) ℤ :=
  homComplex E (unitComplex.{u, v, w} R)

/-- The small coproducts used by total complexes exist by module sheafification.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
instance smallColimits : HasColimitsOfSize.{0, 0} (Modules.{u, v, w} R) := inferInstance

/-- Supply the total-complex coproducts directly, avoiding a search through special totals.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
instance hasTotal (E F : CochainComplex (Modules.{u, v, w} R) ℤ) :
    F.HasMapBifunctor (dual.{u, v, w} R E) (curriedTensor (Modules.{u, v, w} R)) := fun _ ↦
      inferInstance

/-- The existing direct-sum total tensor complex, with sign on the second differential.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def total (E F : CochainComplex (Modules.{u, v, w} R) ℤ) : CochainComplex (Modules.{u, v, w} R) ℤ :=
  letI := hasTotal.{u, v, w} R E F
  CochainComplex.mapBifunctor F (dual.{u, v, w} R E) (curriedTensor (Modules.{u, v, w} R))

/-- The actual coproduct inclusion into the total tensor, with its codomain fixed.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def inclusion (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (p q n : ℤ) (h : p + q = n) :
    F.X p ⊗ (dual.{u, v, w} R E).X q ⟶ (total.{u, v, w} R E F).X n :=
  letI := hasTotal.{u, v, w} R E F
  CochainComplex.ιMapBifunctor F (dual.{u, v, w} R E) (curriedTensor (Modules.{u, v, w} R)) p q n h

/-- Local pure tensors enter the tensor sheaf through its sheafification unit.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def pureTensor (A B : Modules.{u, v, w} R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) : (A ⊗ B).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (A.val ⊗ B.val) ≫ (SheafOfModules.tensorObjIsoSheafification.{v, u, max u v w}
        (R := R) A B).inv.val).app U).hom
        (x ⊗ₜ[R.obj.obj U] y)

/-- Projection from the ordinary dual to its unique possibly nonzero Hom factor.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def dualProjection (E : CochainComplex (Modules.{u, v, w} R) ℤ) (q i : ℤ) (h : i + q = 0) :
    (dual.{u, v, w} R E).X q ⟶ SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)) :=
  homComplexπ E (unitComplex.{u, v, w} R) q i 0 h ≫
    SheafOfModules.homObjMap (𝟙 (E.X i))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules.{u, v, w} R))).hom

/-- The canonical module comparison is specified on every slice and every pure tensor.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def IsModuleEvaluation (A B : Modules.{u, v, w} R)
    (θ : B ⊗ SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R)) ⟶ SheafOfModules.homObj A B) :
    Prop :=
  ∀ (U : Cᵒᵖ) (y : B.val.obj U)
    (φ : (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val.obj U)
    (V : (Over U.unop)ᵒᵖ) (x : A.val.obj (op V.unop.left)),
    ((((θ.val.app U).hom
      (pureTensor.{u, v, w} R B (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))) U y φ)).app
        V).hom x) =
        ((φ.app V).hom x) • B.val.map V.unop.hom.op y

/-- The source finite-sum family, indexed by the complete closed interval, possibly empty.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def sourceFamily (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b n : ℤ)
    (i : ↥(Finset.Icc a b)) : Modules.{u, v, w} R :=
  F.X (i.val + n) ⊗ SheafOfModules.homObj (E.X i.val) (𝟙_ (Modules.{u, v, w} R))

/-- The target finite-sum family, using the same indexing and degree convention.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def targetFamily (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b n : ℤ)
    (i : ↥(Finset.Icc a b)) : Modules.{u, v, w} R :=
  SheafOfModules.homObj (E.X i.val) (F.X (i.val + n))

/-- Finite biproducts from the existing sectionwise finite products; no new objects chosen.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
instance finiteBiproducts : HasFiniteBiproducts (Modules.{u, v, w} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

attribute [local irreducible] homComplex homComplexFunctor homComplexπ

private def evaluationSection (A B : Modules.{u, v, w} R) (U : Cᵒᵖ)
    (y : B.val.obj U)
    (φ : (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val.obj U) :
    (SheafOfModules.homObj A B).val.obj U where
  app V := ModuleCat.ofHom
    { toFun := fun x ↦ (show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
        B.val.map V.unop.hom.op y
      map_add' := by intro x x'; rw [map_add, add_smul]
      map_smul' := by
        intro r x
        change (show R.obj.obj (op V.unop.left) from (φ.app V).hom (r • x)) • _ = _
        rw [map_smul]
        change ((show R.obj.obj (op V.unop.left) from r) *
          (show R.obj.obj (op V.unop.left) from (φ.app V).hom x)) •
            B.val.map V.unop.hom.op y =
          (show R.obj.obj (op V.unop.left) from r) •
            ((show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
              B.val.map V.unop.hom.op y)
        exact mul_smul _ _ _ }
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((φ.app W).hom (A.val.map f.unop.left.op x)) •
        B.val.map W.unop.hom.op y =
      B.val.map f.unop.left.op (((φ.app V).hom x) • B.val.map V.unop.hom.op y)
    rw [B.val.map_smul]
    have hφ := PresheafOfModules.naturality_apply φ f x
    change (φ.app W).hom (A.val.map f.unop.left.op x) =
      R.obj.map f.unop.left.op ((φ.app V).hom x) at hφ
    rw [hφ, ← B.val.map_comp_apply, ← op_comp, Over.w]
    rfl

private def evaluationBilinear (A B : Modules.{u, v, w} R) (U : Cᵒᵖ) :
    B.val.obj U →ₗ[R.obj.obj U]
      (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val.obj U →ₗ[R.obj.obj U]
        (SheafOfModules.homObj A B).val.obj U where
  toFun y :=
    { toFun := evaluationSection R A B U y
      map_add' := by
        intro φ ψ
        apply PresheafOfModules.hom_ext
        intro V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change ((show R.obj.obj (op V.unop.left) from (φ.app V).hom x) +
          (show R.obj.obj (op V.unop.left) from (ψ.app V).hom x)) •
            B.val.map V.unop.hom.op y = _
        exact add_smul _ _ _
      map_smul' := by
        intro r φ
        apply PresheafOfModules.hom_ext
        intro V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (R.obj.map V.unop.hom.op r *
          (show R.obj.obj (op V.unop.left) from (φ.app V).hom x)) •
            B.val.map V.unop.hom.op y =
          R.obj.map V.unop.hom.op r •
            ((show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
              B.val.map V.unop.hom.op y)
        exact mul_smul _ _ _ }
  map_add' := by
    intro y z
    apply LinearMap.ext
    intro φ
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
        B.val.map V.unop.hom.op (y + z) =
      (show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
          B.val.map V.unop.hom.op y +
        (show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
          B.val.map V.unop.hom.op z
    rw [map_add]
    exact smul_add _ _ _
  map_smul' := by
    intro r y
    apply LinearMap.ext
    intro φ
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (φ.app V).hom x • B.val.map V.unop.hom.op (r • y) =
      R.obj.map V.unop.hom.op r • ((φ.app V).hom x • B.val.map V.unop.hom.op y)
    rw [B.val.map_smul]
    change (show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
        (R.obj.map V.unop.hom.op r • B.val.map V.unop.hom.op y) = _
    exact smul_comm _ _ _

private theorem evaluationBilinear_apply (A B : Modules.{u, v, w} R)
    (U : Cᵒᵖ) (y : B.val.obj U)
    (φ : (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val.obj U)
    (V : (Over U.unop)ᵒᵖ) (x : A.val.obj (op V.unop.left)) :
    (((evaluationBilinear R A B U y φ).app V).hom x) =
      (φ.app V).hom x • B.val.map V.unop.hom.op y := by
  rfl

private def evaluationPresheaf (A B : Modules.{u, v, w} R) :
    B.val ⊗ (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val ⟶
      (SheafOfModules.homObj A B).val where
  app U := by
    let f := TensorProduct.lift (evaluationBilinear R A B U)
    exact (ModuleCat.ofHom f :
      ModuleCat.of (R.obj.obj U)
          (B.val.obj U ⊗[R.obj.obj U]
            (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val.obj U) ⟶
        ModuleCat.of (R.obj.obj U) ((SheafOfModules.homObj A B).val.obj U))
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro y φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show R.obj.obj (op W.unop.left) from
        (φ.app (Over.map f.unop |>.op.obj W)).hom x) •
          B.val.map W.unop.hom.op (B.val.map f y) = _
    rw [← B.val.map_comp_apply]
    rfl

private def tensorLift (A B N : Modules.{u, v, w} R) (q : A.val ⊗ B.val ⟶ N.val) :
    A ⊗ B ⟶ N :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom ≫
    ((PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).homEquiv _ _).symm q

private def moduleEvaluation (A B : Modules.{u, v, w} R) :
    B ⊗ SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R)) ⟶ SheafOfModules.homObj A B :=
  tensorLift R B (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R)))
    (SheafOfModules.homObj A B) (evaluationPresheaf R A B)

attribute [local irreducible] SheafOfModules.monoidalCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] dual total inclusion unitComplex
  CochainComplex.ιMapBifunctor CochainComplex.mapBifunctor
  sourceFamily targetFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comparison_natural {P D : Type*} [Category P] [Category D]
    [MonoidalCategory P] [MonoidalCategory D] (S : P ⥤ D) [S.Monoidal]
    {A A' B B' : D} {X X' Y Y' : P}
    (uA : A ⟶ S.obj X) (uA' : A' ⟶ S.obj X')
    (uB : B ⟶ S.obj Y) (uB' : B' ⟶ S.obj Y')
    (f : A ⟶ A') (g : B ⟶ B') (f' : X ⟶ X') (g' : Y ⟶ Y')
    (hf : f ≫ uA' = uA ≫ S.map f') (hg : g ≫ uB' = uB ≫ S.map g') :
    (f ⊗ₘ g) ≫ (uA' ⊗ₘ uB') ≫ (Functor.Monoidal.μIso S X' Y').hom =
      (uA ⊗ₘ uB) ≫ (Functor.Monoidal.μIso S X Y).hom ≫ S.map (f' ⊗ₘ g') := by
  simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]
  rw [← tensorHom_comp_tensorHom]
  simp only [Functor.Monoidal.μIso_hom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural]

private theorem restriction_map_id {A B : Modules.{u, v, w} R} (f : A ⟶ B) :
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map f = f.val := by
  rfl

attribute [local irreducible] sheafCompose
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction

private def inverseCounit :
    𝟭 (Modules.{u, v, w} R) ⟶
      SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
        PresheafOfModules.sheafification.{max u v w}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) where
  app M := ((asIso (PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).inv).app M
  naturality {A B} f := by
    have h := ((asIso (PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).inv).naturality f
    rw [Functor.comp_map, restriction_map_id R f, Functor.id_map] at h
    exact h

private theorem tensorComparison_formula (A B : Modules.{u, v, w} R) :
    (SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom =
      ((inverseCounit R).app A ⊗ₘ (inverseCounit R).app B) ≫
        (Functor.Monoidal.μIso
          (PresheafOfModules.sheafification.{max u v w}
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)) A.val B.val).hom := by
  rfl

attribute [local irreducible] inverseCounit

private theorem tensorIso_natural {A A' B B' : Modules.{u, v, w} R}
    (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) A' B').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom ≫
        (PresheafOfModules.sheafification.{max u v w}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
            (f.val ⊗ₘ g.val) := by
  let S := PresheafOfModules.sheafification.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let η := inverseCounit R
  have h := comparison_natural S (η.app A) (η.app A') (η.app B) (η.app B')
    f g f.val g.val (η.naturality f) (η.naturality g)
  rw [tensorComparison_formula, tensorComparison_formula]
  dsimp only [S, η, Functor.id_obj, SheafOfModules.forget] at h
  simpa only [Category.assoc] using h

attribute [local semireducible] sheafCompose PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction

private theorem pureTensor_map {A A' B B' : Modules.{u, v, w} R}
    (f : A ⟶ A') (g : B ⟶ B') (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    ((f ⊗ₘ g).val.app U).hom (pureTensor R A B U x y) =
      pureTensor R A' B' U ((f.val.app U).hom x) ((g.val.app U).hom y) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := SheafOfModules.tensorObjIsoSheafification (R := R) A B
  let e' := SheafOfModules.tensorObjIsoSheafification (R := R) A' B'
  have he : e.inv ≫ (f ⊗ₘ g) = (PresheafOfModules.sheafification.{max u v w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
        (f.val ⊗ₘ g.val) ≫ e'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact tensorIso_natural R f g
  have hn := adj.unit.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ adj.unit.app (A'.val ⊗ B'.val) =
    adj.unit.app (A.val ⊗ B.val) ≫
      ((PresheafOfModules.sheafification.{max u v w}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (f.val ⊗ₘ g.val)).val at hn
  have h : (adj.unit.app (A.val ⊗ B.val) ≫ e.inv.val) ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ (adj.unit.app (A'.val ⊗ B'.val) ≫ e'.inv.val) := by
    rw [Category.assoc, ← SheafOfModules.comp_val, he, SheafOfModules.comp_val,
      ← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun k ↦ (k.app U).hom (x ⊗ₜ[R.obj.obj U] y)) h

private theorem tensor_ext {A B N : Modules.{u, v, w} R} (f g : A ⊗ B ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U),
      (f.val.app U).hom (pureTensor R A B U x y) =
        (g.val.app U).hom (pureTensor R A B U x y)) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv).1
  apply ((PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).homEquiv
      (A.val ⊗ B.val) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h U

attribute [local irreducible] evaluationPresheaf evaluationBilinear evaluationSection

private theorem tensorLift_fac (A B N : Modules.{u, v, w} R)
    (q : A.val ⊗ B.val ⟶ N.val) :
    let adj := PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    (adj.unit.app (A.val ⊗ B.val) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val) ≫
      (tensorLift R A B N q).val = q := by
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := SheafOfModules.tensorObjIsoSheafification (R := R) A B
  have hi : e.inv.val ≫ e.hom.val = 𝟙 _ :=
    congrArg SheafOfModules.Hom.val e.inv_hom_id
  have h := (adj.homEquiv _ N).apply_symm_apply q
  change adj.unit.app _ ≫ ((adj.homEquiv _ _).symm q).val = q at h
  change (adj.unit.app _ ≫ e.inv.val) ≫
    (e.hom.val ≫ ((adj.homEquiv _ _).symm q).val) = q
  rw [Category.assoc, ← Category.assoc e.inv.val, hi, Category.id_comp]
  exact h

private theorem moduleEvaluation_spec (A B : Modules.{u, v, w} R) :
    IsModuleEvaluation R A B (moduleEvaluation R A B) := by
  intro U y φ V x
  have h := congrArg
    (fun f ↦ (((f.app U).hom (y ⊗ₜ[R.obj.obj U] φ)).app V).hom x)
    (tensorLift_fac R B (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R)))
      (SheafOfModules.homObj A B) (evaluationPresheaf R A B))
  change ((((moduleEvaluation R A B).val.app U).hom
      (pureTensor R B (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))) U y φ)).app
        V).hom x = _ at h
  refine h.trans ?_
  simp only [evaluationPresheaf, ModuleCat.hom_ofHom]
  erw [TensorProduct.lift.tmul]
  exact evaluationBilinear_apply R A B U y φ V x

private theorem moduleEvaluation_natural_left {A A' : Modules.{u, v, w} R}
    (f : A' ⟶ A) (B : Modules.{u, v, w} R) :
    B ◁ SheafOfModules.homObjMap f (𝟙 _) ≫ moduleEvaluation R A' B =
      moduleEvaluation R A B ≫ SheafOfModules.homObjMap f (𝟙 B) := by
  rw [← id_tensorHom]
  apply tensor_ext R
  intro U y φ
  change (moduleEvaluation R A' B).val.app U
      ((𝟙 B ⊗ₘ SheafOfModules.homObjMap f (𝟙 _)).val.app U
        (pureTensor R B _ U y φ)) = _
  rw [pureTensor_map]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((moduleEvaluation R A' B).val.app U
      (pureTensor R B _ U y ((SheafOfModules.homObjMap f (𝟙 _)).val.app U φ))).app V).hom x =
    (((moduleEvaluation R A B).val.app U (pureTensor R B _ U y φ)).app V).hom
      ((f.val.app (op V.unop.left)).hom x)
  rw [moduleEvaluation_spec R A' B, moduleEvaluation_spec R A B]
  rfl

attribute [local semireducible] SheafOfModules.monoidalCategory

private theorem moduleEvaluation_natural_right (A : Modules.{u, v, w} R)
    {B B' : Modules.{u, v, w} R} (g : B ⟶ B') :
    g ▷ SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R)) ≫ moduleEvaluation R A B' =
      moduleEvaluation R A B ≫ SheafOfModules.homObjMap (𝟙 A) g := by
  rw [← tensorHom_id]
  apply tensor_ext R
  intro U y φ
  change (moduleEvaluation R A B').val.app U
      ((g ⊗ₘ 𝟙 _).val.app U (pureTensor R B _ U y φ)) = _
  rw [pureTensor_map]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((moduleEvaluation R A B').val.app U
      (pureTensor R B' _ U ((g.val.app U).hom y) φ)).app V).hom x =
    (g.val.app (op V.unop.left)).hom
      ((((moduleEvaluation R A B).val.app U (pureTensor R B _ U y φ)).app V).hom x)
  rw [moduleEvaluation_spec R A B', moduleEvaluation_spec R A B]
  change (show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
      B'.val.map V.unop.hom.op ((g.val.app U).hom y) =
    (g.val.app (op V.unop.left)).hom
      ((show R.obj.obj (op V.unop.left) from (φ.app V).hom x) •
        B.val.map V.unop.hom.op y)
  rw [map_smul]
  have hg := PresheafOfModules.naturality_apply g.val V.unop.hom.op y
  rw [hg]

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] tensorLift moduleEvaluation

private def evaluationComponent (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p q n r t : ℤ) (hpq : p + q = n) (hrt : r + n = t) :
    F.X p ⊗ (dual R E).X q ⟶ SheafOfModules.homObj (E.X r) (F.X t) := by
  classical
  by_cases h : r + q = 0
  · have ht : t = p := by omega
    exact F.X p ◁ dualProjection R E q r h ≫
      moduleEvaluation R (E.X r) (F.X p) ≫
        SheafOfModules.homObjMap (𝟙 (E.X r)) (eqToHom (congrArg F.X ht.symm))
  · exact 0

private theorem evaluationComponent_supported
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) (hrq : r + q = 0) (hrn : r + n = p) :
    evaluationComponent R E F p q n r p hpq hrn =
      F.X p ◁ dualProjection R E q r hrq ≫ moduleEvaluation R (E.X r) (F.X p) := by
  simp only [evaluationComponent, dite_eq_left hrq, eqToHom_refl,
    SheafOfModules.homObjMap_id, Category.comp_id]

private theorem evaluationComponent_zero
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p q n r t : ℤ) (hpq : p + q = n) (hrt : r + n = t) (hrq : r + q ≠ 0) :
    evaluationComponent R E F p q n r t hpq hrt = 0 := by
  simp only [evaluationComponent, dite_eq_right hrq]

attribute [local irreducible] evaluationComponent

private def evaluationDegree (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (n : ℤ) :
    (total R E F).X n ⟶ (homComplex E F).X n :=
  HomologicalComplex.mapBifunctorDesc (K₁ := F) (K₂ := dual R E)
    (F := curriedTensor (Modules.{u, v, w} R)) (c := .up ℤ) fun p q hpq ↦
      (homComplexIsLimit E F n).lift
        (Fan.mk _ fun r : ℤ ↦ evaluationComponent R E F p q n r (r + n) hpq rfl)

@[reassoc]
private theorem evaluationDegree_component
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p q n r t : ℤ) (hpq : p + q = n) (hrt : r + n = t) :
    inclusion R E F p q n hpq ≫ evaluationDegree R E F n ≫
        homComplexπ E F n r t hrt = evaluationComponent R E F p q n r t hpq hrt := by
  subst t
  rw [← Category.assoc]
  unfold inclusion evaluationDegree
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  exact (homComplexIsLimit E F n).fac _ (Discrete.mk r)

attribute [local irreducible] evaluationDegree

private lemma biproduct_transport {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type*} (S : I → C) [HasBiproduct S] {i j : I} (hij : i = j)
    (h : S i = S j) : eqToHom h ≫ biproduct.ι S j = biproduct.ι S i := by
  subst j
  simp

private lemma finiteTensorBiproduct {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
    (F D : CochainComplex C ℤ) [F.HasMapBifunctor D (curriedTensor C)]
    (a b n : ℤ) (hbounded : ∀ q : ℤ, -q < a ∨ b < -q → IsZero (D.X q)) :
    ∃ e : (⨁ fun r : ↥(Finset.Icc a b) ↦ F.X (r.val + n) ⊗ D.X (-r.val)) ≅
        (CochainComplex.mapBifunctor F D (curriedTensor C)).X n,
      ∀ r : ↥(Finset.Icc a b), biproduct.ι _ r ≫ e.hom =
        HomologicalComplex.ιMapBifunctor F D (curriedTensor C) (.up ℤ)
          (r.val + n) (-r.val) n (by change r.val + n + -r.val = n; omega) := by
  classical
  let S : ↥(Finset.Icc a b) → C := fun r ↦
    F.X (r.val + n) ⊗ D.X (-r.val)
  let inclusion : ∀ r, S r ⟶ (CochainComplex.mapBifunctor F D (curriedTensor C)).X n := fun r ↦
    HomologicalComplex.ιMapBifunctor F D
      (curriedTensor _) (.up ℤ) (r.val + n) (-r.val) n (by
        change r.val + n + -r.val = n
        omega)
  let toTotal : (⨁ S) ⟶ (CochainComplex.mapBifunctor F D (curriedTensor C)).X n :=
    biproduct.desc inclusion
  let component : ∀ (p q : ℤ) (_ : p + q = n),
      (F.X p ⊗ D.X q ⟶ ⨁ S) := fun p q hpq ↦
    if hq : -q ∈ Finset.Icc a b then
      eqToHom (by
        have hp : p = -q + n := by omega
        simp only [S, hp, neg_neg]) ≫ biproduct.ι S ⟨-q, hq⟩
    else 0
  let fromTotal : (CochainComplex.mapBifunctor F D (curriedTensor C)).X n ⟶ (⨁ S) :=
    HomologicalComplex.mapBifunctorDesc (K₁ := F) (K₂ := D)
      (F := curriedTensor _) (c := .up ℤ) component
  have hleft : toTotal ≫ fromTotal = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro r
    dsimp only [toTotal]
    rw [biproduct.ι_desc_assoc]
    dsimp only [inclusion, fromTotal]
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    dsimp only [component]
    rw [dite_eq_left (by simpa only [neg_neg] using r.property)]
    have hr : (⟨- -r.val, by simpa only [neg_neg] using r.property⟩ :
        ↥(Finset.Icc a b)) = r := by
      apply Subtype.ext
      exact neg_neg r.val
    simp only [Category.comp_id]
    exact biproduct_transport S hr.symm _
  have hright : fromTotal ≫ toTotal = 𝟙 _ := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [← Category.assoc]
    dsimp only [fromTotal]
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    change p + q = n at hpq
    dsimp only [component]
    by_cases hq : -q ∈ Finset.Icc a b
    · rw [dite_eq_left hq]
      have hp : p = -q + n := by omega
      subst p
      dsimp only [toTotal]
      rw [Category.assoc, biproduct.ι_desc]
      dsimp only [inclusion]
      simp only [Category.comp_id]
      have transport : ∀ (q' : ℤ) (_ : q = q')
          (hh : F.X (-q + n) ⊗ D.X q = F.X (-q + n) ⊗ D.X q')
          (h : -q + n + q' = n),
          eqToHom hh ≫ HomologicalComplex.ιMapBifunctor F D (curriedTensor C)
            (.up ℤ) (-q + n) q' n h =
          HomologicalComplex.ιMapBifunctor F D (curriedTensor C)
            (.up ℤ) (-q + n) q n hpq := by
        intro q' hq'
        subst q'
        intro hh h
        simp
      exact transport _ (neg_neg q).symm _ _
    · rw [dite_eq_right hq]
      have hzero : IsZero (D.X q) :=
        hbounded q (by
          simpa only [Finset.mem_Icc, not_and_or, not_le] using hq)
      exact ((tensorLeft (F.X p)).map_isZero hzero).eq_of_src _ _
  refine ⟨⟨toTotal, fromTotal, hleft, hright⟩, ?_⟩
  intro r
  exact biproduct.ι_desc inclusion r

private theorem homObj_isZero_left (A B : Modules.{u, v, w} R) (hA : IsZero A) :
    IsZero (SheafOfModules.homObj (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := A) (N := B),
    (IsZero.iff_id_eq_zero A).mp hA]
  apply SheafOfModules.hom_ext
  ext V φ : 3
  change (PresheafOfModules.restrictOver _ V.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver _ V.unop).map (𝟙 B.val) = 0
  ext W x
  change (φ.app W).hom (0) = 0
  exact map_zero _

private theorem targetBiproduct
    (P F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b n : ℤ)
    (hbounded : ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r)) :
    ∃ e : (homComplex (R := R) P F).X n ≅
        (⨁ fun r : ↥(Finset.Icc a b) ↦
          SheafOfModules.homObj (R := R) (P.X r.val) (F.X (r.val + n))),
      ∀ r : ↥(Finset.Icc a b),
        e.hom ≫ biproduct.π _ r =
          homComplexπ P F n r.val (r.val + n) rfl := by
  classical
  let T : ↥(Finset.Icc a b) → Modules.{u, v, w} R := fun r ↦
    SheafOfModules.homObj (R := R) (P.X r.val) (F.X (r.val + n))
  let H := (homComplex (R := R) P F).X n
  let π : ∀ r : ℤ, H ⟶
      SheafOfModules.homObj (R := R) (P.X r) (F.X (r + n)) :=
    fun r ↦ homComplexπ P F n r (r + n) rfl
  have hlim : IsLimit (Fan.mk H π) :=
    homComplexIsLimit P F n
  let f : H ⟶ ⨁ T := biproduct.lift fun r ↦ π r.val
  let cone : Fan (fun r : ℤ ↦
      SheafOfModules.homObj (R := R) (P.X r) (F.X (r + n))) :=
    Fan.mk (⨁ T) fun r ↦ if hr : r ∈ Finset.Icc a b then biproduct.π T ⟨r, hr⟩ else 0
  let g : (⨁ T) ⟶ H := hlim.lift cone
  have hg (r : ℤ) : g ≫ π r =
      if hr : r ∈ Finset.Icc a b then biproduct.π T ⟨r, hr⟩ else 0 :=
    hlim.fac cone (Discrete.mk r)
  have hfg : f ≫ g = 𝟙 H := by
    apply hlim.hom_ext
    intro j
    rcases j with ⟨r⟩
    change (f ≫ g) ≫ π r = 𝟙 H ≫ π r
    rw [Category.assoc, hg]
    by_cases hr : r ∈ Finset.Icc a b
    · simp [hr, f]
    · have hz : IsZero (SheafOfModules.homObj (R := R)
          (P.X r) (F.X (r + n))) := by
        apply homObj_isZero_left R _ _
        apply hbounded r
        simp only [Finset.mem_Icc, not_and_or, not_le] at hr
        exact hr
      exact hz.eq_of_tgt _ _
  have hgf : g ≫ f = 𝟙 (⨁ T) := by
    apply biproduct.hom_ext
    intro r
    simp only [Category.assoc, f, biproduct.lift_π, Category.id_comp]
    rw [hg]
    simp
  let e : H ≅ ⨁ T := { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }
  change ∃ e : H ≅ ⨁ T, ∀ r : ↥(Finset.Icc a b),
    e.hom ≫ biproduct.π T r = π r.val
  exact ⟨e, fun r ↦ biproduct.lift_π _ r⟩

private theorem homObjMap_zero_target {A B B' : Modules.{u, v, w} R}
    (f : A ⟶ A) : SheafOfModules.homObjMap (R := R) f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem homObj_isZero_right (A B : Modules.{u, v, w} R) (hB : IsZero B) :
    IsZero (SheafOfModules.homObj A B) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id,
    hB.eq_of_tgt (𝟙 _) 0]
  exact homObjMap_zero_target R _

private theorem homObjMap_isIso_target (A : Modules.{u, v, w} R)
    {B B' : Modules.{u, v, w} R} (e : B ≅ B') :
    IsIso (SheafOfModules.homObjMap (𝟙 A) e.hom) := by
  refine ⟨⟨SheafOfModules.homObjMap (𝟙 A) e.inv, ?_, ?_⟩⟩
  · rw [SheafOfModules.homObjMap_comp_homObjMap]
    simp only [Category.id_comp, Iso.hom_inv_id, SheafOfModules.homObjMap_id]
  · rw [SheafOfModules.homObjMap_comp_homObjMap]
    simp only [Category.id_comp, Iso.inv_hom_id, SheafOfModules.homObjMap_id]

private theorem isIso_dependent {D : Type*} [Category D] {A : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (A ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

private theorem dualProjection_isIso (E : CochainComplex (Modules.{u, v, w} R) ℤ)
    (q i : ℤ) (hi : i + q = 0) : IsIso (dualProjection R E q i hi) := by
  classical
  let M := unitComplex R
  let Q := fun p : ℤ ↦ SheafOfModules.homObj (E.X p) (M.X (p + q))
  let H := (dual R E).X q
  let π := fun p : ℤ ↦ homComplexπ E M q p (p + q) rfl
  have hc : IsLimit (Fan.mk H π) := homComplexIsLimit E M q
  have hz (p : ℤ) (h : p ≠ i) : IsZero (Q p) := by
    apply homObj_isZero_right R
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (𝟙_ (Modules.{u, v, w} R)) (p + q) (by omega)
  let v : Q i ⟶ H := Fan.IsLimit.lift hc
    (fun p ↦ if h : p = i then eqToHom (congrArg Q h.symm) else 0)
  have hv : v ≫ π i = 𝟙 (Q i) := by
    change Fan.IsLimit.lift hc _ ≫ (Fan.mk H π).proj i = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ : π i ≫ v = 𝟙 H := by
    apply Fan.IsLimit.hom_ext hc
    intro p
    change (π i ≫ v) ≫ π p = 𝟙 H ≫ π p
    by_cases h : p = i
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz p h).eq_of_tgt _ _
  have hπiso : IsIso (homComplexπ E M q i 0 hi) := by
    have h : IsIso (π i) := (Iso.mk (π i) v hπ hv).isIso_hom
    exact isIso_dependent (fun t h ↦ homComplexπ E M q i t h) hi h
  unfold dualProjection
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules.{u, v, w} R))
  have hs : IsIso (SheafOfModules.homObjMap (𝟙 (E.X i)) e.hom) :=
    homObjMap_isIso_target R (E.X i) e
  exact IsIso.comp_isIso

private theorem dualProjection_d (E : CochainComplex (Modules.{u, v, w} R) ℤ)
    (q r : ℤ) (hr : r + (q + 1) = 0) :
    (dual R E).d q (q + 1) ≫ dualProjection R E (q + 1) r hr =
      (q + 1).negOnePow • (dualProjection R E q (r + 1) (by omega) ≫
        SheafOfModules.homObjMap (E.d r (r + 1)) (𝟙 _)) := by
  have hd := homComplex_d_π E (unitComplex R) q (q + 1) r 0 (-1) (r + 1)
    rfl hr (by omega) (by omega)
  unfold dualProjection dual
  rw [← Category.assoc, hd]
  have hz : SheafOfModules.homObjMap (𝟙 (E.X r)) ((unitComplex R).d (-1) 0) = 0 := by
    change SheafOfModules.homObjMap (𝟙 _) (0 : (unitComplex R).X (-1) ⟶ _) = 0
    exact homObjMap_zero_target R _
  rw [hz, comp_zero, zero_sub]
  simp only [Int.negOnePow_succ, Units.neg_smul, Preadditive.neg_comp,
    Linear.units_smul_comp, Category.assoc]
  congr 2

private theorem sourceBiproduct (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (a b n : ℤ) (hbounded : ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i))
    (δ : ∀ i : ℤ, (dual R E).X (-i) ≅
      SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R))) :
    ∃ s : biproduct (sourceFamily R E F a b n) ≅ (total R E F).X n,
      ∀ i : ↥(Finset.Icc a b),
        biproduct.ι (sourceFamily R E F a b n) i ≫ s.hom =
          F.X (i.val + n) ◁ (δ i.val).inv ≫
            inclusion R E F (i.val + n) (-i.val) n (by omega) := by
  have hD (q : ℤ) (hq : -q < a ∨ b < -q) : IsZero ((dual R E).X q) := by
    have h := homObj_isZero_left R (E.X (-q)) (𝟙_ (Modules.{u, v, w} R))
      (hbounded (-q) hq)
    have hi := dualProjection_isIso R E q (-q) (neg_add_cancel q)
    exact h.of_iso (asIso (dualProjection R E q (-q) (neg_add_cancel q)))
  obtain ⟨e, he⟩ := finiteTensorBiproduct F (dual R E) a b n hD
  let d (i : ↥(Finset.Icc a b)) : sourceFamily R E F a b n i ≅
      F.X (i.val + n) ⊗ (dual R E).X (-i.val) :=
    (tensorLeft (F.X (i.val + n))).mapIso (δ i.val).symm
  refine ⟨biproduct.mapIso d ≪≫ e, ?_⟩
  intro i
  simp only [Iso.trans_hom, biproduct.mapIso_hom, biproduct.ι_map_assoc, he]
  rfl

private theorem whiskerLeft_units_smul (A : Modules.{u, v, w} R)
    {B B' : Modules.{u, v, w} R} (r : ℤˣ) (f : B ⟶ B') :
    A ◁ (r • f) = r • (A ◁ f) := by
  change (tensorLeft A).map ((r : ℤ) • f) = (r : ℤ) • (tensorLeft A).map f
  exact (tensorLeft A).map_zsmul

private theorem total_d (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (p q : ℤ) :
    inclusion R E F p q (p + q) rfl ≫ (total R E F).d (p + q) (p + q + 1) =
      F.d p (p + 1) ▷ (dual R E).X q ≫
          inclusion R E F (p + 1) q (p + q + 1) (by omega) +
        p.negOnePow • (F.X p ◁ (dual R E).d q (q + 1) ≫
          inclusion R E F p (q + 1) (p + q + 1) (by omega)) := by
  unfold inclusion total
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)
      q (p + q + 1) (by change p + 1 + q = p + q + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (p + q + 1)
      (by change p + (q + 1) = p + q + 1; omega)]
  change (1 : ℤˣ) • _ + p.negOnePow • _ = _
  rw [one_smul]
  rfl

private theorem evaluationComponent_d₁
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p p' q n m r t t' : ℤ) (hpq : p + q = n) (hpq' : p' + q = m)
    (hrt : r + n = t) (hrt' : r + m = t') :
    F.d p p' ▷ (dual R E).X q ≫
        evaluationComponent R E F p' q m r t' hpq' hrt' =
      evaluationComponent R E F p q n r t hpq hrt ≫
        SheafOfModules.homObjMap (𝟙 (E.X r)) (F.d t t') := by
  by_cases hr : r + q = 0
  · have ht : t = p := by omega
    have ht' : t' = p' := by omega
    cases ht
    cases ht'
    rw [evaluationComponent_supported R E F _ _ _ _ hpq' hr (by omega),
      evaluationComponent_supported R E F _ _ _ _ hpq hr (by omega)]
    rw [← Category.assoc, ← whisker_exchange, Category.assoc,
      moduleEvaluation_natural_right R]
    simp only [Category.assoc]
  · rw [evaluationComponent_zero R E F _ _ _ _ _ _ _ hr,
      evaluationComponent_zero R E F _ _ _ _ _ _ _ hr, comp_zero, zero_comp]

private theorem evaluationComponent_d₂
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p q r n m t : ℤ) (hpq : p + q = n) (hpq' : p + (q + 1) = m)
    (hrt : r + m = t) (hrt' : r + 1 + n = t) :
    F.X p ◁ (dual R E).d q (q + 1) ≫
        evaluationComponent R E F p (q + 1) m r t hpq' hrt =
      (q + 1).negOnePow •
        (evaluationComponent R E F p q n (r + 1) t hpq hrt' ≫
            SheafOfModules.homObjMap (E.d r (r + 1)) (𝟙 _)) := by
  by_cases hr : r + (q + 1) = 0
  · have hr' : r + 1 + q = 0 := by omega
    have ht : t = p := by omega
    cases ht
    rw [evaluationComponent_supported R E F _ _ _ _ hpq' hr (by omega),
      evaluationComponent_supported R E F _ _ _ _ hpq hr' (by omega)]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, dualProjection_d R E q r hr,
      whiskerLeft_units_smul, Linear.units_smul_comp,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, moduleEvaluation_natural_left R]
    simp only [Category.assoc]
  · have hr' : r + 1 + q ≠ 0 := by omega
    rw [evaluationComponent_zero R E F _ _ _ _ _ _ _ hr,
      evaluationComponent_zero R E F _ _ _ _ _ _ _ hr', comp_zero, zero_comp, smul_zero]

private theorem evaluationDegree_comm
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (n m : ℤ)
    (hnm : n + 1 = m) :
    evaluationDegree R E F n ≫ (homComplex E F).d n m =
      (total R E F).d n m ≫ evaluationDegree R E F m := by
  subst m
  dsimp only [total, CochainComplex.mapBifunctor]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  subst n
  apply homComplex_hom_ext
  intro r t hrt
  subst t
  change inclusion R E F p q (p + q) rfl ≫
      (evaluationDegree R E F (p + q) ≫ (homComplex E F).d _ _) ≫
        homComplexπ E F (p + q + 1) r (r + (p + q + 1)) rfl =
    inclusion R E F p q (p + q) rfl ≫
      (total R E F).d _ _ ≫ evaluationDegree R E F (p + q + 1) ≫
        homComplexπ E F (p + q + 1) r (r + (p + q + 1)) rfl
  simp only [Category.assoc]
  rw [homComplex_d_π E F (p + q) (p + q + 1) r (r + (p + q + 1))
    (r + (p + q)) (r + 1) rfl rfl rfl (by omega)]
  simp only [Preadditive.comp_sub, Linear.comp_units_smul]
  rw [evaluationDegree_component_assoc, evaluationDegree_component_assoc]
  symm
  rw [← Category.assoc (inclusion R E F p q (p + q) rfl), total_d R E F p q]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
  rw [evaluationDegree_component, evaluationDegree_component,
    evaluationComponent_d₁ R E F p (p + 1) q (p + q) (p + q + 1) r
      (r + (p + q)) (r + (p + q + 1)) rfl (by omega) rfl rfl,
    evaluationComponent_d₂ R E F p q r (p + q) (p + q + 1)
      (r + (p + q + 1)) rfl (by omega) rfl (by omega)]
  rw [smul_smul, ← Int.negOnePow_add]
  have hs : p + (q + 1) = p + q + 1 := by omega
  rw [hs, Int.negOnePow_succ, Units.neg_smul]
  simp only [sub_eq_add_neg]

private def evaluationMap (E F : CochainComplex (Modules.{u, v, w} R) ℤ) :
    total R E F ⟶ homComplex E F where
  f := evaluationDegree R E F
  comm' n m h := evaluationDegree_comm R E F n m h

private theorem evaluationDegree_matrix
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b n : ℤ)
    (δ : ∀ i : ℤ, (dual R E).X (-i) ≅
      SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)))
    (hδ : ∀ i : ℤ, (δ i).hom = dualProjection R E (-i) i (by omega))
    (s : biproduct (sourceFamily R E F a b n) ≅ (total R E F).X n)
    (t : (homComplex E F).X n ≅ biproduct (targetFamily R E F a b n))
    (hs : ∀ i : ↥(Finset.Icc a b),
      biproduct.ι (sourceFamily R E F a b n) i ≫ s.hom =
        F.X (i.val + n) ◁ (δ i.val).inv ≫
          inclusion R E F (i.val + n) (-i.val) n (by omega))
    (ht : ∀ i : ↥(Finset.Icc a b),
      t.hom ≫ biproduct.π (targetFamily R E F a b n) i =
        homComplexπ E F n i.val (i.val + n) rfl) :
    s.hom ≫ evaluationDegree R E F n ≫ t.hom =
      biproduct.map (fun i : ↥(Finset.Icc a b) ↦
        moduleEvaluation R (E.X i.val) (F.X (i.val + n))) := by
  classical
  dsimp only [sourceFamily, targetFamily] at *
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [sourceFamily, targetFamily] at *
  simp only [Category.assoc]
  rw [ht]
  simp only [← Category.assoc]
  rw [hs]
  simp only [Category.assoc]
  rw [evaluationDegree_component]
  by_cases hij : i = j
  · subst j
    rw [evaluationComponent_supported R E F _ _ _ _ _ (add_neg_cancel i.val)]
    rw [← hδ i.val, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id]
    simp only [sourceFamily, Category.id_comp,
      biproduct.ι_map_assoc, biproduct.ι_π_self, Category.comp_id]
  · have hr : j.val + -i.val ≠ 0 := by
      intro h
      apply hij
      apply Subtype.ext
      omega
    rw [evaluationComponent_zero R E F _ _ _ _ _ _ _ hr, comp_zero]
    simp only [sourceFamily, biproduct.ι_map_assoc,
      biproduct.ι_π_ne _ hij, comp_zero]

attribute [local semireducible] SheafOfModules.monoidalCategory

private theorem evaluationDegree_slice
    (E F : CochainComplex (Modules.{u, v, w} R) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) (hrq : r + q = 0) (hrn : r + n = p)
    (U : Cᵒᵖ) (y : (F.X p).val.obj U) (φ : ((dual R E).X q).val.obj U)
    (V : (Over U.unop)ᵒᵖ) (x : (E.X r).val.obj (op V.unop.left)) :
    ((((homComplexπ E F n r p hrn).val.app U).hom
      (((inclusion R E F p q n hpq ≫ evaluationDegree R E F n).val.app U).hom
        (pureTensor R (F.X p) ((dual R E).X q) U y φ))).app V).hom x =
      (show R.obj.obj (op V.unop.left) from
        ((((dualProjection R E q r hrq).val.app U).hom φ).app V).hom x) •
        (F.X p).val.map V.unop.hom.op y := by
  have h := evaluationDegree_component R E F p q n r p hpq hrn
  rw [evaluationComponent_supported R E F p q n r hpq hrq hrn] at h
  have he := congrArg (fun k ↦ (((k.val.app U).hom
    (pureTensor R (F.X p) ((dual R E).X q) U y φ)).app V).hom x) h
  change _ = _ at he
  rw [← id_tensorHom] at he
  change _ = ((((moduleEvaluation R (E.X r) (F.X p)).val.app U).hom
    (((𝟙 (F.X p) ⊗ₘ dualProjection R E q r hrq).val.app U).hom
      (pureTensor R (F.X p) ((dual R E).X q) U y φ))).app V).hom x at he
  rw [pureTensor_map] at he
  exact he.trans (moduleEvaluation_spec R (E.X r) (F.X p) U y
    ((dualProjection R E q r hrq).val.app U φ) V x)

/-- Finite-support assembly of the actual ordinary tensor-Hom evaluation.
Source: Stacks 08JJ, last three displays of `lemma-dual-perfect-complex`, and
0A8X, the Hom and total tensor differentials.
(blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly).

Proof: (1) Project the dual onto Hom(E^i,R) in degree -i; all other factors
vanish. Inserting zero maps in the other factors constructs the inverse by
the product universal property. Project its Hom differential to obtain its sign.
(2) Discard zero tensor summands outside the finite interval and reindex by
(p,q)=(i+n,-i). The coproduct universal property gives the source identification.
Zero tensor factors follow sectionwise and then by module sheafification.
(3) Discard zero Hom factors outside that interval. The remaining finite product
is the biproduct: its inclusions have identity diagonal and zero off-diagonal,
and the sum of inclusion-projection composites is the identity.
(4) The slice formula y tensor phi maps to (x maps to phi(x) times y) is balanced
and compatible with restriction. Sheafification and the coproduct universal
property give the degree maps. The analogous construction defines theta.
(5) On a pure tensor in degrees p,q, the tensor differential gives d_F y tensor
phi + (-1)^(p+q+1) y tensor (phi d_E). The Hom differential gives d_F f -
(-1)^(p+q) f d_E. Both have the same two components, at -q and -q-1, and zero
elsewhere, so the maps form a chain map without an additional sign.
(6) Under the specified identifications its matrix is diagonal with blocks theta.
(7) The finite diagonal of the inverses of theta is an inverse in each degree;
this includes the empty interval and requires no bound on F.
(8) Invert the chain-map equation to show that these degreewise inverses form
an inverse chain map. These eight steps are the node's complete proof plan.

The first existential constructs the canonical module comparisons and pins their
values on all slices. The implication then imposes precisely their invertibility,
so no additional existence assumption about those comparisons is needed. -/
theorem assembly (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b : ℤ)
    (hbounded : ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) :
    ∃ θ : ∀ (i : ℤ) (M : Modules.{u, v, w} R),
      M ⊗ SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)) ⟶
        SheafOfModules.homObj (E.X i) M,
    (∀ (i : ℤ) (M : Modules.{u, v, w} R), IsModuleEvaluation.{u, v, w} R (E.X i) M (θ i M)) ∧
    ((∀ (i : ℤ) (M : Modules.{u, v, w} R), IsIso (θ i M)) →
      ∃ ε : total.{u, v, w} R E F ≅ homComplex E F,
      ∃ δ : ∀ i : ℤ,
        (dual.{u, v, w} R E).X (-i) ≅ SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)),
      (∀ i : ℤ, (δ i).hom = dualProjection.{u, v, w} R E (-i) i (by omega)) ∧
      (∀ (p q n r : ℤ) (hpq : p + q = n) (hrq : r + q = 0)
        (hrn : r + n = p) (U : Cᵒᵖ) (y : (F.X p).val.obj U)
        (φ : ((dual.{u, v, w} R E).X q).val.obj U)
        (V : (Over U.unop)ᵒᵖ) (x : (E.X r).val.obj (op V.unop.left)),
        ((((homComplexπ E F n r p hrn).val.app U).hom
          (((inclusion.{u, v, w} R E F p q n hpq ≫ ε.hom.f n).val.app U).hom
            (pureTensor.{u, v, w} R (F.X p) ((dual.{u, v, w} R E).X q) U y φ))).app V).hom x =
          ((((dualProjection.{u, v, w} R E q r hrq).val.app U).hom φ).app V).hom x •
            (F.X p).val.map V.unop.hom.op y) ∧
      (∀ (p q n r t : ℤ) (hpq : p + q = n) (hrt : r + n = t) (_hrq : r + q ≠ 0),
        inclusion.{u, v, w} R E F p q n hpq ≫ ε.hom.f n ≫
          homComplexπ E F n r t hrt = 0) ∧
      (∀ n : ℤ,
        ∃ s : biproduct (sourceFamily.{u, v, w} R E F a b n) ≅ (total.{u, v, w} R E F).X n,
        ∃ t : (homComplex E F).X n ≅ biproduct (targetFamily.{u, v, w} R E F a b n),
        (∀ i : ↥(Finset.Icc a b),
          biproduct.ι (sourceFamily.{u, v, w} R E F a b n) i ≫ s.hom =
            F.X (i.val + n) ◁ (δ i.val).inv ≫
              inclusion.{u, v, w} R E F
                (i.val + n) (-i.val) n (by omega)) ∧
        (∀ i : ↥(Finset.Icc a b),
          t.hom ≫ biproduct.π (targetFamily.{u, v, w} R E F a b n) i =
            homComplexπ E F n i.val (i.val + n) rfl) ∧
        s.hom ≫ ε.hom.f n ≫ t.hom =
          biproduct.map (fun i : ↥(Finset.Icc a b) ↦ θ i.val (F.X (i.val + n)))) ∧
      (∀ (p q r : ℤ),
        inclusion.{u, v, w} R E F
            p q (p + q) rfl ≫
          (total.{u, v, w} R E F).d (p + q) (p + q + 1) ≫ ε.hom.f (p + q + 1) ≫
          homComplexπ E F (p + q + 1) r (r + (p + q + 1)) rfl =
        inclusion.{u, v, w} R E F
            p q (p + q) rfl ≫ ε.hom.f (p + q) ≫
          (homComplexπ E F (p + q) r (r + (p + q)) rfl ≫
            SheafOfModules.homObjMap (𝟙 (E.X r))
              (F.d (r + (p + q)) (r + (p + q + 1))) -
            (p + q).negOnePow •
              (homComplexπ E F (p + q) (r + 1) (r + (p + q + 1)) (by omega) ≫
                SheafOfModules.homObjMap (E.d r (r + 1)) (𝟙 _)))) ∧
      (∀ n : ℤ, IsIso (ε.hom.f n)) ∧
      (∀ n : ℤ, ε.inv.f n ≫ ε.hom.f n = 𝟙 _ ∧ ε.hom.f n ≫ ε.inv.f n = 𝟙 _)) := by
  classical
  let θ := fun (i : ℤ) (M : Modules.{u, v, w} R) ↦ moduleEvaluation R (E.X i) M
  refine ⟨θ, fun i M ↦ moduleEvaluation_spec R (E.X i) M, ?_⟩
  intro hθ
  let δ : ∀ i : ℤ, (dual R E).X (-i) ≅
      SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)) := fun i ↦
    @asIso _ _ _ _ (dualProjection R E (-i) i (add_neg_cancel i))
      (dualProjection_isIso R E (-i) i (add_neg_cancel i))
  have hδ : ∀ i : ℤ, (δ i).hom = dualProjection R E (-i) i (by omega) := fun _ ↦ rfl
  have hdecomp (n : ℤ) :
      ∃ s : biproduct (sourceFamily R E F a b n) ≅ (total R E F).X n,
      ∃ t : (homComplex E F).X n ≅ biproduct (targetFamily R E F a b n),
      (∀ i : ↥(Finset.Icc a b),
        biproduct.ι (sourceFamily R E F a b n) i ≫ s.hom =
          F.X (i.val + n) ◁ (δ i.val).inv ≫
            inclusion R E F (i.val + n) (-i.val) n (by omega)) ∧
      (∀ i : ↥(Finset.Icc a b),
        t.hom ≫ biproduct.π (targetFamily R E F a b n) i =
          homComplexπ E F n i.val (i.val + n) rfl) ∧
      s.hom ≫ evaluationDegree R E F n ≫ t.hom =
        biproduct.map (fun i : ↥(Finset.Icc a b) ↦ θ i.val (F.X (i.val + n))) := by
    obtain ⟨s, hs⟩ := sourceBiproduct R E F a b n hbounded δ
    obtain ⟨t, ht⟩ := targetBiproduct R E F a b n hbounded
    exact ⟨s, t, hs, ht, evaluationDegree_matrix R E F a b n δ hδ s t hs ht⟩
  have hi (n : ℤ) : IsIso ((evaluationMap R E F).f n) := by
    obtain ⟨s, t, _, _, heq⟩ := hdecomp n
    have hblocks (i : ↥(Finset.Icc a b)) : IsIso (θ i.val (F.X (i.val + n))) := hθ _ _
    have heq' : evaluationDegree R E F n =
        s.inv ≫ (biproduct.mapIso fun i : ↥(Finset.Icc a b) ↦
          asIso (θ i.val (F.X (i.val + n)))).hom ≫ t.inv := by
      simp only [biproduct.mapIso_hom]
      calc
        evaluationDegree R E F n = s.inv ≫
            (s.hom ≫ evaluationDegree R E F n ≫ t.hom) ≫ t.inv := by simp
        _ = s.inv ≫ (biproduct.map
            (fun i : ↥(Finset.Icc a b) ↦ θ i.val (F.X (i.val + n)))) ≫ t.inv := by rw [heq]
        _ = s.inv ≫ (biproduct.mapIso
            (fun i : ↥(Finset.Icc a b) ↦ asIso (θ i.val (F.X (i.val + n))))).hom ≫ t.inv := by
          rfl
    change IsIso (evaluationDegree R E F n)
    rw [heq']
    infer_instance
  have : IsIso (evaluationMap R E F) := HomologicalComplex.Hom.isIso_of_components _
  let ε := asIso (evaluationMap R E F)
  refine ⟨ε, δ, hδ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact evaluationDegree_slice R E F
  · intro p q n r t hpq hrt hrq
    exact (evaluationDegree_component R E F p q n r t hpq hrt).trans
      (evaluationComponent_zero R E F p q n r t hpq hrt hrq)
  · exact hdecomp
  · intro p q r
    change inclusion R E F p q (p + q) rfl ≫
      (total R E F).d _ _ ≫ (evaluationMap R E F).f _ ≫ _ = _
    rw [← (evaluationMap R E F).comm_assoc]
    rw [homComplex_d_π E F (p + q) (p + q + 1) r (r + (p + q + 1))
      (r + (p + q)) (r + 1) rfl rfl rfl (by omega)]
    rfl
  · exact hi
  · intro n
    exact ⟨HomologicalComplex.congr_hom ε.inv_hom_id n,
      HomologicalComplex.congr_hom ε.hom_inv_id n⟩

end CategoryTheory.RingedSiteBoundedEvaluation
