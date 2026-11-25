/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
/-! # The canonical cohomology comparison for scalar extension

We use the source library's Ext-based `Modules.H`, written as its underlying
abelian-sheaf cohomology. Exact inverse image acts on Ext classes. The constant
integer sheaf comparison and the adjoint coefficient map give the cohomology map.
Naturality makes it linear for the scalar representations induced by the maps to
an affine base. Tensor extension gives `H.baseChange`. It is defined for arbitrary
commutative algebras; only bijectivity needs flatness.

The definitions share sheafification and Ext instances and name the cartesian
scheme, projections, module and adjunction unit. `cohomologyModule` states the
scalar action directly through `Sheaf.H.map`, avoiding expanded module wrappers.
`HOver` retains the displayed structure map in its type. No data is postponed.

Source: Stacks Project, Cohomology, Section 01F7 (pullback of cohomology), and
Cohomology of Schemes, Lemma 30.5.2 (Tag 02KH), the canonical comparison map.
(blueprint: def-pc-flat-cohomology-comparison)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [-instance] instAddCommGroupH moduleH
/-- The canonical sheafification instance, shared by all comparisons.
Source: Mathlib's sheafification for abelian sheaves.
(blueprint: def-pc-flat-cohomology-comparison) -/
theorem cohomologyHasSheafify (Z : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u} := by infer_instance
attribute [local instance] cohomologyHasSheafify

/-- The canonical small Ext instance, shared by all comparisons.
Source: Mathlib `IsGrothendieckAbelian.hasExt`.
(blueprint: def-pc-flat-cohomology-comparison) -/
theorem cohomologyHasExt (Z : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) := by infer_instance
attribute [local instance] cohomologyHasExt

variable {X Y : Scheme.{u}}
/-- Exact inverse image on abelian sheaves.
Source: Stacks Project, Sections 01F7 and 02KE.
(blueprint: def-pc-flat-cohomology-comparison) -/
def invImage (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (Opens.map f.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
/-- Inverse image of abelian sheaves preserves finite limits.
Source: Mathlib `lan_preservesFiniteLimits_of_flat` and
`Functor.sheafPullbackConstruction.preservesFiniteLimits`.
Proof: the preimage functor on opens is representably flat: the category of opens
whose preimage contains a given open is nonempty and cofiltered by intersection.
The cited Lan theorem gives finite-limit preservation for abelian presheaves;
left-exact sheafification and the sheaf pullback construction transfer it to sheaves.
(blueprint: lem-pc-abelian-inverse-image-finite-limits) -/
instance invImage_preservesFiniteLimits (f : X ⟶ Y) : PreservesFiniteLimits (invImage f) := by
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map f.base)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
/-- Inverse image of abelian sheaves preserves finite colimits.
Source: Mathlib `Functor.sheafAdjunctionContinuous` and
`Adjunction.leftAdjoint_preservesColimits`.
Proof: sheaf pullback is left adjoint to continuous sheaf pushforward. The cited
adjunction theorem gives preservation of all colimits, hence of finite colimits.
(blueprint: lem-pc-abelian-inverse-image-finite-colimits) -/
instance invImage_preservesFiniteColimits (f : X ⟶ Y) : PreservesFiniteColimits (invImage f) := by
  have := ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).leftAdjoint_preservesColimits
  exact inferInstanceAs (PreservesFiniteColimits
    ((Opens.map f.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)))
instance invImage_additive (f : X ⟶ Y) : (invImage f).Additive := by
  have : ((Opens.map f.base).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
    ⟨by intros; ext U x; rfl⟩
  exact ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).left_adjoint_additive

/-- The abelian-sheaf coefficient map adjoint to the underlying module morphism.
Source: Stacks Project, Sections 01F7 and 02KE.
(blueprint: def-pc-flat-cohomology-comparison) -/
def coeff (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (pushforward f).obj N) :
    (invImage f).obj ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _ |>.symm
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ)

/-- Inverse image of the constant integer sheaf is the constant integer sheaf.
Source: Stacks Project, Sections 01F7 and 02KE.
(blueprint: def-pc-flat-cohomology-comparison) -/
def constIso (f : X ⟶ Y) :
    (invImage f).obj ((constantSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  ((Opens.map f.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    isTerminalTop isTerminalTop).app (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Naturality of the adjoint coefficient maps.
Source: Stacks Project, Sections 01F7 and 02KE.
(blueprint: def-pc-flat-cohomology-comparison) -/
lemma coeff_naturality (f : X ⟶ Y) {M M' : Y.Modules} {N N' : X.Modules}
    (φ : M ⟶ (pushforward f).obj N) (ψ : M' ⟶ (pushforward f).obj N')
    (a : M ⟶ M') (b : N ⟶ N') (h : a ≫ ψ = φ ≫ (pushforward f).map b) :
    (invImage f).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map a) ≫ coeff f ψ =
      coeff f φ ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map b := by
  apply (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    f.base).homEquiv_naturality_right_square
  change (SheafOfModules.toSheaf Y.ringCatSheaf).map a ≫
      (SheafOfModules.toSheaf Y.ringCatSheaf).map ψ =
    (SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
      (SheafOfModules.toSheaf Y.ringCatSheaf).map ((pushforward f).map b)
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- Naturality of the comparison on Ext-based abelian-sheaf cohomology.
Source: Stacks Project, Section 01F7, and `Sheaf.H.mapFunctor_map`.
(blueprint: def-pc-flat-cohomology-comparison) -/
lemma sheafComparison_naturality
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    (G : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : (constantSheaf K AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ≅
      G.obj ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))))
    {F E : Sheaf J AddCommGrpCat.{u}} {F' E' : Sheaf K AddCommGrpCat.{u}}
    (φ : G.obj F ⟶ F') (ψ : G.obj E ⟶ E') (a : F ⟶ E) (b : F' ⟶ E')
    (h : G.map a ≫ ψ = φ ≫ b) (q : ℕ) (x : F.H q) :
    Sheaf.H.map ψ q (Sheaf.H.mapFunctor G e E q (Sheaf.H.map a q x)) =
      Sheaf.H.map b q (Sheaf.H.map φ q (Sheaf.H.mapFunctor G e F q x)) := by
  rw [Sheaf.H.mapFunctor_map]
  rw [← Sheaf.H.map_comp_apply, h, Sheaf.H.map_comp_apply]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Cohomology with its scalar action from the displayed morphism to Spec R.
Source: Stacks Project, Section 01F7.
(blueprint: def-pc-flat-cohomology-comparison) -/
def HOver (_f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) : Type u :=
  M.H q

instance HOver_addCommGroup (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    AddCommGroup (HOver f M q) := by
  exact instAddCommGroupH M q

/-- A scalar representation on a sheaf acts on its Ext cohomology.
Source: Mathlib's functoriality and additivity of `Sheaf.H.map`.
(blueprint: def-pc-flat-cohomology-comparison) -/
@[instance_reducible]
def cohomologyModule {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (F : Sheaf J AddCommGrpCat.{u}) (ρ : R →+* End F) (q : ℕ) : Module R (F.H q) where
  smul a x := Sheaf.H.map (ρ a).asHom q x
  one_smul x := by
    change Sheaf.H.map (ρ 1).asHom q x = x
    rw [map_one]
    exact Sheaf.H.map_id_apply x
  mul_smul a b x := by
    change Sheaf.H.map (ρ (a * b)).asHom q x =
      Sheaf.H.map (ρ a).asHom q (Sheaf.H.map (ρ b).asHom q x)
    rw [map_mul, End.mul_asHom]
    exact Sheaf.H.map_comp_apply (ρ b).asHom (ρ a).asHom x
  smul_add a x y := (Sheaf.H.map (ρ a).asHom q).map_add x y
  smul_zero a := (Sheaf.H.map (ρ a).asHom q).map_zero
  add_smul a b x := by
    change Sheaf.H.map (ρ (a + b)).asHom q x =
      Sheaf.H.map (ρ a).asHom q x + Sheaf.H.map (ρ b).asHom q x
    rw [map_add, End.add_asHom, Sheaf.H.map_add_apply]
  zero_smul x := by
    change Sheaf.H.map (ρ 0).asHom q x = 0
    rw [map_zero, End.zero_asHom]
    have h := Sheaf.H.map_add_apply (0 : F ⟶ F) 0 x
    rw [add_zero] at h
    exact left_eq_add.mp h

/-- The scalar representation on the underlying abelian sheaf of a module.
Source: the source library's `smulHom` identities and functoriality of `toSheaf`.
(blueprint: def-pc-flat-cohomology-comparison) -/
def scalarRep (M : X.Modules) :
    Γ(X, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) where
  toFun a := .of ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a))
  map_one' := End.ext (by
    change (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom 1) = 𝟙 _
    rw [smulHom_one]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_id M)
  map_zero' := End.ext (by
    change (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom 0) = 0
    rw [smulHom_zero, Functor.map_zero])
  map_add' a b := End.ext (by
    change (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom (a + b)) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a) +
        (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom b)
    rw [smulHom_add, Functor.map_add])
  map_mul' a b := End.ext (by
    change (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom (a * b)) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom b) ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a)
    rw [smulHom_mul, Functor.map_comp])

instance HOver_module (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) : Module R (HOver f M q) :=
  letI : Module Γ(X, ⊤) (HOver f M q) := moduleH M q
  Module.compHom _ (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)

variable [Algebra R S]

/-- The morphism of affine schemes induced by the scalar-extension homomorphism.
Source: Stacks Project, Sections 01F7 and 02KE.
(blueprint: def-pc-flat-cohomology-comparison) -/
def baseChangeMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The scheme in the cartesian base-change square.
Source: Stacks Project, Tag 02KH.
(blueprint: def-pc-flat-cohomology-comparison) -/
def baseChangedScheme (f : X ⟶ Spec (.of R)) : Scheme.{u} :=
  Limits.pullback f (baseChangeMap R S)

/-- Projection to the original scheme.
Source: Stacks Project, Tag 02KH.
(blueprint: def-pc-flat-cohomology-comparison) -/
def baseChangeFst (f : X ⟶ Spec (.of R)) : baseChangedScheme (S := S) f ⟶ X :=
  Limits.pullback.fst f (baseChangeMap R S)

/-- Projection to the base-changed affine base.
Source: Stacks Project, Tag 02KH.
(blueprint: def-pc-flat-cohomology-comparison) -/
def baseChangeSnd (f : X ⟶ Spec (.of R)) :
    baseChangedScheme (S := S) f ⟶ Spec (.of S) :=
  Limits.pullback.snd f (baseChangeMap R S)

/-- The module on the cartesian base change, using the module pullback functor.
Source: Stacks Project, Tag 02KH.
(blueprint: def-pc-flat-cohomology-comparison) -/
def baseChangedModule (f : X ⟶ Spec (.of R)) (M : X.Modules) :
    (baseChangedScheme (S := S) f).Modules :=
  (pullback (baseChangeFst (S := S) f)).obj M

/-- The scalar maps commute in the cartesian base-change square.
Source: Stacks Project, Sections 01F7 and 02KE.
(blueprint: def-pc-flat-cohomology-comparison) -/
lemma scalarMap_baseChange (f : X ⟶ Spec (.of R)) (a : R) :
    (baseChangeFst (S := S) f).appTop
        (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom a) =
      (((Scheme.ΓSpecIso (.of S)).inv ≫
        (baseChangeSnd (S := S) f).appTop).hom (algebraMap R S a)) := by
  have h := congrArg Scheme.Hom.appTop (pullback.condition (f := f) (g := baseChangeMap R S))
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  change f.appTop ≫ (baseChangeFst (S := S) f).appTop =
    (baseChangeMap R S).appTop ≫ (baseChangeSnd (S := S) f).appTop at h
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))
  change CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv =
    (Scheme.ΓSpecIso (.of R)).inv ≫ (baseChangeMap R S).appTop at hn
  have he : (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
        (baseChangeFst (S := S) f).appTop =
      CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
        (baseChangeSnd (S := S) f).appTop := by
    rw [h, ← Category.assoc, ← hn, Category.assoc]
  exact ConcreteCategory.congr_hom he a

instance HOver_moduleBaseChange (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    Module R (HOver (baseChangeSnd (S := S) f)
      (baseChangedModule (S := S) f M) q) :=
  Module.compHom _ (algebraMap R S)

instance HOver_scalarTower (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    IsScalarTower R S (HOver (baseChangeSnd (S := S) f)
      (baseChangedModule (S := S) f M) q) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The adjunction unit into the direct image of the base-changed module.
Source: Stacks Project, Tag 02KH, the canonical comparison.
(blueprint: def-pc-flat-cohomology-comparison) -/
def baseChangeUnit (f : X ⟶ Spec (.of R)) (M : X.Modules) :
    M ⟶ (pushforward (baseChangeFst (S := S) f)).obj
      (baseChangedModule (S := S) f M) :=
  (pullbackPushforwardAdjunction (baseChangeFst (S := S) f)).unit.app M

/-- An exact inverse-image comparison is linear for compatible scalar representations.
Source: Stacks Project, Section 01F7; naturality of the Ext comparison.
(blueprint: def-pc-flat-cohomology-comparison) -/
def cohomologyComparisonLinear
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    (G : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : (constantSheaf K AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ≅
      G.obj ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))))
    {F : Sheaf J AddCommGrpCat.{u}} {F' : Sheaf K AddCommGrpCat.{u}}
    (φ : G.obj F ⟶ F') (ρ : R →+* End F) (τ : R →+* End F')
    (h : ∀ a, G.map ((ρ a)).asHom ≫ φ = φ ≫ (τ a).asHom) (q : ℕ) :
    letI := cohomologyModule F ρ q
    letI := cohomologyModule F' τ q
    F.H q →ₗ[R] F'.H q := by
  letI := cohomologyModule F ρ q
  letI := cohomologyModule F' τ q
  exact
    { toFun := fun x ↦ Sheaf.H.map φ q (Sheaf.H.mapFunctor G e F q x)
      map_add' := fun x y ↦ by
        rw [map_add, map_add]
      map_smul' := fun a x ↦
        sheafComparison_naturality G e φ φ (ρ a).asHom (τ a).asHom (h a) q x }

/-- The pullback on cohomology before extending scalars.
Source: Stacks Project, Tag 02KH, canonical comparison.
(blueprint: def-pc-flat-cohomology-comparison) -/
def H.baseChangeLinear (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    HOver f M q →ₗ[R] HOver (baseChangeSnd (S := S) f)
      (baseChangedModule (S := S) f M) q :=
  cohomologyComparisonLinear (R := R) (invImage (baseChangeFst (S := S) f))
    (constIso (baseChangeFst (S := S) f)).symm
    (coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M))
    ((scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom))
    (((scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)).comp
        (algebraMap R S)) (fun a ↦ by
      change (invImage (baseChangeFst (S := S) f)).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (M.smulHom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom a))) ≫
        coeff _ (baseChangeUnit (S := S) f M) =
          coeff _ (baseChangeUnit (S := S) f M) ≫
            (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).map
              ((baseChangedModule (S := S) f M).smulHom
                ((((Scheme.ΓSpecIso (.of S)).inv ≫
                  (baseChangeSnd (S := S) f).appTop).hom) (algebraMap R S a)))
      rw [← scalarMap_baseChange (S := S) f a]
      apply coeff_naturality
      rw [pushforward_map_smulHom]
      exact smulHom_naturality (baseChangeUnit (S := S) f M) _) q

/-- Extend an R-linear comparison uniquely to its S-linear tensor comparison.
Source: Mathlib `TensorProduct.AlgebraTensorModule.lift`.
(blueprint: def-pc-flat-cohomology-comparison) -/
def extendComparison {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Module S B] [IsScalarTower R S B]
    (l : A →ₗ[R] B) : TensorProduct R S A →ₗ[S] B :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b ↦ b • l
      map_add' := fun _ _ ↦ add_smul _ _ _
      map_smul' := fun _ _ ↦ mul_smul _ _ _ }

/-- The canonical base-change comparison; it is defined without assuming flatness.
Source: Stacks Project, Tag 02KH, canonical comparison.
(blueprint: def-pc-flat-cohomology-comparison) -/
def H.baseChange (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    TensorProduct R S (HOver f M q) →ₗ[S]
      HOver (baseChangeSnd (S := S) f)
        (baseChangedModule (S := S) f M) q :=
  extendComparison (H.baseChangeLinear (S := S) f M q)

attribute [instance] instAddCommGroupH moduleH
end
end AlgebraicGeometry.Scheme.Modules
