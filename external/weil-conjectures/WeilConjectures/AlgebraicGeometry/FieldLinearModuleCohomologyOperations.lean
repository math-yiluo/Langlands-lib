/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.AlgebraicGeometry.ModuleResolutionHomologyExt
import WeilConjectures.AlgebraicGeometry.FieldScalarRestrictionInjectives
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic

/-! # Field-linear cohomology, pullback and cup product of scheme modules

Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED,
the maps preceding equation `equation-kunneth-on-cech`
(blueprint: def-sc-field-linear-module-cohomology-operations).

Cohomology is the recorded right derived functor on O-modules, with scalars restricted
along the structure map. Its canonical comparison with Ext transports exact inverse-image
and tensor operations on sheaves of k-vector spaces back to these cohomology modules.
-/

@[expose] public section

universe u w w' v v' u' t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))
local instance : Abelian (SheafOfModules.{u} X.ringCatSheaf) := inferInstance
local instance : Abelian
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) := inferInstance
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ext_transport_smul
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    {R : Type t} [Ring R] [Linear R D]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {A B : C} {T : D} (η : T ⟶ S.obj A) (τ : A ⟶ A)
    (r : R) (h : η ≫ S.map τ = r • η) (n : ℕ) (a : Abelian.Ext A B n) :
    (Abelian.Ext.mk₀ η).comp
        (((Abelian.Ext.mk₀ τ).comp a (zero_add n)).mapExactFunctor S) (zero_add n) =
      r • (Abelian.Ext.mk₀ η).comp (a.mapExactFunctor S) (zero_add n) := by
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    h, Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp]

-- An ordinary corepresenting bijection extends to Ext by injective dimension shifting.
private theorem extComparison_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ (I : C), Injective I → Injective (R.obj I))
    (A : C) (B : D) (g : B ⟶ R.obj A)
    (h₀ : ∀ F : C, Function.Bijective (fun f : A ⟶ F ↦ g ≫ R.map f))
    (F : C) (n : ℕ) :
    Function.Bijective (((CategoryTheory.Abelian.Ext.mk₀ g).precomp (R.obj F) (zero_add n)).comp
      (R.mapExtAddHom A F n)) := open CategoryTheory.Abelian in by
  let c (F : C) (n : ℕ) :=
    ((Ext.mk₀ g).precomp (R.obj F) (zero_add n)).comp (R.mapExtAddHom A F n)
  change Function.Bijective (c F n)
  induction n generalizing F with
  | zero =>
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
      obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
      change (Ext.mk₀ g).comp ((Ext.mk₀ x).mapExactFunctor R) rfl =
        (Ext.mk₀ g).comp ((Ext.mk₀ y).mapExactFunctor R) rfl at hxy
      rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
        Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀] at hxy
      exact congrArg Ext.mk₀ ((h₀ F).1 ((Ext.mk₀_bijective _ _).1 hxy))
    · obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
      obtain ⟨f, hf⟩ := (h₀ F).2 z
      refine ⟨Ext.mk₀ f, ?_⟩
      change (Ext.mk₀ g).comp ((Ext.mk₀ f).mapExactFunctor R) rfl = _
      rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
      exact congrArg Ext.mk₀ hf
  | succ n hn =>
    let I : InjectivePresentation F := Classical.arbitrary _
    have : Injective I.J := I.injective
    have : Injective (R.obj I.J) := hR I.J I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hSR : (S.map R).ShortExact := hS.map_of_exact R
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ S.g).postcomp A (add_zero n)) (hS.extClass.postcomp A rfl)
      ((Ext.mk₀ (R.map S.g)).postcomp B (add_zero n)) (hSR.extClass.postcomp B rfl)
      (c S.X₂ n) (c S.X₃ n) (c S.X₁ (n + 1)) ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B hSR n (n + 1) rfl))
      (hn _).2 (hn _) ?_ ?_
    · ext x
      change ((Ext.mk₀ g).comp (x.mapExactFunctor R) (zero_add n)).comp
        (Ext.mk₀ (R.map S.g)) (add_zero n) =
        (Ext.mk₀ g).comp ((x.comp (Ext.mk₀ S.g) (add_zero n)).mapExactFunctor R)
          (zero_add n)
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
      exact Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (zero_add n)
    · ext x
      change ((Ext.mk₀ g).comp (x.mapExactFunctor R) (zero_add n)).comp hSR.extClass rfl =
        (Ext.mk₀ g).comp ((x.comp hS.extClass rfl).mapExactFunctor R) (zero_add (n + 1))
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      exact Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))
    · intro x
      exact Ext.covariant_sequence_exact₁ A hS x
        (Ext.eq_zero_of_injective (I := I.J) _) rfl
    · intro x
      exact Ext.covariant_sequence_exact₁ B hSR x
        (Ext.eq_zero_of_injective (I := R.obj I.J) _) rfl


/-- scalar Map.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarMap (U : X.Opens) : k →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
/-- KSheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
abbrev KSheaf (X : Scheme.{u}) (k : Type u) [Field k] :=
  Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)
/-- scalar Obj.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarObj (F : (SheafOfModules.{u} X.ringCatSheaf)) (U : (Opens X)ᵒᵖ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (scalarMap f U.unop)).obj (F.val.obj U)
/-- scalar Restriction linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarRestriction_linear (F : SheafOfModules.{u} X.ringCatSheaf)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ∀ (r : k) (x : scalarObj f F U),
      ((F.val.map i).hom.toAddMonoidHom
        (@SMul.smul k (F.val.obj U)
          (Module.compHom _ (scalarMap f U.unop)).toSMul r x) : scalarObj f F V) =
        @SMul.smul k (F.val.obj V) (Module.compHom _ (scalarMap f V.unop)).toSMul r
        ((F.val.map i).hom.toAddMonoidHom x) := by
  intro r x
  change F.val.map i ((scalarMap f U.unop r) • (show F.val.obj U from x)) =
    (scalarMap f V.unop r) • (show F.val.obj V from F.val.map i x)
  rw [F.val.map_smul]
  congr 1
  change (X.presheaf.map i).hom (scalarMap f U.unop r) = scalarMap f V.unop r
  simp only [scalarMap, RingHom.comp_apply]
  change (X.presheaf.map (homOfLE (le_top (a := U.unop))).op ≫
    X.presheaf.map i) _ = _
  rw [← X.presheaf.map_comp]
  rfl
/-- scalar Restriction.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarRestriction (F : (SheafOfModules.{u} X.ringCatSheaf)) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    scalarObj f F U ⟶ scalarObj f F V :=
  letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k (F.val.obj V) := Module.compHom _ (scalarMap f V.unop)
  ModuleCat.ofHom
    { toFun := fun x : scalarObj f F U ↦ ((F.val.map i).hom.toAddMonoidHom x : scalarObj f F V)
      map_add' := fun a b ↦ (F.val.map i).hom.map_add a b
      map_smul' := scalarRestriction_linear f F i }
/-- scalar Restriction id.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarRestriction_id (F : (SheafOfModules.{u} X.ringCatSheaf)) (U : (Opens X)ᵒᵖ) :
    scalarRestriction f F (𝟙 U) = 𝟙 (scalarObj f F U) := by
  ext x
  change (F.val.map (𝟙 U)).hom x = x
  simp
/-- scalar Restriction comp.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarRestriction_comp (F : (SheafOfModules.{u} X.ringCatSheaf)) {U V W : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    scalarRestriction f F (i ≫ j) = scalarRestriction f F i ≫ scalarRestriction f F j := by
  ext x
  change (F.val.map (i ≫ j)).hom x = (F.val.map j).hom ((F.val.map i).hom x)
  simp
/-- scalar Presheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPresheaf (F : (SheafOfModules.{u} X.ringCatSheaf)) : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj := scalarObj f F
  map := scalarRestriction f F
  map_id := scalarRestriction_id f F
  map_comp := scalarRestriction_comp f F
/-- scalar Presheaf is Sheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Restriction of scalars leaves the underlying sections and restriction maps unchanged.
The gluing and uniqueness axioms for F therefore give the sheaf axiom for this presheaf. -/
theorem scalarPresheaf_isSheaf (F : (SheafOfModules.{u} X.ringCatSheaf)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (scalarPresheaf f F) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})
  exact F.isSheaf
/-- scalar Sheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarSheaf (F : (SheafOfModules.{u} X.ringCatSheaf)) : KSheaf X k :=
  ⟨scalarPresheaf f F, scalarPresheaf_isSheaf f F⟩
/-- scalar Hom linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_linear {F G : SheafOfModules.{u} X.ringCatSheaf}
    (a : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    ∀ (r : k) (x : scalarObj f F U),
      ((a.val.app U).hom.toAddMonoidHom
        (@SMul.smul k (F.val.obj U)
          (Module.compHom _ (scalarMap f U.unop)).toSMul r x) : scalarObj f G U) =
        @SMul.smul k (G.val.obj U) (Module.compHom _ (scalarMap f U.unop)).toSMul r
        ((a.val.app U).hom.toAddMonoidHom x) := by
  intro r x
  exact (a.val.app U).hom.map_smul (scalarMap f U.unop r) x
/-- scalar Hom App.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarHomApp {F G : (SheafOfModules.{u} X.ringCatSheaf)} (a : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    scalarObj f F U ⟶ scalarObj f G U :=
  letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k (G.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  ModuleCat.ofHom
    { toFun := fun x : scalarObj f F U ↦ ((a.val.app U).hom.toAddMonoidHom x : scalarObj f G U)
      map_add' := fun x y ↦ (a.val.app U).hom.map_add x y
      map_smul' := scalarHom_linear f a U }
/-- scalar Hom naturality.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_naturality {F G : (SheafOfModules.{u} X.ringCatSheaf)} (a : F ⟶ G)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    scalarRestriction f F i ≫ scalarHomApp f a V =
      scalarHomApp f a U ≫ scalarRestriction f G i := by
  ext x
  exact PresheafOfModules.naturality_apply a.val i x
/-- scalar Hom.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarHom {F G : SheafOfModules.{u} X.ringCatSheaf} (a : F ⟶ G) :
    scalarSheaf f F ⟶ scalarSheaf f G :=
  ⟨{ app := scalarHomApp f a, naturality := fun _ _ i ↦ scalarHom_naturality f a i }⟩
/-- scalar Hom id.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_id (F : SheafOfModules.{u} X.ringCatSheaf) :
    scalarHom f (𝟙 F) = 𝟙 (scalarSheaf f F) := by
  ext U x
  rfl
/-- scalar Hom comp.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_comp {F G H : (SheafOfModules.{u} X.ringCatSheaf)} (a : F ⟶ G) (b : G ⟶ H) :
    scalarHom f (a ≫ b) = scalarHom f a ≫ scalarHom f b := by
  ext U x
  rfl
/-- scalar Functor.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarFunctor : (SheafOfModules.{u} X.ringCatSheaf) ⥤ KSheaf X k where
  obj := scalarSheaf f
  map := scalarHom f
  map_id := scalarHom_id f
  map_comp := scalarHom_comp f
/-- scalar Functor additive.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
@[instance] theorem scalarFunctor_additive : (scalarFunctor f).Additive := by
  constructor
  intro X Y f g
  ext U x
  rfl
/-- scalar Functor preserves Finite Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Finite limits of module sheaves and of k-vector-space sheaves are computed
sectionwise. Restriction of scalars preserves module limits and retains every underlying
section and restriction map. Hence the canonical comparison with each finite limit is
a sectionwise isomorphism and therefore a sheaf isomorphism. -/
@[instance] theorem scalarFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (scalarFunctor f) := by
  have : PreservesFiniteLimits (scalarFunctor f ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) :=
    preservesFiniteLimits_of_evaluation _ (fun U ↦ by
      change PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf U ⋙
        ModuleCat.restrictScalars (scalarMap f U.unop))
      exact comp_preservesFiniteLimits _ _)
  exact preservesFiniteLimits_of_reflects_of_preserves (scalarFunctor f)
    (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k))
/-- Forgetting scalar sheaves commutes with sheafification and reflects finite colimits.
Source: Stacks Project, Modules on Sites, Tag 03DB. -/
private theorem scalarForget_preservesFiniteColimits :
    PreservesFiniteColimits (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})) := by
  let U := ModuleCat.restrictScalars.{u} (Int.castRingHom k)
  let V := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u} (Int.castRingHom k)).isLeftAdjoint
  have : (U ⋙ V).IsLeftAdjoint := inferInstance
  have : (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).IsLeftAdjoint :=
    inferInstanceAs (U ⋙ V).IsLeftAdjoint
  let J := Opens.grothendieckTopology X
  let G := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u}).symm ≪≫
      Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  infer_instance

/-- scalar Functor preserves Finite Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Forgetting from k-module sheaves to abelian sheaves preserves sheafification:
local injectivity and local surjectivity depend only on the unchanged underlying functions.
Thus this forgetful functor preserves finite colimits, using the sheafification adjunction.
Its composite with scalarFunctor is the underlying-abelian-sheaf functor of O-module
sheaves, which preserves colimits. The forgetful functor reflects isomorphisms and hence
finite colimits. Reflection therefore proves the assertion. -/
@[instance] theorem scalarFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (scalarFunctor f) := by
  let Q := sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})
  have : PreservesFiniteColimits Q := scalarForget_preservesFiniteColimits
  have : PreservesFiniteColimits (scalarFunctor f ⋙ Q) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf X.ringCatSheaf))
  exact preservesFiniteColimits_of_reflects_of_preserves (scalarFunctor f) Q
attribute [local instance] moduleResolution_enoughInjectives
local instance : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{u, u, u + 1} (SheafOfModules.{u} X.ringCatSheaf)
local instance : HasExt.{u + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
local instance : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _

/-- The carrier of the recorded O-module cohomology before restricting scalars.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
abbrev scalarCohomologyCarrier (_f : X ⟶ Spec (CommRingCat.of k))
    (F : (SheafOfModules.{u} X.ringCatSheaf)) (n : ℕ) :=
  (RingedSpace.moduleCohomology X.toRingedSpace n).obj F

/-- Restrict the cohomology module action along the structure map k → Γ(X, O_X).
Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
instance scalarCohomologyModule (f : X ⟶ Spec (CommRingCat.of k))
    (F : (SheafOfModules.{u} X.ringCatSheaf)) (n : ℕ) :
    Module k (scalarCohomologyCarrier f F n) :=
  Module.compHom _ (scalarMap f ⊤)

/-- The recorded O-module cohomology with its restricted k-vector-space structure.
Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomology (F : (SheafOfModules.{u} X.ringCatSheaf)) (n : ℕ) : ModuleCat.{u} k :=
  ModuleCat.of k (scalarCohomologyCarrier f F n)

-- Comparing resolution homology with derived functors requires universe-level conversion.
/-- exists module Ext Equiv.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Evaluate module morphisms from the structure sheaf at 1. This identifies the Hom complex
with the global-sections complex. Compare degree-n homology via the injective-resolution
comparison isomorphism, giving precisely the displayed cocycle formula. -/
theorem exists_moduleExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    ∃ e : ((RingedSpace.moduleCohomology X.toRingedSpace n).obj F) ≃+
        Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n,
      ∀ (I : InjectiveResolution F)
        (a : (RingedSpace.globalSectionsComplex I).cycles n)
        (φ : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
        (hφ : φ ≫ I.cocomplex.d n (n+1) = 0),
        φ.val.app (op ⊤) (1 : Γ(X, ⊤)) =
          (RingedSpace.globalSectionsComplex I).iCycles n a →
        e ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
          ((RingedSpace.globalSectionsComplex I).homologyπ n a)) =
            InjectiveResolution.extMk.{u, u, u + 1} I φ (n+1) rfl hφ := by
  let J := injectiveResolution F
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  obtain ⟨eJ, heJ⟩ := moduleResolutionHomologyExtEquiv F J n
  let e := (J.isoRightDerivedObj Γ n).toLinearEquiv.toAddEquiv.trans eJ
  refine ⟨e, ?_⟩
  intro I c φ hφ hc
  let ψ : I.Hom J (𝟙 F) := ⟨InjectiveResolution.desc (𝟙 F) J I, by simp⟩
  let K := RingedSpace.globalSectionsComplex I
  let L := RingedSpace.globalSectionsComplex J
  let χ : K ⟶ L := (Γ.mapHomologicalComplex (.up ℕ)).map ψ.hom
  let c' := HomologicalComplex.cyclesMap χ n c
  change φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = K.iCycles n c at hc
  have hc' : (φ ≫ ψ.hom.f n).val.app (op ⊤) (1 : Γ(X, ⊤)) = L.iCycles n c' := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i χ n) c
    simp only [ConcreteCategory.comp_apply] at h
    rw [← hc] at h
    exact h.symm
  have hn := ConcreteCategory.congr_hom
    (InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 F) I J ψ.hom
      (by simp [ψ]) Γ n) (K.homologyπ n c)
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality χ n) c
  simp only [ConcreteCategory.comp_apply] at hn hp
  change (Γ.rightDerived n).map (𝟙 F)
      ((I.isoRightDerivedObj Γ n).inv (K.homologyπ n c)) =
    (J.isoRightDerivedObj Γ n).inv
      (HomologicalComplex.homologyMap χ n (K.homologyπ n c)) at hn
  rw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hn
  rw [hp] at hn
  rw [hn]
  change eJ ((J.isoRightDerivedObj Γ n).hom
    ((J.isoRightDerivedObj Γ n).inv (L.homologyπ n c'))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  rw [heJ c' (φ ≫ ψ.hom.f n) (by simp [reassoc_of% hφ]) hc']
  exact (InjectiveResolution.extMk_comp_mk₀ φ (n + 1) rfl hφ ψ).symm.trans
    (Abelian.Ext.comp_mk₀_id _)

/-- module Ext Equiv.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def moduleExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace n).obj F) ≃+
      Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n :=
  Classical.choose (exists_moduleExtEquiv F n)

section

attribute [local irreducible] moduleExtEquiv

/-- constant Scalar Unit.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def constantScalarUnit : KSheaf X k :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).obj (ModuleCat.of k k)

/-- constant Scalar Unit Iso.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def constantScalarUnitIso : constantScalarUnit (X := X) (k := k) ≅ 𝟙_ (KSheaf X k) :=
  (Functor.Monoidal.εIso
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k))).symm

attribute [local irreducible] constantScalarUnitIso

/-- scalar Unit Linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarUnitLinear : ModuleCat.of k k ⟶
    (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op ⊤) :=
  letI : Module k ((SheafOfModules.unit X.ringCatSheaf).val.obj (op ⊤)) :=
    Module.compHom _ (scalarMap f ⊤)
  ModuleCat.ofHom
    { toFun := fun r : k ↦ scalarMap f ⊤ r
      map_add' := fun r s ↦ (scalarMap f ⊤).map_add r s
      map_smul' := by
        intro r s
        change scalarMap f ⊤ (r * s) = scalarMap f ⊤ r * scalarMap f ⊤ s
        exact (scalarMap f ⊤).map_mul r s }

/-- The scalar-unit map sends r to its scalar section.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: This is the defining formula of the explicit linear map. -/
theorem exists_scalarUnitLinear (r : k) : scalarUnitLinear f r = scalarMap f ⊤ r := by
  rfl

/-- scalar Unit Morphism.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarUnitMorphism : 𝟙_ (KSheaf X k) ⟶
    scalarSheaf f (SheafOfModules.unit X.ringCatSheaf) :=
  constantScalarUnitIso.inv ≫
    ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
      isTerminalTop).homEquiv _ _).symm (scalarUnitLinear f)

attribute [local irreducible] scalarUnitMorphism

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- scalar Ext Map.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarExtMap (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (a : Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n) :
    Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    (a.mapExactFunctor (scalarFunctor f)) (zero_add n)

attribute [local irreducible] scalarExtMap

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- scalar Cohomology Ext Map.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyExtMap (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (a : scalarCohomology f F n) :
    Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  scalarExtMap f F n (moduleExtEquiv F n a)

attribute [local irreducible] scalarCohomologyExtMap

/-- scalar Cohomology Ext Map add.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: The chosen moduleExtEquiv is an additive equivalence, so it sends a sum to the
sum of its images. Exact-functor transport on Ext preserves addition by
Ext.mapExactFunctor_add. Precomposition by the degree-zero scalar-unit Ext class preserves
addition by Ext.comp_add. Compose these three equalities. -/
theorem scalarCohomologyExtMap_add (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (a b : scalarCohomology f F n) :
    scalarCohomologyExtMap f F n (a+b) =
      scalarCohomologyExtMap f F n a + scalarCohomologyExtMap f F n b := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      unfold scalarCohomologyExtMap scalarExtMap
      exact (((Abelian.Ext.precomp (Abelian.Ext.mk₀ (scalarUnitMorphism f))
        (scalarSheaf f F) (zero_add n)).comp
        ((scalarFunctor f).mapExtAddHom (SheafOfModules.unit X.ringCatSheaf) F n)).comp
          (moduleExtEquiv F n).toAddMonoidHom).map_add a b

attribute [local irreducible] scalarMap scalarUnitLinear

-- Multiplication on the structure sheaf by a scalar global section.
private def scalarUnitEndomorphism (r : k) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
    ((SheafOfModules.unit X.ringCatSheaf).val.sectionsMk
      (fun U ↦ scalarMap f U.unop r) (by
        intro U V i
        change (X.presheaf.map i).hom (scalarMap f U.unop r) = scalarMap f V.unop r
        simp only [scalarMap, RingHom.comp_apply]
        change (X.presheaf.map (homOfLE (le_top (a := U.unop))).op ≫
          X.presheaf.map i) _ = _
        rw [← X.presheaf.map_comp]
        rfl))

private theorem scalarUnitEndomorphism_apply (r : k) (U : (Opens X)ᵒᵖ)
    (s : Γ(X, U.unop)) :
    (scalarUnitEndomorphism f r).val.app U s = s * scalarMap f U.unop r := by
  rfl

attribute [local irreducible] scalarUnitEndomorphism

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarUnitEndomorphism_comp (r : k) :
    scalarUnitMorphism f ≫ (scalarFunctor f).map (scalarUnitEndomorphism f r) =
      r • scalarUnitMorphism f := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
    isTerminalTop
  let v := (adj.homEquiv (ModuleCat.of k k)
    (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).symm (scalarUnitLinear f)
  have he : adj.homEquiv _ _ v = scalarUnitLinear f :=
    (adj.homEquiv _ _).apply_symm_apply _
  have hv : v ≫ scalarHom f (scalarUnitEndomorphism f r) = r • v := by
    apply (adj.homEquiv _ _).injective
    erw [adj.homEquiv_naturality_right, he]
    have hmap : adj.homEquiv _ _ (r • v) = r • adj.homEquiv _ _ v := by
      rw [adj.homEquiv_unit, adj.homEquiv_unit]
      change adj.unit.app (ModuleCat.of k k) ≫ (r • v.hom.app (op ⊤)) =
        r • (adj.unit.app (ModuleCat.of k k) ≫ v.hom.app (op ⊤))
      exact Linear.comp_smul _ _ _ _ r _
    rw [hmap, he]
    change scalarUnitLinear f ≫ (scalarHom f (scalarUnitEndomorphism f r)).hom.app
      (op ⊤) = r • scalarUnitLinear f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    unfold scalarUnitLinear
    change (scalarUnitEndomorphism f r).val.app (op ⊤) (scalarMap f ⊤ s) =
      scalarMap f ⊤ r * scalarMap f ⊤ s
    rw [scalarUnitEndomorphism_apply, mul_comm]
  unfold scalarUnitMorphism scalarFunctor
  change (constantScalarUnitIso.inv ≫ v) ≫ scalarHom f (scalarUnitEndomorphism f r) =
    r • (constantScalarUnitIso.inv ≫ v)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun w ↦ constantScalarUnitIso.inv ≫ w) hv).trans
      (Linear.comp_smul _ _ _ _ r _))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleExtEquiv_scalar (F : SheafOfModules.{u} X.ringCatSheaf)
    (n : ℕ) (r : k) (a : scalarCohomology f F n) :
    moduleExtEquiv F n (r • a) =
      (Abelian.Ext.mk₀ (scalarUnitEndomorphism f r)).comp (moduleExtEquiv F n a)
        (zero_add n) := by
  let I := injectiveResolution F
  let K := RingedSpace.globalSectionsComplex I
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  obtain ⟨φ, hφ, heφ⟩ := I.extMk_surjective (moduleExtEquiv F n a) (n + 1) rfl
  let x := φ.val.app (op ⊤) (1 : Γ(X, ⊤))
  have hx : K.d n (n + 1) x = 0 := by
    exact congrArg (fun t ↦ t.val.app (op ⊤) (1 : Γ(X, ⊤))) hφ
  let c : K.cycles n := K.cyclesMk x (n + 1) (by simp) hx
  have hc : φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = K.iCycles n c :=
    (K.i_cyclesMk x (n + 1) (by simp) hx).symm
  have he (c : K.cycles n) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
      (hφ : φ ≫ I.cocomplex.d n (n + 1) = 0)
      (hc : φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = K.iCycles n c) :
      moduleExtEquiv F n ((I.isoRightDerivedObj Γ n).inv (K.homologyπ n c)) =
        I.extMk φ (n + 1) rfl hφ := by
    with_unfolding_all exact Classical.choose_spec (exists_moduleExtEquiv F n) I c φ hφ hc
  have ha : (I.isoRightDerivedObj Γ n).inv (K.homologyπ n c) = a :=
    (moduleExtEquiv F n).injective ((he c φ hφ hc).trans heφ)
  let t : ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) := scalarMap f ⊤ r
  have har : (I.isoRightDerivedObj Γ n).inv (K.homologyπ n (t • c)) = r • a := by
    erw [(K.homologyπ n).hom.map_smul, (I.isoRightDerivedObj Γ n).inv.hom.map_smul, ha]
    rfl
  have hrc : (scalarUnitEndomorphism f r ≫ φ).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      K.iCycles n (t • c) := by
    erw [(K.iCycles n).hom.map_smul, ← hc]
    change (φ.val.app (op ⊤))
      ((scalarUnitEndomorphism f r).val.app (op ⊤) (1 : Γ(X, ⊤))) = _
    erw [scalarUnitEndomorphism_apply, one_mul]
    set_option backward.isDefEq.respectTransparency false in
      simpa only [smul_eq_mul, mul_one] using
        (φ.val.app (op ⊤)).hom.map_smul t (1 : Γ(X, ⊤))
  rw [← har, he (t • c) (scalarUnitEndomorphism f r ≫ φ)
    (by rw [Category.assoc, hφ, comp_zero]) hrc]
  exact (I.mk₀_comp_extMk φ (n + 1) rfl hφ (scalarUnitEndomorphism f r)).symm.trans
    (congrArg (fun x ↦ (Abelian.Ext.mk₀ (scalarUnitEndomorphism f r)).comp x
      (zero_add n)) heφ)

attribute [local irreducible] scalarSheaf

/-- scalar Cohomology Ext Map smul.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: The injective-resolution comparison is additive and k-linear, as are exact-functor
transport on Ext and precomposition by the scalar-unit morphism. Compose these maps. -/
theorem scalarCohomologyExtMap_smul (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (r : k) (a : scalarCohomology f F n) :
    scalarCohomologyExtMap f F n (r • a) = r • scalarCohomologyExtMap f F n a := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types false in
      unfold scalarCohomologyExtMap scalarExtMap
      rw [moduleExtEquiv_scalar f F n r a]
      exact ext_transport_smul.{u + 1, u, u + 1, u, u, u + 1, u}
        (C := SheafOfModules.{u} X.ringCatSheaf) (D := KSheaf X k)
        (R := k) (A := SheafOfModules.unit X.ringCatSheaf) (B := F)
        (T := 𝟙_ (KSheaf X k)) (scalarFunctor f) (scalarUnitMorphism f)
        (scalarUnitEndomorphism f r) r (scalarUnitEndomorphism_comp f r) n
        (moduleExtEquiv F n a)

section

attribute [local semireducible] scalarSheaf

private noncomputable def fieldUnitSectionsEquiv (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    (SheafOfModules.unit (moduleRings Y.toRingedSpace) ⟶ M) ≃+
      (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M where
  toFun f := (M.unitHomEquiv f).val (Opposite.op ⊤)
  invFun a := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      rfl))
  left_inv f := by
    apply M.unitHomEquiv.injective
    apply Subtype.ext
    funext U
    simp only [Equiv.apply_symm_apply]
    exact (M.unitHomEquiv f).property _
  right_inv a := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val (Opposite.op ⊤) = a
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 _) a = a
    simp
  map_add' f g := by
    change (f.val.app (Opposite.op ⊤) + g.val.app (Opposite.op ⊤))
      (1 : (moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤)) = _
    rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnitHom_bijective (G : SheafOfModules.{u} X.ringCatSheaf) :
    Function.Bijective (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ G ↦
      scalarUnitMorphism f ≫ (scalarFunctor f).map φ) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
    isTerminalTop
  let e := (adj.homEquiv (ModuleCat.of k k) (scalarSheaf f G)).symm.trans
    (constantScalarUnitIso (X := X) (k := k)).homFromEquiv
  have hev : Function.Bijective
      (fun q : ModuleCat.of k k ⟶ (scalarSheaf f G).obj.obj (op ⊤) ↦ q 1) := by
    constructor
    · intro q q' h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      have hq := q.hom.map_smul r (1 : k)
      have hq' := q'.hom.map_smul r (1 : k)
      change q.hom 1 = q'.hom 1 at h
      rw [h] at hq
      simpa only [smul_eq_mul, mul_one] using hq.trans hq'.symm
    · intro x
      exact ⟨ModuleCat.ofHom (Y := (scalarSheaf f G).obj.obj (op ⊤))
        (LinearMap.toSpanSingleton k
        ((scalarSheaf f G).obj.obj (op ⊤)) x), one_smul k x⟩
  let t (φ : SheafOfModules.unit X.ringCatSheaf ⟶ G) :=
    scalarUnitLinear f ≫ (scalarHom f φ).hom.app (op ⊤)
  have ht : Function.Bijective t := by
    apply (hev.of_comp_iff' t).mp
    have heval : (fun q : ModuleCat.of k k ⟶
        (scalarSheaf f G).obj.obj (op ⊤) ↦ q 1) ∘ t =
        (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ G ↦
          (φ.val.app (op ⊤) (1 : Γ(X, ⊤)) : (scalarSheaf f G).obj.obj (op ⊤))) := by
      funext φ
      unfold t scalarUnitLinear
      change (φ.val.app (op ⊤)).hom (scalarMap f ⊤ 1) =
        (φ.val.app (op ⊤)).hom (1 : Γ(X, ⊤))
      rw [map_one]
    rw [heval]
    with_unfolding_all exact (fieldUnitSectionsEquiv X G).bijective
  have he : (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ G ↦
      scalarUnitMorphism f ≫ (scalarFunctor f).map φ) = e ∘ t := by
    funext φ
    change scalarUnitMorphism f ≫ scalarHom f φ =
      constantScalarUnitIso.inv ≫
        (adj.homEquiv (ModuleCat.of k k) (scalarSheaf f G)).symm (t φ)
    unfold scalarUnitMorphism
    change (constantScalarUnitIso.inv ≫
      (adj.homEquiv (ModuleCat.of k k)
        (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).symm
          (scalarUnitLinear f)) ≫ scalarHom f φ = _
    erw [Category.assoc, ← adj.homEquiv_naturality_right_symm]
    rfl
  rw [he]
  exact e.bijective.comp ht

/-- scalar Cohomology Ext Map bijective.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Restriction of scalars preserves injective acyclicity for global sections: its left
adjoint tensors with the structure sheaf, which is exact over the field k. Compare the
two derived global-sections functors using evaluation at 1 and the constant-sheaf adjunction. -/
theorem scalarCohomologyExtMap_bijective (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    Function.Bijective (scalarCohomologyExtMap f F n) := by
  have hI : (scalarFunctor f).PreservesInjectiveObjects := by
    have hi := SheafOfModules.fieldScalarRestriction_preservesInjectives
      X.toTopCat X.ringCatSheaf
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
    refine ⟨fun {I} hI ↦ ?_⟩
    let q := (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
    let S := SheafOfModules.forgetToSheafModuleCat.{u} X.ringCatSheaf (op ⊤)
      isTerminalTop.op ⋙ sheafCompose (Opens.grothendieckTopology X)
        (ModuleCat.restrictScalars q)
    have e : scalarSheaf f I ≅ S.obj I :=
      ObjectProperty.isoMk _ (NatIso.ofComponents
        (fun U ↦ ModuleCat.restrictScalarsComp'App q
          (X.ringCatSheaf.obj.map (isTerminalTop.op.to U)).hom (scalarMap f U.unop)
          (by unfold scalarMap; rfl) (I.val.obj U)) (by
            intro U V i
            ext x
            rfl))
    exact Injective.of_iso e.symm (hi.injective_obj hI)
  have h₀ : ∀ G : SheafOfModules.{u} X.ringCatSheaf,
      Function.Bijective (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ G ↦
        scalarUnitMorphism f ≫ (scalarFunctor f).map φ) := by
    exact scalarUnitHom_bijective f
  have hExt := extComparison_bijective (scalarFunctor f)
    (fun I h ↦ hI.injective_obj h) _ _ (scalarUnitMorphism f) h₀ F n
  unfold scalarCohomologyExtMap scalarExtMap
  change Function.Bijective
    ((((Abelian.Ext.mk₀ (scalarUnitMorphism f)).precomp _ (zero_add n)).comp
      ((scalarFunctor f).mapExtAddHom _ F n)).comp (moduleExtEquiv F n).toAddMonoidHom)
  exact hExt.comp (moduleExtEquiv F n).bijective

/-- Injectivity follows by taking the first component of scalarCohomologyExtMap_bijective.
Source: Stacks Project, Cohomology, Tag 01F7.
(blueprint: lem-sc-field-linear-ext-map-injective) -/
theorem scalarCohomologyExtMap_injective (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    Function.Injective (scalarCohomologyExtMap f F n) :=
  (scalarCohomologyExtMap_bijective f F n).1

/-- Surjectivity follows by taking the second component of scalarCohomologyExtMap_bijective.
Source: Stacks Project, Cohomology, Tag 01F7.
(blueprint: lem-sc-field-linear-ext-map-surjective) -/
theorem scalarCohomologyExtMap_surjective (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    Function.Surjective (scalarCohomologyExtMap f F n) :=
  (scalarCohomologyExtMap_bijective f F n).2

end

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- scalar Cohomology Ext Equiv: the comparison `scalarCohomologyExtMap` as an additive
equivalence; it is k-linear by `scalarCohomologyExtMap_smul`.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    scalarCohomology f F n ≃+
      Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  { Equiv.ofBijective (scalarCohomologyExtMap f F n)
      (scalarCohomologyExtMap_bijective f F n) with
    map_add' := scalarCohomologyExtMap_add f F n }

end

attribute [irreducible] scalarCohomologyExtEquiv
  scalarCohomologyExtMap scalarExtMap moduleExtEquiv

variable {Y : Scheme.{u}}

/-- scalar Inverse Image.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarInverseImage (a : Y ⟶ X) : KSheaf X k ⥤ KSheaf Y k :=
  (Opens.map a.base).sheafPullback (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

/-- scalar Inverse Image additive.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Inverse image on sheaves is exact and additive. This follows from the stalk
formula and filtered-colimit exactness for vector spaces, and from its left adjunction. -/
@[instance] theorem scalarInverseImage_additive (a : Y ⟶ X) :
    (scalarInverseImage (k := k) a).Additive := by
  have hp : ((Opens.map a.base).sheafPushforwardContinuous
      (ModuleCat.{u} k) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)).Additive := by
    constructor
    intro M N g h
    ext U x
    rfl
  exact ((Opens.map a.base).sheafAdjunctionContinuous
    (ModuleCat.{u} k) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)).left_adjoint_additive
/-- scalar Inverse Image preserves Finite Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Inverse image on sheaves is exact and additive. This follows from the stalk
formula and filtered-colimit exactness for vector spaces, and from its left adjunction. -/
@[instance] theorem scalarInverseImage_preservesFiniteLimits (a : Y ⟶ X) :
    PreservesFiniteLimits (scalarInverseImage (k := k) a) := by
  have := lan_preservesFiniteLimits_of_flat (E := ModuleCat.{u} k) (Opens.map a.base)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map a.base) (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
/-- scalar Inverse Image preserves Finite Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Inverse image on sheaves is exact and additive. This follows from the stalk
formula and filtered-colimit exactness for vector spaces, and from its left adjunction. -/
@[instance] theorem scalarInverseImage_preservesFiniteColimits (a : Y ⟶ X) :
    PreservesFiniteColimits (scalarInverseImage (k := k) a) := by
  dsimp [scalarInverseImage, Functor.sheafPullback]
  infer_instance

local instance : MonoidalCategory (KSheaf Y k) := Sheaf.monoidalCategory _ _

/-- scalar Inverse Unit Iso.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarInverseUnitIso (a : Y ⟶ X) :
    (scalarInverseImage (k := k) a).obj (𝟙_ (KSheaf X k)) ≅ 𝟙_ (KSheaf Y k) :=
  (scalarInverseImage a).mapIso constantScalarUnitIso.symm ≪≫
    ((Opens.map a.base).constantSheafsheafPullbackIso (ModuleCat.{u} k) _ _
      isTerminalTop isTerminalTop).app (ModuleCat.of k k) ≪≫ constantScalarUnitIso

/-- Naturality of the restricted field action along a morphism over Spec k.
Source: Stacks Project, Modules, Tag 0096. -/
private theorem scalarMap_pullback (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (U : X.Opens) (r : k) :
    (a.app U).hom (scalarMap f U r) = scalarMap g (a ⁻¹ᵁ U) r := by
  have hn := a.naturality (homOfLE (le_top (a := U))).op
  have ht := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ht
  simp only [scalarMap, RingHom.comp_apply]
  change (X.presheaf.map (homOfLE (le_top (a := U))).op ≫ a.app U)
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) r) = _
  rw [hn]
  change (a.appTop ≫ Y.presheaf.map (homOfLE (le_top (a := a ⁻¹ᵁ U))).op)
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) r) = _
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ a.appTop ≫
    Y.presheaf.map (homOfLE (le_top (a := a ⁻¹ᵁ U))).op) r = _
  rw [← Category.assoc f.appTop, ht]
  rfl

/-- exists scalar Pullback Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the inverse-image/direct-image adjunction on sheaves of k-vector spaces.
The canonical unit of tensor pullback is k-linear because a is over Spec k. Its adjoint
is the coefficient map, and the adjunction formula is exactly the displayed equality. -/
theorem exists_scalarPullbackCoefficient (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{u} X.ringCatSheaf) :
    ∃ j : (scalarInverseImage a).obj (scalarSheaf f F) ⟶
        scalarSheaf g ((tensorPullback a).obj F),
      ∀ (U : X.Opens) (s : F.val.obj (op U)),
        ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).homEquiv
          _ _) j).hom.app (op U) s =
            ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).val.app
              (op U) s := by
  let η : F ⟶ (pushforward a).obj ((tensorPullback a).obj F) :=
    (Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F
  let H := (tensorPullback a).obj F
  let βApp (U : (Opens X)ᵒᵖ) :
      scalarObj f F U ⟶ scalarObj g H ((Opens.map a.base).op.obj U) :=
    letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
    letI : Module k (H.val.obj ((Opens.map a.base).op.obj U)) :=
      Module.compHom _ (scalarMap g (a ⁻¹ᵁ U.unop))
    ModuleCat.ofHom
      { toFun := fun s : scalarObj f F U ↦
          (η.val.app U s : scalarObj g H ((Opens.map a.base).op.obj U))
        map_add' := fun s t ↦ (η.val.app U).hom.map_add s t
        map_smul' := by
          intro r s
          change η.val.app U ((scalarMap f U.unop r) • (show F.val.obj U from s)) =
            (scalarMap g (a ⁻¹ᵁ U.unop) r) •
              (show H.val.obj ((Opens.map a.base).op.obj U) from η.val.app U s)
          rw [(η.val.app U).hom.map_smul]
          change ((a.app U.unop).hom (scalarMap f U.unop r)) •
            (show H.val.obj ((Opens.map a.base).op.obj U) from η.val.app U s) = _
          rw [scalarMap_pullback f g a h] }
  let β : scalarSheaf f F ⟶
      ((Opens.map a.base).sheafPushforwardContinuous (ModuleCat.{u} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj
          (scalarSheaf g H) :=
    ⟨{ app := βApp, naturality := by
        intro U V i
        ext s
        exact PresheafOfModules.naturality_apply η.val i s }⟩
  let adj := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  refine ⟨(adj.homEquiv _ _).symm β, ?_⟩
  intro U s
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun t ↦ t.hom)
      ((adj.homEquiv _ _).apply_symm_apply β)) (op U)) s

/-- scalar Pullback Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackCoefficient (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{u} X.ringCatSheaf) :
    (scalarInverseImage a).obj (scalarSheaf f F) ⟶
      scalarSheaf g ((tensorPullback a).obj F) :=
  Classical.choose (exists_scalarPullbackCoefficient f g a h F)

/-- scalar Cohomology Pullback.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyPullback (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{u} X.ringCatSheaf)
    (n : ℕ) (x : scalarCohomology f F n) :
    scalarCohomology g ((tensorPullback a).obj F) n :=
  (scalarCohomologyExtEquiv g _ n).symm
    (((Abelian.Ext.mk₀ (scalarInverseUnitIso a).inv).comp
      ((scalarCohomologyExtEquiv f F n x).mapExactFunctor (scalarInverseImage a))
      (zero_add n)).comp (Abelian.Ext.mk₀ (scalarPullbackCoefficient f g a h F)) (add_zero n))

attribute [irreducible] scalarCohomologyPullback scalarPullbackCoefficient
  scalarInverseUnitIso scalarUnitMorphism

local instance : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf
local instance : SymmetricCategory (KSheaf X k) := Sheaf.symmetricCategory _ _
local instance : MonoidalPreadditive (KSheaf X k) := Sheaf.monoidalPreadditive

/-- scalar Tensor Left Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorLeftLimits (M : KSheaf X k) :
    PreservesFiniteLimits (tensorLeft M) := by
  have : PreservesFiniteLimits (tensorLeft M.obj) :=
    preservesFiniteLimits_of_evaluation _ (fun U ↦ by
      have : PreservesFiniteLimits (tensorLeft (M.obj.obj U)) := inferInstance
      change PreservesFiniteLimits
        ((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj U ⋙ tensorLeft (M.obj.obj U))
      exact comp_preservesFiniteLimits _ _)
  have : PreservesFiniteLimits (tensorLeft M.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{u} k) ⋙ tensorLeft M.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (Sheaf.tensorLeftIso M).symm
/-- scalar Tensor Left Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorLeftColimits (M : KSheaf X k) :
    PreservesFiniteColimits (tensorLeft M) := by
  let : SymmetricCategory (KSheaf X k) := Sheaf.symmetricCategory _ _
  let : MonoidalClosed ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} k) :=
    MonoidalClosed.FunctorCategory.monoidalClosed
  let : MonoidalClosed (KSheaf X k) :=
    Monoidal.Reflective.monoidalClosed
      (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u} k))
  infer_instance
/-- scalar Tensor Right Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorRightLimits (M : KSheaf X k) :
    PreservesFiniteLimits (tensorRight M) := by
  exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
/-- scalar Tensor Right Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorRightColimits (M : KSheaf X k) :
    PreservesFiniteColimits (tensorRight M) := by
  exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

/-- scalar Ext Cup.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarExtCup {A B : KSheaf X k} {p q : ℕ}
    (a : Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) A p)
    (b : Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) B q) :
    Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (A ⊗ B) (p+q) :=
  ((Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv).comp
    (a.mapExactFunctor (tensorRight (𝟙_ (KSheaf X k)))) (zero_add p)).comp
      (b.mapExactFunctor (tensorLeft A)) rfl

/-- The sectionwise k-linear tensor coefficient, sending pure tensors to tensor sections.
Source: Stacks Project, Cohomology, Tag 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarTensorCoefficientApp (F G : SheafOfModules.{u} X.ringCatSheaf)
    (U : (Opens X)ᵒᵖ) :
    scalarObj f F U ⊗ scalarObj f G U ⟶ scalarObj f (F ⊗ G) U :=
  letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k (G.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k ((F ⊗ G).val.obj U) := Module.compHom _ (scalarMap f U.unop)
  ModuleCat.MonoidalCategory.tensorLift (fun s t ↦ tmulSection s t)
    (fun s s' t ↦ add_tmulSection s s' t)
    (fun r s t ↦ smul_tmulSection (scalarMap f U.unop r) s t)
    (fun s t t' ↦ tmulSection_add s t t')
    (fun r s t ↦ tmulSection_smul (scalarMap f U.unop r) s t)

/-- The tensor-section maps commute with restriction.
Source: Stacks Project, Cohomology, Tag 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Both composites send a pure tensor to the tensor of the restricted sections,
by the restriction formula for tensor sections. Pure tensors generate the tensor product. -/
theorem scalarTensorCoefficientApp_naturality (F G : SheafOfModules.{u} X.ringCatSheaf)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (scalarPresheaf f F ⊗ scalarPresheaf f G).map i ≫
        scalarTensorCoefficientApp f F G V =
      scalarTensorCoefficientApp f F G U ≫ (scalarPresheaf f (F ⊗ G)).map i := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change tmulSection ((F.val.map i).hom s) ((G.val.map i).hom t) =
    ((F ⊗ G).val.map i).hom (tmulSection s t)
  exact (tmulSection_map (leOfHom i.unop) s t).symm

/-- The sectionwise coefficient as a morphism of presheaves of k-vector spaces.
Source: Stacks Project, Cohomology, Tag 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarTensorPresheafCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    scalarPresheaf f F ⊗ scalarPresheaf f G ⟶ scalarPresheaf f (F ⊗ G) where
  app := scalarTensorCoefficientApp f F G
  naturality := fun _ _ i ↦ scalarTensorCoefficientApp_naturality f F G i

/-- scalar Tensor Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    scalarSheaf f F ⊗ scalarSheaf f G ⟶ scalarSheaf f (F ⊗ G) :=
  (Sheaf.tensorLeftIso (scalarSheaf f F)).hom.app (scalarSheaf f G) ≫
    ((CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology X) (ModuleCat.{u} k)).homEquiv _ _).symm
        (scalarTensorPresheafCoefficient f F G)

attribute [local irreducible] scalarTensorCoefficient

private theorem scalarTensorInclusionComparison (M N : KSheaf X k) :
    Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{u} k)) M N ≫
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).map
        ((Sheaf.tensorLeftIso M).hom.app N) =
      (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
        (ModuleCat.{u} k)).unit.app (M.obj ⊗ N.obj) := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit,
    Category.assoc, ← Functor.map_comp]
  have hc : Functor.OplaxMonoidal.δ
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) M.obj N.obj ≫
      ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
        (ModuleCat.{u} k)).counit.app M ⊗ₘ
      (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
        (ModuleCat.{u} k)).counit.app N) ≫
      (Sheaf.tensorLeftIso M).hom.app N = 𝟙 _ := by
    simp [Sheaf.tensorLeftIso, Sheaf.presheafToSheafCompTensorLeftIso,
      tensorHom_def, ← whisker_exchange_assoc, ← comp_whiskerRight_assoc]
  simp only [Category.assoc] at *
  erw [hc]
  simp

/-- The sheafified tensor coefficient sends pure tensors to tensor sections.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: The sheafification adjunction extends the sectionwise map. Its defining
adjunction identity, composed with the monoidal sheafification comparison, says that
its composite with the tensorator of the inclusion is the sectionwise tensor map.
Evaluating on a pure tensor gives tmulSection s t. -/
theorem exists_scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    ∀ (U : X.Opens) (s : scalarObj f F (op U)) (t : scalarObj f G (op U)),
      (scalarTensorCoefficient f F G).hom.app (op U)
        (((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
          (ModuleCat.{u} k)) (scalarSheaf f F) (scalarSheaf f G)).app (op U))
            (s ⊗ₜ[k] t)) = tmulSection s t := by
  have hc : Functor.LaxMonoidal.μ
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k))
      (scalarSheaf f F) (scalarSheaf f G) ≫
      (scalarTensorCoefficient f F G).hom = scalarTensorPresheafCoefficient f F G := by
    unfold scalarTensorCoefficient
    change _ ≫ (sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{u} k)).map (_ ≫ _) = _
    rw [Functor.map_comp, ← Category.assoc, scalarTensorInclusionComparison]
    exact ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
      (ModuleCat.{u} k)).homEquiv _ _).apply_symm_apply _
  intro U s t
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hc (op U)) (s ⊗ₜ[k] t)

/-- scalar Cohomology Cup.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyCup (F G : SheafOfModules.{u} X.ringCatSheaf) (p q : ℕ)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomology f (F ⊗ G) (p+q) :=
  (scalarCohomologyExtEquiv f _ (p+q)).symm
    ((scalarExtCup (scalarCohomologyExtEquiv f F p a)
      (scalarCohomologyExtEquiv f G q b)).comp
        (Abelian.Ext.mk₀ (scalarTensorCoefficient f F G)) (add_zero _))

/-- The normalized tensor-pullback adjunction, with its sectionwise unit.
Source: Stacks Project, Tag 0096
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackAdjunction {A B : Scheme.{u}} (a : A ⟶ B) :
    tensorPullback a ⊣ pushforward a :=
  Classical.choose (exists_tensorPullbackAdjunction a)

attribute [irreducible] scalarPullbackAdjunction scalarCohomologyCup

/-- The canonical composition comparison for tensor pullback, using its normalized adjunction.
Source: Stacks Project, Tag 0097; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackCompIso {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    tensorPullback (a ≫ b) ≅ tensorPullback b ⋙ tensorPullback a :=
  (scalarPullbackAdjunction (a ≫ b)).leftAdjointUniq
    (((scalarPullbackAdjunction b).comp
      (scalarPullbackAdjunction a)).ofNatIsoRight
        (pushforwardComp a b))

attribute [irreducible] scalarPullbackCompIso

/-- The canonical comparison associated to a commutative square of scheme morphisms.
Source: Stacks Project, Tag 0097; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackSquareIso {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules) :
    (tensorPullback a).obj ((tensorPullback b).obj M) ≅
      (tensorPullback c).obj ((tensorPullback d).obj M) :=
  ((scalarPullbackCompIso a b).app M).symm ≪≫
    eqToIso (congrArg (fun t ↦ (tensorPullback t).obj M) h) ≪≫
      (scalarPullbackCompIso c d).app M

/-- Coefficient functoriality on the recorded derived-functor cohomology.
Source: Stacks Project, Tag 01DZ
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyMap {M N : SheafOfModules.{u} X.ringCatSheaf}
    (a : M ⟶ N) (n : ℕ) (x : scalarCohomology f M n) : scalarCohomology f N n :=
  ((ModuleCat.restrictScalars (scalarMap f ⊤)).map
    ((RingedSpace.moduleCohomology X.toRingedSpace n).map a)).hom x

/-- Coefficients of the external cup product on a fibre product.
Source: Stacks Project, Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
abbrev externalCupCoefficients {A B : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
    (b : B ⟶ Spec (CommRingCat.of k)) (M : A.Modules) (N : B.Modules) :
    (Limits.pullback a b).Modules :=
  (tensorPullback (Limits.pullback.fst a b)).obj M ⊗
    (tensorPullback (Limits.pullback.snd a b)).obj N

/-- Pull back both classes and take their cup product.
Source: Stacks Project, Varieties, Tag 0BED, maps preceding equation-kunneth-on-cech
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def externalCup {A B : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
    (b : B ⟶ Spec (CommRingCat.of k)) (M : A.Modules) (N : B.Modules) (p q : ℕ)
    (x : scalarCohomology a M p) (y : scalarCohomology b N q) :
    scalarCohomology (Limits.pullback.fst a b ≫ a) (externalCupCoefficients a b M N) (p + q) :=
  scalarCohomologyCup (Limits.pullback.fst a b ≫ a) _ _ p q
    (scalarCohomologyPullback a (Limits.pullback.fst a b ≫ a) (Limits.pullback.fst a b) rfl M p x)
    (scalarCohomologyPullback b (Limits.pullback.fst a b ≫ a) (Limits.pullback.snd a b)
      (Limits.pullback.condition.symm) N q y)

attribute [local irreducible] scalarPullbackSquareIso

/-- The canonical coefficient comparison for pullback of the external tensor product.
Source: Stacks Project, Tags 0097 and 01CD; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def externalCupPullbackIso {A B A' B' : Scheme.{u}}
    (a : A ⟶ Spec (CommRingCat.of k)) (b : B ⟶ Spec (CommRingCat.of k))
    (a' : A' ⟶ Spec (CommRingCat.of k)) (b' : B' ⟶ Spec (CommRingCat.of k))
    (u : A' ⟶ A) (v : B' ⟶ B) (w : Limits.pullback a' b' ⟶ Limits.pullback a b)
    (h₁ : w ≫ Limits.pullback.fst a b = Limits.pullback.fst a' b' ≫ u)
    (h₂ : w ≫ Limits.pullback.snd a b = Limits.pullback.snd a' b' ≫ v)
    (M : A.Modules) (N : B.Modules) :
    (tensorPullback w).obj (externalCupCoefficients a b M N) ≅
      externalCupCoefficients a' b' ((tensorPullback u).obj M)
        ((tensorPullback v).obj N) :=
  (Classical.choose (module_pullback_tensor w)) _ _ ≪≫
    tensorIso
      (scalarPullbackSquareIso w (Limits.pullback.fst a b) (Limits.pullback.fst a' b') u h₁ M)
      (scalarPullbackSquareIso w (Limits.pullback.snd a b) (Limits.pullback.snd a' b') v h₂ N)
end
end AlgebraicGeometry.Scheme.Modules
