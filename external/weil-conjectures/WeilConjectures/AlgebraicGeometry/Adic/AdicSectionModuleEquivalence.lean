/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # Section modules of native adic sheaves

The internal action induces the ordinary module structure on each section group.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

/-- The commutative coefficient sheaf, with the native locally finite function sections.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonRing (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} := by
  let F : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} :=
    { obj := fun V ↦ CommRingCat.of
        (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left))
      map := fun f ↦ CommRingCat.ofHom (WeilCoefficients.uliftAlgHom
        (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l f.unop.left.base.hom)).toRingHom
      map_id := fun V ↦ by ext r; rfl
      map_comp := fun f g ↦ by ext r; rfl }
  refine ⟨F, ?_⟩
  let : HasLimitsOfSize.{u, u + 1} CommRingCat.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} CommRingCat.{u + 1}
  let : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_of_univLE.{u + 1, u + 1} _
  apply (Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X) F
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).2
  exact ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1})).obj
      (adicConstantSheaf l X)).property

/-- Forget sheaf descent and identify the transported coefficient monoid with its pointwise monoid.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonPresheafFunctor (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) : AdicSheaf l X ⥤
    Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj := by
  let F := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let φ : Mon.mk (adicConstantSheaf l X).obj ⟶ F.mapMon.obj (Mon.mk (adicConstantSheaf l X)) :=
    Mon.Hom.mk' (𝟙 _)
      ((Category.comp_id _).trans (adicConstantSheaf_ε_comp_map_one' X).symm)
      (by
        rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
        exact (adicConstantSheaf_μ_comp_map_mul' X).symm)
  letI : IsMonHom φ.hom := φ.isMonHom_hom
  exact F.mapMod (adicConstantSheaf l X) ⋙ Mod.comap φ.hom

/-- The module structure on sections induced by the internal action on pure tensors.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
@[instance_reducible]
noncomputable def comparisonSectionModule {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} (P : Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l)
      (adicConstantSheaf l X).obj) (V : X.ProEtᵒᵖ) :
    Module ((comparisonRing l X).obj.obj V) (P.X.obj V) := by
  change Module (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left))
    (P.X.obj V)
  let A := (adicConstantSheaf l X).obj
  let a := (Mod.act (A := A) P.X).app V
  refine
    { smul := fun r x ↦ a (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)
      one_smul := ?_
      mul_smul := ?_
      smul_zero := ?_
      smul_add := ?_
      zero_smul := ?_
      add_smul := ?_ }
  · intro r s x
    have h := ConcreteCategory.congr_hom (congr_app (Mod.mul_act (A := A) P.X) V)
      ((r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] s) ⊗ₜ x)
    exact h
  · intro x
    have h := ConcreteCategory.congr_hom (congr_app (Mod.one_act (A := A) P.X) V)
      ((1 : ULift.{u + 1} (PadicAlgCl l)) ⊗ₜ x)
    change a ((1 : ULift.{u + 1}
      (PadicAlgCl.locallyFiniteFunctions l V.unop.left)) ⊗ₜ x) = x
    change a (((η[A]).app V (1 : ULift.{u + 1} (PadicAlgCl l))) ⊗ₜ x) =
      (1 : ULift.{u + 1} (PadicAlgCl l)) • x at h
    rw [one_smul] at h
    rw [adicConstantSheaf_one_app] at h
    have hk : (1 : ULift.{u + 1} (PadicAlgCl l)).down = 1 := rfl
    rw [hk, map_one] at h
    exact h
  · intro r
    change a (r ⊗ₜ (0 : P.X.obj V)) = 0
    rw [TensorProduct.tmul_zero, map_zero]
  · intro r x y
    change a (r ⊗ₜ (x + y)) = a (r ⊗ₜ x) + a (r ⊗ₜ y)
    rw [TensorProduct.tmul_add, map_add]
  · intro r s x
    change a ((r + s) ⊗ₜ x) = a (r ⊗ₜ x) + a (s ⊗ₜ x)
    rw [TensorProduct.add_tmul, map_add]
  · intro x
    change a ((0 : ULift.{u + 1}
      (PadicAlgCl.locallyFiniteFunctions l V.unop.left)) ⊗ₜ x) = 0
    rw [TensorProduct.zero_tmul, map_zero]

/-- The presheaf of modules obtained from a presheaf with an internal coefficient action.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonModulePresheaf {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} (P : Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l)
      (adicConstantSheaf l X).obj) :
    PresheafOfModules.{u + 1} ((comparisonRing l X).obj ⋙
      forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  letI (V : X.ProEtᵒᵖ) :
      Module (((comparisonRing l X).obj ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj V)
        ((P.X ⋙ forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}).obj V) :=
    comparisonSectionModule P V
  refine PresheafOfModules.ofPresheaf
    (P.X ⋙ forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}) ?_
  intro V W f r x
  change (P.X.obj V) at x
  change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r
  exact (ConcreteCategory.congr_hom ((Mod.act (A := (adicConstantSheaf l X).obj) P.X).naturality f)
    (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)).symm

/-- Encode internal presheaf modules by their section modules, leaving maps unchanged.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonPresheafEncoding (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj ⥤
      PresheafOfModules.{u + 1} ((comparisonRing l X).obj ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  obj P := comparisonModulePresheaf P
  map {P Q} f := PresheafOfModules.homMk
    (Functor.whiskerRight f.hom
      (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1})) (by
      intro V r x
      change P.X.obj V at x
      change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r
      exact ConcreteCategory.congr_hom
        (congr_app (Mod.act_hom f) V) (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x))
  map_id M := by ext V x; rfl
  map_comp f g := by ext V x; rfl

/-- The native-to-sectionwise module functor, unchanged on underlying additive sections.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonModuleFunctor (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    AdicSheaf l X ⥤ SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X)) where
  obj M :=
    { val := comparisonModulePresheaf ((comparisonPresheafFunctor l X).obj M)
      isSheaf := ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1})).obj M.X).property }
  map f := ⟨(comparisonPresheafEncoding l X).map
    ((comparisonPresheafFunctor l X).map f)⟩
  map_id M := by ext V x; rfl
  map_comp f g := by ext V x; rfl

/-- Recover the vector-space scalar action by restricting along constant coefficient functions.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
@[instance_reducible]
noncomputable def comparisonScalarModule {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) (V : X.ProEtᵒᵖ) :
    Module (ULift.{u + 1} (PadicAlgCl l)) (P.val.obj V) :=
  Module.compHom (P.val.obj V) (algebraMap _
    (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left)))

/-- The vector-space presheaf recovered from sectionwise modules via constant functions.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonVectorPresheaf {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) : X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l := by
  letI (V : X.ProEtᵒᵖ) := comparisonScalarModule P V
  exact
    { obj := fun V ↦ ModuleCat.of _ (P.val.obj V)
      map := fun {V W} f ↦ ModuleCat.ofHom
        { toFun := P.val.map f
          map_add' := (P.val.map f).hom.map_add
          map_smul' := fun k m ↦ by
            exact P.val.map_smul f (algebraMap _
              (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left)) k) m }
      map_id := fun V ↦ by ext m; simp
      map_comp := fun f g ↦ by ext m; exact P.val.map_comp_apply f g m }

/-- The vector-space sheaf recovered from a sectionwise module sheaf.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonVectorSheaf {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) := by
  refine ⟨comparisonVectorPresheaf P, ?_⟩
  exact Presheaf.isSheaf_of_isSheaf_comp _ _
    (forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}) P.isSheaf

/-- The ordinary scalar action as a linear map out of a tensor product.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def sectionOrdinaryAction
    (k S N : Type (u + 1)) [CommRing k] [CommRing S] [Algebra k S]
    [AddCommGroup N] [Module S N] :
    letI := Module.compHom N (algebraMap k S)
    ModuleCat.of k S ⊗ ModuleCat.of k N ⟶ ModuleCat.of k N := by
  letI := Module.compHom N (algebraMap k S)
  exact ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ k
    (fun (r : S) (m : N) ↦ r • m)
    (fun r s m ↦ add_smul r s m)
    (fun c r m ↦ by
      change (c • r) • m = algebraMap k S c • (r • m)
      rw [Algebra.smul_def, mul_smul])
    (fun r m n ↦ smul_add r m n)
    (fun c r m ↦ by
      change r • (algebraMap k S c • m) = algebraMap k S c • (r • m)
      rw [← mul_smul, mul_comm r, mul_smul])))

/-- The sectionwise module action as a natural vector-space bilinear pairing.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonReverseAction {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) :
    (adicConstantSheaf l X).obj ⊗ comparisonVectorPresheaf P ⟶
      comparisonVectorPresheaf P where
  app V := sectionOrdinaryAction (ULift.{u + 1} (PadicAlgCl l))
    (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left)) (P.val.obj V)
  naturality V W f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro r m
    exact (P.val.map_smul f r m).symm

/-- The internal presheaf module constructed from a sectionwise module sheaf.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonReversePresheaf {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) :
    Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj := by
  let a := comparisonReverseAction P
  letI : ModObj (adicConstantSheaf l X).obj (comparisonVectorPresheaf P) :=
    ModObj.mk' _ a (by
      apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro c m
      change (P.val.obj V) at m
      change (ULift.up (algebraMap (PadicAlgCl l)
        (PadicAlgCl.locallyFiniteFunctions l V.unop.left) c.down) :
          ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left)) •
            (m : P.val.obj V) = _
      rfl) (by
      apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_threefold
      intro r s m
      change (P.val.obj V) at m
      change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r s
      change (r * s) • (m : P.val.obj V) = r • s • (m : P.val.obj V)
      exact mul_smul r s m)
  exact ⟨comparisonVectorPresheaf P⟩

/-- Sheafify internal presheaf modules and identify the coefficient monoid through the counit.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonModuleReflector (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj ⥤ AdicSheaf l X := by
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let F := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let φ : Mon.mk (adicConstantSheaf l X).obj ⟶ F.mapMon.obj (Mon.mk (adicConstantSheaf l X)) :=
    Mon.Hom.mk' (𝟙 _)
      ((Category.comp_id _).trans (adicConstantSheaf_ε_comp_map_one' X).symm)
      (by
        rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
        exact (adicConstantSheaf_μ_comp_map_mul' X).symm)
  letI : IsMonHom φ.hom := φ.isMonHom_hom
  let ψ := (adj.homEquiv _ _).symm φ.hom
  have hψ : ψ = adj.counit.app (adicConstantSheaf l X) := by
    simp [ψ, φ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by
    rw [hψ]
    exact @isMonHom_ofIso _ _ _ _ _
      ((presheafToSheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).monObjObj
        (adicConstantSheaf l X).obj)
      (asIso (adj.counit.app (adicConstantSheaf l X)))
  exact adj.modLeft φ.hom

/-- The native module obtained by sheafifying the recovered internal presheaf action.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonLiftModule {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) : AdicSheaf l X :=
  (comparisonModuleReflector l X).obj (comparisonReversePresheaf P)

/-- The sheafification unit as an internal presheaf-module morphism.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonLiftUnit {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (comparisonRing l X))) : comparisonReversePresheaf P ⟶
      (comparisonPresheafFunctor l X).obj (comparisonLiftModule P) := by
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let F := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let φ : Mon.mk (adicConstantSheaf l X).obj ⟶ F.mapMon.obj (Mon.mk (adicConstantSheaf l X)) :=
    Mon.Hom.mk' (𝟙 _)
      ((Category.comp_id _).trans (adicConstantSheaf_ε_comp_map_one' X).symm)
      (by
        rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
        exact (adicConstantSheaf_μ_comp_map_mul' X).symm)
  letI : IsMonHom φ.hom := φ.isMonHom_hom
  let ψ := (adj.homEquiv _ _).symm φ.hom
  have hψ : ψ = adj.counit.app (adicConstantSheaf l X) := by
    simp [ψ, φ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by
    rw [hψ]
    exact @isMonHom_ofIso _ _ _ _ _
      ((presheafToSheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).monObjObj
        (adicConstantSheaf l X).obj)
      (asIso (adj.counit.app (adicConstantSheaf l X)))
  exact (adj.modAdjunction φ.hom).unit.app (comparisonReversePresheaf P)

/-- The presheaf forgetful functor on native modules is fully faithful.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonPresheafFullyFaithful (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (comparisonPresheafFunctor l X).FullyFaithful where
  preimage {M N} f := by
    refine Mod.homMk ⟨f.hom⟩ ?_
    apply Sheaf.tensor_hom_ext
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    have h := Mod.act_hom f
    simp only [comparisonPresheafFunctor, Functor.comp_obj, Mod.act_comap_obj,
      Functor.act_mapMod_obj, id_whiskerRight, Category.id_comp, Category.assoc] at h
    convert! h using 1
  map_preimage f := by apply Mod.hom_ext; rfl
  preimage_map f := by apply Mod.hom_ext; rfl

noncomputable local instance {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) :
    SMul ((adicConstantSheaf l X).obj.obj V)
      (((comparisonModuleFunctor l X).obj M).val.obj V) :=
  (comparisonSectionModule ((comparisonPresheafFunctor l X).obj M) V).toSMul

/-- The action of a constant coefficient on native sections is their original vector-space action.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
theorem comparison_constant_smul {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (k : ULift.{u + 1} (PadicAlgCl l))
    (m : M.X.obj.obj V) :
    ((η[(adicConstantSheaf l X).obj]).app V k) •
        (show ((comparisonModuleFunctor l X).obj M).val.obj V from m) = k • m := by
  let a := (comparisonPresheafFunctor l X).obj M
  have h := ConcreteCategory.congr_hom
    (congr_app (Mod.one_act (A := (adicConstantSheaf l X).obj) a.X) V) (k ⊗ₜ m)
  change (Mod.act a.X).app V
    (((η[(adicConstantSheaf l X).obj]).app V k) ⊗ₜ m) = k • m at h
  exact h

/-- A sectionwise linear map recovered as a native module map.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonPreimageMap {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {M N : AdicSheaf l X}
    (f : (comparisonModuleFunctor l X).obj M ⟶ (comparisonModuleFunctor l X).obj N) :
    M ⟶ N := by
  apply (comparisonPresheafFullyFaithful l X).preimage
  let a := (comparisonPresheafFunctor l X).obj M
  let b := (comparisonPresheafFunctor l X).obj N
  let t : a.X ⟶ b.X :=
    { app V := by
        let g : a.X.obj V →+ b.X.obj V := (f.val.app V).hom.toAddMonoidHom
        refine ModuleCat.ofHom { g with map_smul' := ?_ }
        intro k m
        have ha := ConcreteCategory.congr_hom
          (congr_app (Mod.one_act (A := (adicConstantSheaf l X).obj) a.X) V)
            (k ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] m)
        have hb := ConcreteCategory.congr_hom
          (congr_app (Mod.one_act (A := (adicConstantSheaf l X).obj) b.X) V)
            (k ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] g m)
        change g (k • m) = k • g m
        have hf := (f.val.app V).hom.map_smul
          ((η[(adicConstantSheaf l X).obj]).app V k) m
        change g ((Mod.act a.X).app V
          (((η[(adicConstantSheaf l X).obj]).app V k) ⊗ₜ m)) =
            (Mod.act b.X).app V
              (((η[(adicConstantSheaf l X).obj]).app V k) ⊗ₜ g m) at hf
        change (Mod.act a.X).app V
          (((η[(adicConstantSheaf l X).obj]).app V k) ⊗ₜ m) = k • m at ha
        change (Mod.act b.X).app V
          (((η[(adicConstantSheaf l X).obj]).app V k) ⊗ₜ g m) = k • g m at hb
        rw [ha, hb] at hf
        exact hf
      naturality V W g := by
        ext m
        exact ConcreteCategory.congr_hom (f.val.naturality g) m }
  refine Mod.homMk t ?_
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro r m
  exact (f.val.app V).hom.map_smul r m

/-- The native-to-sectionwise module functor is fully faithful.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonModuleFullyFaithful (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (comparisonModuleFunctor l X).FullyFaithful where
  preimage f := comparisonPreimageMap f
  map_preimage f := by ext V m; rfl
  preimage_map f := by apply Mod.hom_ext; ext V m; rfl

/-- The underlying map of the internal module lift unit is the vector sheafification unit.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
theorem comparisonLiftUnit_hom {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X))) :
    (comparisonLiftUnit P).hom =
      toSheafify (Scheme.ProEt.topology X) (comparisonVectorPresheaf P) := by
  unfold comparisonLiftUnit
  rw [Adjunction.modAdjunction_unit_app_hom]
  rfl

/-- The recovered presheaf action has precisely the original section module structure.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonReverseSections {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X))) :
    comparisonModulePresheaf (comparisonReversePresheaf P) ≅ P.val := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    rfl
  · intro V W f
    ext m
    rfl

/-- Sheafifying a sectionwise module and re-encoding its action recovers that module.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonLiftCounit {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X))) :
    (comparisonModuleFunctor l X).obj (comparisonLiftModule P) ≅ P := by
  let t := comparisonLiftUnit P
  have ht : IsIso t.hom := by
    dsimp only [t]
    rw [comparisonLiftUnit_hom]
    exact isIso_toSheafify (Scheme.ProEt.topology X) (comparisonVectorSheaf P).property
  have : IsIso ((Mod.forget (adicConstantSheaf l X).obj).map t) := ht
  have : IsIso t := isIso_of_reflects_iso t (Mod.forget (adicConstantSheaf l X).obj)
  let e := (comparisonPresheafEncoding l X).mapIso (asIso t)
  let c := e.symm ≪≫ comparisonReverseSections P
  exact
    { hom := ⟨c.hom⟩
      inv := ⟨c.inv⟩
      hom_inv_id := SheafOfModules.hom_ext c.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext c.inv_hom_id }

/-- Full faithfulness and the explicit sheafified preimage make the section functor an equivalence.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable instance comparisonModuleFunctor_isEquivalence
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (comparisonModuleFunctor l X).IsEquivalence := by
  let F := comparisonModuleFunctor l X
  let : F.Full := (comparisonModuleFullyFaithful l X).full
  let : F.Faithful := (comparisonModuleFullyFaithful l X).faithful
  let : F.EssSurj := ⟨fun P ↦ ⟨comparisonLiftModule P, ⟨comparisonLiftCounit P⟩⟩⟩
  exact {}

/-- Native adic modules identify with the sectionwise modules over the sheaf of locally
finite coefficient functions. Source: Stacks 03CV and 0GMW.
(blueprint: lem-sf-adic-section-module-equivalence).
The internal action restricts to sectionwise bilinear actions, whose laws follow on pure
threefold tensors and the unit. Conversely restrict scalars along constant functions and
extend the action across monoidal sheafification. The module adjunction unit is invertible
because the original section presheaf already is a sheaf. The forward functor is fully
faithful since scalar-linear maps recover the original vector-space linearity and the
internal action equation is detected before sheafification. -/
noncomputable def adicSectionModuleEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    AdicSheaf l X ≌ SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) :=
  (comparisonModuleFunctor l X).asEquivalence

/-- The section module of the native regular module is the ordinary regular sheaf module.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonUnitIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (comparisonModuleFunctor l X).obj (AdicSheaf.unit l X) ≅
      SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) := by
  let e : ((comparisonModuleFunctor l X).obj (AdicSheaf.unit l X)).val ≅
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X))).val :=
    PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) (by
      intro r
      ext m
      change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r m
      have h := congr_app (adicConstantSheaf_μ_comp_map_mul' (l := l) X) V
      have hh := ConcreteCategory.congr_hom h
        (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] m)
      exact hh.symm)) (by intro V W f; ext m; rfl)
  exact
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id }

-- Pin the native colimit instance before the functor appears in its dependent type.
/-- Native adic modules have coproducts in the required index universe.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable instance comparisonNativeCoproducts (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) : HasCoproducts.{u + 1} (AdicSheaf l X) := by
  intro I
  let : HasColimitsOfSize.{u + 1, u + 1} (AdicSheaf l X) :=
    IsGrothendieckAbelian.hasColimits (AdicSheaf l X)
  exact HasColimitsOfSize.has_colimits_of_shape (Discrete I)

attribute [local irreducible] comparisonModuleFunctor

/-- The section equivalence identifies a coordinate sum of native units with the free module sheaf.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
noncomputable def comparisonFreeIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (I : Type (u + 1)) :
    (comparisonModuleFunctor l X).obj (∐ (fun (_ : I) ↦ AdicSheaf.unit l X)) ≅
      SheafOfModules.free (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) I := by
  exact PreservesCoproduct.iso (comparisonModuleFunctor l X)
    (fun (_ : I) ↦ AdicSheaf.unit l X) ≪≫
      Sigma.mapIso (fun (_ : I) ↦ comparisonUnitIso l X)

/-- The free-module comparison preserves each coordinate inclusion.
Source: Stacks 03CV and 0GMW; the explicit native action and sheafification.
(blueprint: lem-sf-adic-section-module-equivalence). -/
theorem comparisonFreeIso_coordinates (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (I : Type (u + 1)) (i : I) :
    (comparisonModuleFunctor l X).map
        (Sigma.ι (fun (_ : I) ↦ AdicSheaf.unit l X) i) ≫
          (comparisonFreeIso l X I).hom =
      (comparisonUnitIso l X).hom ≫ SheafOfModules.ιFree i := by
  rw [comparisonFreeIso, Iso.trans_hom, ← Category.assoc]
  have hι : (comparisonModuleFunctor l X).map
      (Sigma.ι (fun (_ : I) ↦ AdicSheaf.unit l X) i) ≫
      (PreservesCoproduct.iso (comparisonModuleFunctor l X)
        (fun (_ : I) ↦ AdicSheaf.unit l X)).hom =
      Sigma.ι (fun (_ : I) ↦ (comparisonModuleFunctor l X).obj
        (AdicSheaf.unit l X)) i := by
    apply (cancel_mono (PreservesCoproduct.iso (comparisonModuleFunctor l X)
      (fun (_ : I) ↦ AdicSheaf.unit l X)).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, PreservesCoproduct.inv_hom]
    exact (ι_comp_sigmaComparison (comparisonModuleFunctor l X)
      (fun (_ : I) ↦ AdicSheaf.unit l X) i).symm
  rw [hι, Sigma.ι_mapIso_hom]
  rfl


end AlgebraicGeometry.ProEtale
