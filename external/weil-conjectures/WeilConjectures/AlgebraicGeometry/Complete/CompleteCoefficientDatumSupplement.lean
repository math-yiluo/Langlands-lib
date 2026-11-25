/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.AlgebraicGeometry.CompleteCoefficientDatum

/-!
# Adic coefficient datum and reduction tower

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-complete-coefficient-datum.md, order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum).

The construction uses one K-flat model with flat terms. Quotient reductions are actual
changed complexes. The ordinary balancing and transition maps are specified uniquely on
local tensor generators; their images under localization are the canonical derived maps.

## Main definitions

- `CompleteCoefficientDatum`: the ring, ideal, torsion, and perfectness conditions.
- `AdicKFlatModel`: one flat-term K-flat representative of an arbitrary derived object.
- `adicReduction`, `adicReductionUnderlying`: the quotient reduction and its scalar restriction.
- `adicTransition`: the localized map induced by the quotient homomorphism.
- `adicNormalization`: the localized scalar-extension balancing isomorphism.

## Main statements

- `adicKFlatModel_exists`: availability of models for every unbounded derived object.
- `adicTransition_id`, `adicTransition_comp`: the transition identities.
- `adicNormalization_cocycle`, `adicNormalization_unit`: normalization coherence.
- `adicReductionUnderlying_tensor`: comparison with the recorded derived tensor product.
-/

@[expose] public section

universe t

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The constant commutative ring sheaf, before forgetting commutativity.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicConstantRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))

/-- The underlying constant ring sheaf used by the recorded pro-etale derived category.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicModuleRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (adicConstantRing X A)

/-- The functorial constant sheaf map associated to a coefficient homomorphism.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicConstantMap (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    adicConstantRing X A ⟶ adicConstantRing X B :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
    (CommRingCat.ofHom (RingHom.ulift φ))

private theorem adicConstantMap_id (X : Scheme.{t}) (A : Type t) [CommRing A] :
    adicConstantMap X (RingHom.id A) = 𝟙 (adicConstantRing X A) := by
  unfold adicConstantMap
  change (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map (𝟙 _) = _
  exact CategoryTheory.Functor.map_id _ _

private theorem adicConstantMap_comp (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    adicConstantMap X φ ≫ adicConstantMap X ψ = adicConstantMap X (ψ.comp φ) := by
  unfold adicConstantMap
  rw [← Functor.map_comp]
  rfl

/-- The same coefficient map, regarded as a map of ring sheaves.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicModuleMap (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    adicModuleRing X A ⟶ adicModuleRing X B :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (adicConstantMap X φ)

/-- Localization into the exact derived category recorded for the small pro-etale site.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicLocalization (X : Scheme.{t}) (A : Type t) [CommRing A] :
    CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ ⥤
      proEtaleDerivedCategory X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- One K-flat flat-term representative of the arbitrary derived object K. The realization
is part of the choice of model, rather than a restriction on K.
Source: blueprint order 1255, construction step 1; Stacks Tag 06YS
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
structure AdicKFlatModel (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (K : proEtaleDerivedCategory X Λ) where
  complex : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ
  isKFlat : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X Λ) complex
  flatTerms : ∀ p : ℤ, CategoryTheory.exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (adicConstantRing X Λ)) (complex.X p))
  realization :
    (adicLocalization X Λ).obj complex ≅ K

/-- Termwise scalar extension, with the target coefficient action retained.
Source: blueprint order 1255, steps 1 and 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicChange (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :=
  SheafOfModules.changeOfRingsComplex.{t + 1, t} (adicConstantMap X φ) P

/-- Termwise restriction of scalars, retaining the same abelian sheaves and differentials.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :=
  ((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- The local pure tensor s tensor m, mapped into the sheafified scalar extension.
Source: blueprint order 1255, steps 2 and 3; Stacks Tag 03EK
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M)).app U
        (s ⊗ₜ[(adicConstantRing X A).obj.obj U,
          ((adicConstantMap X φ).hom.app U).hom] m)

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorSection_smul (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s r : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    adicTensorSection X φ M U (s * r) m = s • adicTensorSection X φ M U r m := by
  unfold adicTensorSection
  rw [← ModuleCat.ExtendScalars.smul_tmul ((adicConstantMap X φ).hom.app U).hom s r m]
  exact (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorHom_ext (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    {N : SheafOfModules.{t + 1} (adicModuleRing X B)}
    (f g : SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U),
      f.val.app U (adicTensorSection X φ M U s m) =
        g.val.app U (adicTensorSection X φ M U s m)) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv.{t + 1} (𝟙 (adicModuleRing X B).obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h U 1 m

set_option backward.isDefEq.respectTransparency false in
private theorem adicChangeHom_tensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {M N : SheafOfModules.{t + 1} (adicModuleRing X A)} (f : M ⟶ N)
    (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X φ) M f).val.app U
        (adicTensorSection X φ M U s m) =
      adicTensorSection X φ N U s (f.val.app U m) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) N :=
    { app := fun V ↦ (ModuleCat.extendScalars ((adicConstantMap X φ).hom.app V).hom).map
        (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality _ M f }
  have hn := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.naturality p
  have hv := congrArg (fun q ↦ q.app U) hn
  have hx := ConcreteCategory.congr_hom hv
    (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m)
  change adicTensorSection X φ N U s (f.val.app U m) = _ at hx
  exact hx.symm

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorSection_map (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    {U V : X.ProEtᵒᵖ} (i : U ⟶ V)
    (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1}
      (adicConstantMap X φ) M).val.map i (adicTensorSection X φ M U s m) =
    adicTensorSection X φ M V ((adicConstantRing X B).obj.map i s) (M.val.map i m) := by
  have hn := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{t + 1}
      (𝟙 (adicModuleRing X B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M)) i
    (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m)
  change _ = (SheafOfModules.changeOfRings.{t, t + 1, t + 1}
    (adicConstantMap X φ) M).val.map i (adicTensorSection X φ M U s m) at hn
  have ht := Classical.choose_spec
    (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1} (adicConstantMap X φ) M i) s m
  change SheafOfModules.changeOfRingsMap (adicConstantMap X φ) M i _ = _ at ht
  change ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
        (adicConstantMap X φ) M)).app V
      (SheafOfModules.changeOfRingsMap (adicConstantMap X φ) M i _) = _ at hn
  rw [ht] at hn
  exact hn.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicTranspose (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (f : SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N) :
    M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N where
  val.app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{t + 1, t + 1, t + 1}
    ((adicConstantMap X φ).hom.app U).hom
      ((PresheafOfModules.sheafificationHomEquiv.{t + 1}
        (𝟙 (adicModuleRing X B).obj) f).app U)
  val.naturality {U V} i := by
    ext m
    change f.val.app V (adicTensorSection X φ M V 1 (M.val.map i m)) =
      N.val.map i (f.val.app U (adicTensorSection X φ M U 1 m))
    have hn := PresheafOfModules.naturality_apply f.val i
      (adicTensorSection X φ M U 1 m)
    rw [adicTensorSection_map, map_one] at hn
    exact hn

set_option backward.isDefEq.respectTransparency false in
private theorem adicTranspose_injective (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B)) :
    Function.Injective (adicTranspose X φ M N) := by
  intro f g h
  apply (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have hv := congrArg (fun q ↦ q.val.app U) h
  exact ConcreteCategory.congr_hom hv m

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorAddHom_ext (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : Sheaf (ProEt.topology X) AddCommGrpCat.{t + 1})
    (f g : (SheafOfModules.toSheaf (adicModuleRing X B)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U),
      f.hom.app U (adicTensorSection X φ M U s m) =
        g.hom.app U (adicTensorSection X φ M U s m)) : f = g := by
  apply ((CategoryTheory.sheafificationAdjunction (ProEt.topology X)
    AddCommGrpCat.{t + 1}).homEquiv
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
        (adicConstantMap X φ) M).presheaf N).injective
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let : Module ((adicConstantRing X A).obj.obj U) ((adicConstantRing X B).obj.obj U) :=
    Module.compHom _ ((adicConstantMap X φ).hom.app U).hom
  induction z using TensorProduct.inductionOn with
  | tmul s m => exact h U s m
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem adicModuleLift_tmul (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) (U : X.ProEtᵒᵖ)
    (M : ModuleCat.{t + 1} ((adicConstantRing X A).obj.obj U))
    (N : ModuleCat.{t + 1} ((adicConstantRing X B).obj.obj U))
    (g : M ⟶ (ModuleCat.restrictScalars ((adicConstantMap X φ).hom.app U).hom).obj N)
    (s : (adicConstantRing X B).obj.obj U) (m : M) :
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
      ((adicConstantMap X φ).hom.app U).hom g
        (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m) =
      s • (show N from g m) := by
  let : Module ((adicConstantRing X A).obj.obj U) ((adicConstantRing X B).obj.obj U) :=
    Module.compHom _ ((adicConstantMap X φ).hom.app U).hom
  let : Module ((adicConstantRing X A).obj.obj U) N :=
    Module.compHom N ((adicConstantMap X φ).hom.app U).hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicLiftSeed (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (g : M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N) :
    SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶
      N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
    ((adicConstantMap X φ).hom.app U).hom (g.val.app U)
  naturality {U V} i := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
      ((adicConstantMap X φ).hom.app V).hom (g.val.app V)
        (SheafOfModules.changeOfRingsMap (adicConstantMap X φ) M i _) =
      N.val.map i
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
          ((adicConstantMap X φ).hom.app U).hom (g.val.app U) _)
    erw [Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1}
        (adicConstantMap X φ) M i) 1 m, map_one]
    rw [adicModuleLift_tmul, adicModuleLift_tmul]
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g.val i m

private noncomputable def adicLift (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (g : M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).symm (adicLiftSeed X φ M N g)

set_option backward.isDefEq.respectTransparency false in
private theorem adicLift_tensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (g : M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N)
    (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (adicLift X φ M N g).val.app U (adicTensorSection X φ M U s m) =
      s • (show N.val.obj U from g.val.app U m) := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).apply_symm_apply (adicLiftSeed X φ M N g)
  have hv := congrArg (fun q ↦ q.app U) h
  have hx := ConcreteCategory.congr_hom hv
    (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m)
  dsimp [adicLiftSeed] at hx
  exact hx.trans (adicModuleLift_tmul X φ U _ _ (g.val.app U) s m)

private theorem adicConstantMap_comp_app (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (U : X.ProEtᵒᵖ) :
    ((adicConstantMap X χ).hom.app U).hom =
      ((adicConstantMap X ψ).hom.app U).hom.comp
        ((adicConstantMap X φ).hom.app U).hom := by
  have hm := adicConstantMap_comp X φ ψ
  rw [h] at hm
  exact congrArg CommRingCat.Hom.hom (congrArg (fun q ↦ q.hom.app U) hm).symm

private noncomputable def adicRestrictCompIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (N : SheafOfModules.{t + 1} (adicModuleRing X C)) :
    (SheafOfModules.restrictScalars (adicModuleMap X χ)).obj N ≅
      (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj
        ((SheafOfModules.restrictScalars (adicModuleMap X ψ)).obj N) where
  hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _
    (adicConstantMap_comp_app X φ ψ χ h U) (N.val.obj U)).hom
  hom.val.naturality i := by ext m; rfl
  inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _
    (adicConstantMap_comp_app X φ ψ χ h U) (N.val.obj U)).inv
  inv.val.naturality i := by ext m; rfl

private noncomputable def adicSheafExtendUnit (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) :=
  adicTranspose X φ M _ (𝟙 _)

private noncomputable def adicSheafBalance (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X ψ)
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ⟶
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M :=
  adicLift X ψ _ _ (adicLift X φ _ _
    (adicSheafExtendUnit X χ M ≫ (adicRestrictCompIso X φ ψ χ h _).hom))

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafBalance_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X C).obj.obj U) (r : (adicConstantRing X B).obj.obj U)
    (m : M.val.obj U) :
    (adicSheafBalance X φ ψ χ h M).val.app U
      (adicTensorSection X ψ _ U s (adicTensorSection X φ M U r m)) =
    adicTensorSection X χ M U (s * (adicConstantMap X ψ).hom.app U r) m := by
  unfold adicSheafBalance
  rw [adicLift_tensorSection, adicLift_tensorSection]
  change s • ((adicConstantMap X ψ).hom.app U r •
    adicTensorSection X χ M U 1 m) = _
  rw [← mul_smul, ← adicTensorSection_smul, mul_one]

private noncomputable def adicSheafBalanceInv (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M ⟶
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X ψ)
        (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) :=
  adicLift X χ _ _ (adicSheafExtendUnit X φ M ≫
    (SheafOfModules.restrictScalars (adicModuleMap X φ)).map
      (adicSheafExtendUnit X ψ _) ≫ (adicRestrictCompIso X φ ψ χ h _).inv)

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafBalanceInv_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X C).obj.obj U) (m : M.val.obj U) :
    (adicSheafBalanceInv X φ ψ χ h M).val.app U (adicTensorSection X χ M U s m) =
    s • adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U 1 m) := by
  exact adicLift_tensorSection X χ _ _ _ U s m

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicSheafBalanceIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X ψ)
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ≅
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M where
  hom := adicSheafBalance X φ ψ χ h M
  inv := adicSheafBalanceInv X φ ψ χ h M
  hom_inv_id := by
    apply adicTranspose_injective X ψ
    apply adicTranspose_injective X φ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adicSheafBalanceInv X φ ψ χ h M).val.app U
      ((adicSheafBalance X φ ψ χ h M).val.app U
        (adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U 1 m))) =
      adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U 1 m)
    rw [adicSheafBalance_tensorSection, map_one, one_mul,
      adicSheafBalanceInv_tensorSection, one_smul]
  inv_hom_id := by
    apply adicTranspose_injective X χ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adicSheafBalance X φ ψ χ h M).val.app U
      ((adicSheafBalanceInv X φ ψ χ h M).val.app U
        (adicTensorSection X χ M U 1 m)) = adicTensorSection X χ M U 1 m
    rw [adicSheafBalanceInv_tensorSection, one_smul, adicSheafBalance_tensorSection,
      map_one, one_mul]

/-- The ordinary balancing map is uniquely specified on local tensor generators and is
invertible. Source: blueprint order 1255, step 3; Stacks Tags 03EK and 0D6D.
Proof: send s tensor (r tensor m) to (s * ψ(r)) tensor m. The balancing relations
make this well-defined; restriction maps commute with the formula. Sheafification gives
the sheaf morphism. Its inverse sends s tensor m to s tensor (1 tensor m).
The differential acts only on m, so these are chain maps. The two composites are
identities by the balancing relations. Local tensor generators prove uniqueness.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalance_exists (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    ∃! f : adicChange X ψ (adicChange X φ P) ⟶ adicChange X χ P,
      IsIso f ∧ ∀ (p : ℤ) (U : X.ProEtᵒᵖ)
        (s : (adicConstantRing X C).obj.obj U)
        (r : (adicConstantRing X B).obj.obj U) (m : (P.X p).val.obj U),
        (f.f p).val.app U
          (adicTensorSection X ψ _ U s (adicTensorSection X φ _ U r m)) =
          adicTensorSection X χ _ U (s * (adicConstantMap X ψ).hom.app U r) m := by
  let e : adicChange X ψ (adicChange X φ P) ≅ adicChange X χ P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ adicSheafBalanceIso X φ ψ χ h (P.X p)) (by
        intro i j hij
        apply adicTranspose_injective X ψ
        apply adicTensorHom_ext X φ
        intro U r m
        change (SheafOfModules.changeOfRingsHom (adicConstantMap X χ) _ (P.d i j)).val.app U
            ((adicSheafBalance X φ ψ χ h (P.X i)).val.app U
              (adicTensorSection X ψ _ U 1 (adicTensorSection X φ _ U r m))) =
          (adicSheafBalance X φ ψ χ h (P.X j)).val.app U
            ((SheafOfModules.changeOfRingsHom (adicConstantMap X ψ) _
              (SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (P.d i j))).val.app U
                (adicTensorSection X ψ _ U 1 (adicTensorSection X φ _ U r m)))
        rw [adicSheafBalance_tensorSection, adicChangeHom_tensorSection,
          adicChangeHom_tensorSection, adicChangeHom_tensorSection]
        exact (adicSheafBalance_tensorSection X φ ψ χ h (P.X j) U 1 r
          ((P.d i j).val.app U m)).symm)
  refine ⟨e.hom, ⟨inferInstance, ?_⟩, ?_⟩
  · intro p U s r m
    exact adicSheafBalance_tensorSection X φ ψ χ h (P.X p) U s r m
  · intro f hf
    apply HomologicalComplex.hom_ext
    intro p
    apply adicTranspose_injective X ψ
    apply adicTensorHom_ext X φ
    intro U r m
    exact (hf.2 p U 1 r m).trans
      (adicSheafBalance_tensorSection X φ ψ χ h (P.X p) U 1 r m).symm

/-- The uniquely characterized ordinary balancing chain map.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicBalanceHom (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X ψ (adicChange X φ P) ⟶ adicChange X χ P :=
  Classical.choose (adicBalance_exists X φ ψ χ h P)

/-- Compatibility of the quotient maps with the coefficient map from Λ.
Source: blueprint order 1255, step 2.
Proof: both composites send the class of x to its class modulo I^a; quotient induction
reduces the equality to the formula for Ideal.Quotient.factor.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_comp_mk {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (b a : ℕ) (hab : a ≤ b) :
    (adicQuotientMap I b a hab).comp (Ideal.Quotient.mk (I ^ b)) =
      Ideal.Quotient.mk (I ^ a) := by
  exact Ideal.Quotient.factor_comp_mk _

/-- The quotient-coefficient reduction, computed by the fixed K-flat model.
Source: blueprint order 1255, step 1; Stacks Tag 06YY
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReduction (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n : ℕ)) :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (n : ℕ))).obj (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n
    : ℕ))) M.complex)

/-- The same reduction after termwise restriction of scalars to Λ.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReductionUnderlying (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) : proEtaleDerivedCategory X Λ :=
  (adicLocalization X Λ).obj
    (adicRestrict X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex))

private noncomputable def adicSheafTransition (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ⟶
    (SheafOfModules.restrictScalars (adicModuleMap X χ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M) :=
  (SheafOfModules.restrictScalars (adicModuleMap X φ)).map
      (adicSheafExtendUnit X ψ _) ≫ (adicRestrictCompIso X φ ψ χ h _).inv ≫
    (SheafOfModules.restrictScalars (adicModuleMap X χ)).map
      (adicSheafBalance X φ ψ χ h M)

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafTransition_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (r : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (adicSheafTransition X φ ψ χ h M).val.app U (adicTensorSection X φ M U r m) =
      adicTensorSection X χ M U ((adicConstantMap X ψ).hom.app U r) m := by
  change (adicSheafBalance X φ ψ χ h M).val.app U
    (adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U r m)) = _
  rw [adicSheafBalance_tensorSection, one_mul]

/-- The transition chain map is uniquely specified by applying the quotient homomorphism
on the coefficient tensor factor. Source: blueprint order 1255, step 2; Stacks Tag 03EK.
Proof: the formula is balanced over Λ and commutes with restrictions. Extend it by the
universal property of module sheafification. It is Λ-linear after restriction of scalars
and commutes with the differential, which acts on the model factor. Tensor generators
locally generate the sheafifications in every degree, proving uniqueness.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransitionComplex_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) :
    ∃! f :
      adicRestrict X (Ideal.Quotient.mk (I ^ (b : ℕ)))
        (adicChange X (Ideal.Quotient.mk (I ^ (b : ℕ))) P) ⟶
      adicRestrict X (Ideal.Quotient.mk (I ^ (a : ℕ)))
        (adicChange X (Ideal.Quotient.mk (I ^ (a : ℕ))) P),
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ)
        (r : (adicConstantRing X (Λ ⧸ I ^ (b : ℕ))).obj.obj U)
        (m : (P.X p).val.obj U),
        (f.f p).val.app U (adicTensorSection X (Ideal.Quotient.mk (I ^ (b : ℕ)))
          _ U r m) =
        adicTensorSection X (Ideal.Quotient.mk (I ^ (a : ℕ))) _ U
          ((adicConstantMap X (adicQuotientMap I b a hab)).hom.app U r) m := by
  let φ := Ideal.Quotient.mk (I ^ (b : ℕ))
  let ψ := adicQuotientMap I b a hab
  let χ := Ideal.Quotient.mk (I ^ (a : ℕ))
  have h : ψ.comp φ = χ := adicQuotientMap_comp_mk I b a hab
  let f : adicRestrict X φ (adicChange X φ P) ⟶
      adicRestrict X χ (adicChange X χ P) :=
    { f p := adicSheafTransition X φ ψ χ h (P.X p)
      comm' i j hij := by
        apply (SheafOfModules.toSheaf (adicModuleRing X Λ)).map_injective
        apply adicTensorAddHom_ext X φ
        intro U r m
        change (SheafOfModules.changeOfRingsHom (adicConstantMap X χ) _ (P.d i j)).val.app U
            ((adicSheafTransition X φ ψ χ h (P.X i)).val.app U
              (adicTensorSection X φ _ U r m)) =
          (adicSheafTransition X φ ψ χ h (P.X j)).val.app U
            ((SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (P.d i j)).val.app U
              (adicTensorSection X φ _ U r m))
        rw [adicSheafTransition_tensorSection, adicChangeHom_tensorSection,
          adicChangeHom_tensorSection, adicSheafTransition_tensorSection] }
  refine ⟨f, ?_, ?_⟩
  · intro p U r m
    exact adicSheafTransition_tensorSection X φ ψ χ h (P.X p) U r m
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro p
    apply (SheafOfModules.toSheaf (adicModuleRing X Λ)).map_injective
    apply adicTensorAddHom_ext X φ
    intro U r m
    exact (hg p U r m).trans
      (adicSheafTransition_tensorSection X φ ψ χ h (P.X p) U r m).symm

/-- Apply the quotient map on the scalar factor, with the original Λ-action retained.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTransitionComplex (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) :
    adicRestrict X (Ideal.Quotient.mk (I ^ (b : ℕ)))
      (adicChange X (Ideal.Quotient.mk (I ^ (b : ℕ))) P) ⟶
    adicRestrict X (Ideal.Quotient.mk (I ^ (a : ℕ)))
      (adicChange X (Ideal.Quotient.mk (I ^ (a : ℕ))) P) :=
  Classical.choose (adicTransitionComplex_exists X I P b a hab)

end AlgebraicGeometry.Scheme
