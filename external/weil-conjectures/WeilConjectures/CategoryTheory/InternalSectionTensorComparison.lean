/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat

/-! # Internal and sectionwise tensor products

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW;
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify

namespace CategoryTheory.InternalAbelianSheafModule
/-- The site is essentially small in the coefficient universe.
Source: the size hypothesis of the node (auxiliary; not a blueprint node).
Proof: shrink its object and arrow types into the coefficient universe using UnivLE;
the resulting small category is equivalent to the original category. -/
@[instance] theorem comparison_essentiallySmall
    {D : Type v} [Category.{w} D] [UnivLE.{max v w, u}] :
    EssentiallySmall.{u} D := by
  have : UnivLE.{v, u} := UnivLE.trans.{v, max v w, u}
  have : UnivLE.{w, u} := UnivLE.trans.{w, max v w, u}
  exact essentiallySmall_of_small_of_locallySmall D

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- Left tensor on abelian sheaves preserves the colimits used in relative tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: use closedness in sk-def-sfb-sheaf-tensor; left tensor is a left adjoint. -/
@[instance] theorem comparison_sheafTensorLeft (M : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  let _ : HasWeakSheafify J AddCommGrpCat.{u} := HasSheafify.isRightAdjoint
  exact (sfbSheafTensor_properties (A := AddCommGrpCat.{u}) J).2.2 M |>.1

/-- Right tensor on abelian sheaves preserves the colimits used in relative tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: conjugate left tensor by the symmetry of det-def-sfb-sheaf-tensor-structure. -/
@[instance] theorem comparison_sheafTensorRight (M : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

variable (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]

/-- Module objects have the coproducts used in direct-sum totalization.
Source: Stacks 03DA--03DB (auxiliary; not a blueprint node).
Proof: section module sheaves have small colimits by
situation-conventions. Transfer their universal property
through sectionModuleEquivalence: applying its inverse to a coproduct gives a
coproduct of the original internal modules by the equivalence's Hom bijections. -/
@[instance] theorem comparison_internalColimits :
    HasColimitsOfSize.{0, 0} (Mod (Sheaf J AddCommGrpCat.{u}) R) := by
  exact Adjunction.has_colimits_of_equivalence (sectionModuleEquivalence J R).functor

/-- The fixed sectionwise equivalence is additive on morphisms.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: its map is the original map on underlying abelian sheaves; addition of module
maps is computed on those underlying maps (prose-03-02). -/
@[instance] theorem comparison_additive : (sectionModuleEquivalence J R).functor.Additive := by
  have : HasBinaryProducts (Mod (Sheaf J AddCommGrpCat.{u}) R) :=
    Adjunction.hasLimitsOfShape_of_equivalence (sectionModuleEquivalence J R).functor
  exact Functor.additive_of_preserves_binary_products _

/-- Every pair of internal complexes admits its direct-sum total tensor.
Source: Stacks 012Z (auxiliary; not a blueprint node).
Proof: comparison_internalColimits supplies every coproduct indexed by p+q=n,
which is the defining HasMapBifunctor condition. -/
@[instance] theorem comparison_internalTotalExists
    (K L : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ) :
    K.HasMapBifunctor L (curriedTensor _) := by
  intro n
  exact (comparison_internalColimits J R).has_colimits_of_shape _ |>.has_colimit _

/-- The pure tensor in the coequalizer relative tensor, formed using the lax tensor
comparison of the inclusion of sheaves into presheaves, then the coequalizer projection.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def comparison_internalTmul
    (M N : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) : (M ⊗ N).X.obj.obj U :=
  ((Mod.tensorObjπ M N).hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X).app U)
      (x ⊗ₜ[ℤ] y))

/-- The pure tensor in the sectionwise sheaf tensor: apply the module-sheafification
unit to the balanced section tensor and the inverse canonical tensor comparison.
Source: Stacks 03EK and 0GMW (auxiliary; not a blueprint node). -/
noncomputable def comparison_sectionTmul
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U)
    ((((PresheafOfModules.sheafificationAdjunction (𝟙
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R)).obj)).unit.app (M.val ⊗ N.val)).app U)
      (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))

private noncomputable instance comparison_closed : MonoidalClosed (Sheaf J AddCommGrpCat.{u}) :=
  (sfbSheafTensor_properties.{v, w, u + 1, u, 0, 0}
    (A := AddCommGrpCat.{u}) J).2.1.some

attribute [local irreducible] comparison_closed

set_option hygiene false in
local notation "E" => sectionModuleFunctor J R
set_option hygiene false in
local notation "IM" => Mod (Sheaf J AddCommGrpCat.{u}) R
set_option hygiene false in
local notation "SM" => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R))
private instance comparison_EAdditive : (E).Additive := comparison_additive J R

private instance comparison_EEquiv : (E).IsEquivalence := by
  change (sectionModuleEquivalence J R).functor.IsEquivalence
  infer_instance

private noncomputable def comparison_tensorIso (M N : IM) :
    (E).obj (M ⊗ N) ≅ (E).obj M ⊗ (E).obj N :=
  (exists_sectionTensorIso J R M N).choose ≪≫
    (SheafOfModules.tensorObjIsoSheafification ((E).obj M) ((E).obj N)).symm

-- Compare the concrete tensor pairings only once, before using their opaque API.
private theorem comparison_tensorIso_tmul (M N : IM) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((comparison_tensorIso J R M N).hom.val.app U) (comparison_internalTmul J R M N U x y) =
      comparison_sectionTmul J R ((E).obj M) ((E).obj N) U x y := by
  exact congrArg
    ((SheafOfModules.tensorObjIsoSheafification ((E).obj M) ((E).obj N)).inv.val.app U)
    ((exists_sectionTensorIso J R M N).choose_spec U x y)

attribute [local irreducible] comparison_tensorIso

private noncomputable abbrev comparison_inclusion : SM ⥤
    PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R)).obj :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)

@[reducible]
private noncomputable instance comparison_inclusionLax :
    (comparison_inclusion J R).LaxMonoidal :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 _)).rightAdjointLaxMonoidal

private noncomputable instance comparison_inclusionBraided :
    (comparison_inclusion J R).LaxBraided := by
  letI : (comparison_inclusion J R).LaxMonoidal :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).rightAdjointLaxMonoidal
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).rightAdjointLaxBraided

-- Identify the concrete sheafification pairing with the adjunction tensorator once.
private theorem comparison_sectionTmul_eq (M N : SM) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    comparison_sectionTmul J R M N U x y =
      ((Functor.LaxMonoidal.μ (comparison_inclusion J R) M N).app U)
        (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y) := rfl

private theorem comparison_inclusion_ε :
    Functor.LaxMonoidal.ε (comparison_inclusion J R) =
      𝟙 (𝟙_ (PresheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R)).obj)) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R)) (𝟙 _)
  have h : Functor.OplaxMonoidal.η (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R))
      (𝟙 _)) = adj.counit.app (𝟙_ SM) := rfl
  change adj.homEquiv _ _ (Functor.OplaxMonoidal.η _) = _
  rw [h, Adjunction.homEquiv_unit]
  exact adj.right_triangle_components (𝟙_ SM)

attribute [local irreducible] comparison_sectionTmul

private theorem comparison_sectionTmul_natural
    {M M' N N' : SM} (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    ((f ⊗ₘ g).val.app U) (comparison_sectionTmul J R M N U x y) =
      comparison_sectionTmul J R M' N' U ((f.val.app U) x) ((g.val.app U) y) := by
  simp only [comparison_sectionTmul_eq]
  exact congrArg (fun k ↦ (k.app U) (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))
    (Functor.LaxMonoidal.μ_natural (comparison_inclusion J R) f g).symm

private theorem comparison_sectionTmul_assoc
    (M N P : SM) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U) :
    ((α_ M N P).hom.val.app U)
        (comparison_sectionTmul J R (M ⊗ N) P U (comparison_sectionTmul J R M N U x y) z) =
      comparison_sectionTmul J R M (N ⊗ P) U x (comparison_sectionTmul J R N P U y z) := by
  simp only [comparison_sectionTmul_eq]
  exact congrArg (fun k ↦ (k.app U)
      ((x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y) ⊗ₜ[(sectionRingSheaf J R).obj.obj U] z))
    (Functor.LaxMonoidal.associativity (comparison_inclusion J R) M N P)

private theorem comparison_sectionTmul_braiding
    (M N : SM) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((β_ M N).hom.val.app U) (comparison_sectionTmul J R M N U x y) =
      comparison_sectionTmul J R N M U y x := by
  simp only [comparison_sectionTmul_eq]
  exact congrArg (fun k ↦ (k.app U) (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))
    (Functor.LaxBraided.braided (F := comparison_inclusion J R) M N)

private theorem comparison_internalTmul_natural
    {M M' N N' : IM} (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    (((E).map (f ⊗ₘ g)).val.app U) (comparison_internalTmul J R M N U x y) =
      comparison_internalTmul J R M' N' U (((E).map f).val.app U x)
        (((E).map g).val.app U y) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h : Mod.tensorObjπ M N ≫ (f ⊗ₘ g).hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.tensorObjπ M' N' := by
    have hf := congrArg (fun k : M ⊗ N ⟶ M' ⊗ N' ↦ Mod.tensorObjπ M N ≫ k.hom)
      (MonoidalCategory.tensorHom_def f g)
    refine hf.trans ?_
    change Mod.tensorObjπ M N ≫ (f ▷ N).hom ≫ (M' ◁ g).hom = _
    rw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
    rfl
  have hn := Functor.LaxMonoidal.μ_natural F f.hom g.hom
  have ht : Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫
      F.map (f ⊗ₘ g).hom =
        (F.map f.hom ⊗ₘ F.map g.hom) ≫
          Functor.LaxMonoidal.μ F M'.X N'.X ≫ F.map (Mod.tensorObjπ M' N') := by
    rw [← F.map_comp, h, F.map_comp, ← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun k ↦ (k.app U).hom (x ⊗ₜ[ℤ] y)) ht

private theorem comparison_internalTmul_assoc (M N P : IM) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) (z : P.X.obj.obj U) :
    (((E).map (α_ M N P).hom).val.app U)
        (comparison_internalTmul J R (M ⊗ N) P U
          (comparison_internalTmul J R M N U x y) z) =
      comparison_internalTmul J R M (N ⊗ P) U x
        (comparison_internalTmul J R N P U y z) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h := congrArg (fun k ↦
      Functor.LaxMonoidal.μ F M.X N.X ▷ F.obj P.X ≫
        Functor.LaxMonoidal.μ F (M.X ⊗ N.X) P.X ≫ F.map k)
    (Mod.tensorObjπ_associator_hom M N P)
  simp only [Functor.map_comp] at h
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.associativity_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc] at h
  exact congrArg (fun k ↦ (k.app U).hom ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)) h

private theorem comparison_internalTmul_braiding (M N : IM) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    (((E).map (β_ M N).hom).val.app U) (comparison_internalTmul J R M N U x y) =
      comparison_internalTmul J R N M U y x := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h : Mod.tensorObjπ M N ≫ (β_ M N).hom.hom =
      (β_ M.X N.X).hom ≫ Mod.tensorObjπ N M :=
    Mod.tensorObjπ_braidingHomX M N
  have ht := congrArg (fun k ↦ Functor.LaxMonoidal.μ F M.X N.X ≫ F.map k) h
  simp only [Functor.map_comp] at ht
  rw [Functor.LaxBraided.braided_assoc] at ht
  exact congrArg (fun k ↦ (k.app U).hom (x ⊗ₜ[ℤ] y)) ht

omit [HasSheafify J AddCommGrpCat.{u}] in
private theorem comparison_sheafTensor_mem (M N : Sheaf J AddCommGrpCat.{u}) :
    J.W (Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N) := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let φ := Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u}) M.obj N.obj ≫
    (adj.counit.app M ⊗ₘ adj.counit.app N)
  have : IsIso φ := by dsimp [φ]; infer_instance
  change J.W (adj.homEquiv _ _ φ)
  rw [Adjunction.homEquiv_unit]
  exact J.W.comp_mem _ _ (J.W_adj_unit_app adj _) (J.W.of_isIso _)

omit [HasSheafify J AddCommGrpCat.{u}] in
private theorem comparison_sheafTriple_hom_ext
    (M N P Q : Sheaf J AddCommGrpCat.{u}) {f g : (M ⊗ N) ⊗ P ⟶ Q}
    (h : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N ▷ P.obj ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) (M ⊗ N) P ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map f =
      Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N ▷ P.obj ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) (M ⊗ N) P ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map g) : f = g := by
  apply Sheaf.tensor_hom_ext
  exact ((J.W.whiskerRight_mem _ (comparison_sheafTensor_mem J M N) P.obj) Q.obj
    Q.property).injective h

-- The triple test involves the two successive relative tensor coequalizers.
private theorem comparison_internalTriple_hom_ext (M N P : IM) {Q : SM}
    {f g : (E).obj ((M ⊗ N) ⊗ P) ⟶ Q}
    (h : ∀ (U : Cᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U) (z : P.X.obj.obj U),
      (f.val.app U) (comparison_internalTmul J R (M ⊗ N) P U
          (comparison_internalTmul J R M N U x y) z) =
        (g.val.app U) (comparison_internalTmul J R (M ⊗ N) P U
          (comparison_internalTmul J R M N U x y) z)) : f = g := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi (Mod.tensorObjπ (M ⊗ N) P)).mp
  apply (cancel_epi (Mod.tensorObjπ M N ▷ P.X)).mp
  apply comparison_sheafTriple_hom_ext J M.X N.X P.X
  simp only [Functor.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc]
  ext U t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul t z =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul x y => exact h U x y z

private theorem comparison_internalTensor_hom_ext (M N : IM) {P : SM}
    {f g : (E).obj (M ⊗ N) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (f.val.app U) (comparison_internalTmul J R M N U x y) =
        (g.val.app U) (comparison_internalTmul J R M N U x y)) : f = g := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi (Mod.tensorObjπ M N)).mp
  apply Sheaf.tensor_hom_ext
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add z z' hz hz' => simp only [map_add, hz, hz']

private theorem comparison_tensorIso_natural
    (M M' N N' : IM) (f : M ⟶ M') (g : N ⟶ N') :
    (E).map (f ⊗ₘ g) ≫ (comparison_tensorIso J R M' N').hom =
      (comparison_tensorIso J R M N).hom ≫ ((E).map f ⊗ₘ (E).map g) := by
  apply comparison_internalTensor_hom_ext J R M N
  intro U x y
  change ((comparison_tensorIso J R M' N').hom.val.app U)
      (((E).map (f ⊗ₘ g)).val.app U (comparison_internalTmul J R M N U x y)) =
    (((E).map f ⊗ₘ (E).map g).val.app U)
      ((comparison_tensorIso J R M N).hom.val.app U (comparison_internalTmul J R M N U x y))
  rw [comparison_internalTmul_natural, comparison_tensorIso_tmul,
    comparison_tensorIso_tmul, comparison_sectionTmul_natural]

private theorem comparison_tensorIso_assoc (M N P : IM) :
    (comparison_tensorIso J R (M ⊗ N) P).hom ≫
        (comparison_tensorIso J R M N).hom ▷ (E).obj P ≫ (α_ _ _ _).hom =
      (E).map (α_ M N P).hom ≫ (comparison_tensorIso J R M (N ⊗ P)).hom ≫
        (E).obj M ◁ (comparison_tensorIso J R N P).hom := by
  apply comparison_internalTriple_hom_ext J R M N P
  intro U x y z
  change ((α_ ((E).obj M) ((E).obj N) ((E).obj P)).hom.val.app U)
      ((((comparison_tensorIso J R M N).hom ▷ (E).obj P).val.app U)
        ((comparison_tensorIso J R (M ⊗ N) P).hom.val.app U
          (comparison_internalTmul J R (M ⊗ N) P U
            (comparison_internalTmul J R M N U x y) z))) =
    (((E).obj M ◁ (comparison_tensorIso J R N P).hom).val.app U)
      ((comparison_tensorIso J R M (N ⊗ P)).hom.val.app U
        (((E).map (α_ M N P).hom).val.app U
          (comparison_internalTmul J R (M ⊗ N) P U
            (comparison_internalTmul J R M N U x y) z)))
  simp only [comparison_tensorIso_tmul, ← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.id_tensorHom,
    comparison_sectionTmul_natural, comparison_internalTmul_assoc,
    comparison_sectionTmul_assoc]
  rfl

private theorem comparison_tensorIso_braiding (M N : IM) :
    (comparison_tensorIso J R M N).hom ≫ (β_ _ _).hom =
      (E).map (β_ M N).hom ≫ (comparison_tensorIso J R N M).hom := by
  apply comparison_internalTensor_hom_ext J R M N
  intro U x y
  change ((β_ ((E).obj M) ((E).obj N)).hom.val.app U)
      ((comparison_tensorIso J R M N).hom.val.app U (comparison_internalTmul J R M N U x y)) =
    (comparison_tensorIso J R N M).hom.val.app U
      (((E).map (β_ M N).hom).val.app U (comparison_internalTmul J R M N U x y))
  rw [comparison_internalTmul_braiding, comparison_tensorIso_tmul,
    comparison_tensorIso_tmul, comparison_sectionTmul_braiding]

private noncomputable def comparison_unitIso : (E).obj (𝟙_ IM) ≅ 𝟙_ SM := by
  let i : ((E).obj (𝟙_ IM)).val ≅ (𝟙_ SM).val :=
    PresheafOfModules.isoMk
      (fun _ ↦ ModuleCat.isoMk (Iso.refl _) (by intro r; ext x; rfl))
      (by intro U V f; rfl)
  exact
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }

private theorem comparison_unitIso_apply (U : Cᵒᵖ) (r : R.obj.obj U) :
    ((comparison_unitIso J R).hom.val.app U) r = r := rfl

attribute [local irreducible] comparison_unitIso

private theorem comparison_sectionTmul_leftUnitor
    (M : SM) (U : Cᵒᵖ) (r : (sectionRingSheaf J R).obj.obj U) (x : M.val.obj U) :
    ((λ_ M).hom.val.app U) (comparison_sectionTmul J R (𝟙_ SM) M U r x) = r • x := by
  rw [comparison_sectionTmul_eq]
  have h := Functor.LaxMonoidal.left_unitality (comparison_inclusion J R) M
  rw [comparison_inclusion_ε, id_whiskerRight, Category.id_comp] at h
  exact congrArg (fun k ↦ (k.app U) (r ⊗ₜ[(sectionRingSheaf J R).obj.obj U] x)) h.symm

private theorem comparison_sectionTmul_rightUnitor
    (M : SM) (U : Cᵒᵖ) (x : M.val.obj U) (r : (sectionRingSheaf J R).obj.obj U) :
    ((ρ_ M).hom.val.app U) (comparison_sectionTmul J R M (𝟙_ SM) U x r) = r • x := by
  rw [comparison_sectionTmul_eq]
  have h := Functor.LaxMonoidal.right_unitality (comparison_inclusion J R) M
  rw [comparison_inclusion_ε, whiskerLeft_id, Category.id_comp] at h
  exact congrArg (fun k ↦ (k.app U) (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] r)) h.symm

private theorem comparison_internal_leftUnitorπ (M : IM) :
    Mod.tensorObjπ (𝟙_ IM) M ≫ (λ_ M).hom.hom = Mod.act (A := R) M.X := by
  change Mod.tensorObjπ (𝟙_ IM) M ≫
      (Bimod.whiskerRight (Mod.toBimodRegularIso (R := R)).hom
        ((Mod.toBimod R).obj M)).hom ≫
      Bimod.LeftUnitorBimod.hom ((Mod.toBimod R).obj M) = _
  dsimp only [Mod.tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one, Mod.toBimodRegularIso_hom_hom,
    id_whiskerRight]
  dsimp only [Bimod.LeftUnitorBimod.hom]
  erw [Category.id_comp, coequalizer.π_desc]
  rfl

private theorem comparison_internal_rightUnitorπ (M : IM) :
    Mod.tensorObjπ M (𝟙_ IM) ≫ (ρ_ M).hom.hom =
      (β_ M.X R).hom ≫ Mod.act (A := R) M.X := by
  change Mod.tensorObjπ M (𝟙_ IM) ≫
      (Bimod.whiskerLeft ((Mod.toBimod R).obj M)
        (Mod.toBimodRegularIso (R := R)).hom).hom ≫
      Bimod.RightUnitorBimod.hom ((Mod.toBimod R).obj M) = _
  dsimp only [Mod.tensorObjπ]
  rw [Bimod.whiskerLeft_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one, Mod.toBimodRegularIso_hom_hom,
    whiskerLeft_id]
  dsimp only [Bimod.RightUnitorBimod.hom]
  erw [Category.id_comp, coequalizer.π_desc]
  rfl

private theorem comparison_internalTmul_leftUnitor (M : IM) (U : Cᵒᵖ)
    (r : R.obj.obj U) (x : M.X.obj.obj U) :
    (((E).map (λ_ M).hom).val.app U)
        (comparison_internalTmul J R (𝟙_ IM) M U r x) =
      (show ((E).obj M).val.obj U from
        (show (sectionRingSheaf J R).obj.obj U from r) •
          (show ((E).obj M).val.obj U from x)) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ F R M.X ≫ F.map k)
    (comparison_internal_leftUnitorπ J R M)
  simp only [Functor.map_comp] at h
  exact congrArg (fun k ↦ (k.app U).hom (r ⊗ₜ[ℤ] x)) h

private theorem comparison_internalTmul_rightUnitor (M : IM) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (r : R.obj.obj U) :
    (((E).map (ρ_ M).hom).val.app U)
        (comparison_internalTmul J R M (𝟙_ IM) U x r) =
      (show ((E).obj M).val.obj U from
        (show (sectionRingSheaf J R).obj.obj U from r) •
          (show ((E).obj M).val.obj U from x)) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ F M.X R ≫ F.map k)
    (comparison_internal_rightUnitorπ J R M)
  simp only [Functor.map_comp] at h
  rw [Functor.LaxBraided.braided_assoc] at h
  exact congrArg (fun k ↦ (k.app U).hom (x ⊗ₜ[ℤ] r)) h

private theorem comparison_tensorIso_leftUnitor (M : IM) :
    (comparison_tensorIso J R (𝟙_ IM) M).hom ≫
        (comparison_unitIso J R).hom ▷ (E).obj M ≫ (λ_ _).hom =
      (E).map (λ_ M).hom := by
  apply comparison_internalTensor_hom_ext J R (𝟙_ IM) M
  intro U r x
  change ((λ_ ((E).obj M)).hom.val.app U)
      ((((comparison_unitIso J R).hom ▷ (E).obj M).val.app U)
        ((comparison_tensorIso J R (𝟙_ IM) M).hom.val.app U
          (comparison_internalTmul J R (𝟙_ IM) M U r x))) = _
  simp only [comparison_tensorIso_tmul, ← MonoidalCategory.tensorHom_id,
    comparison_sectionTmul_natural,
    comparison_unitIso_apply]
  exact comparison_sectionTmul_leftUnitor J R ((E).obj M) U r x |>.trans
    (comparison_internalTmul_leftUnitor J R M U r x).symm

private theorem comparison_tensorIso_rightUnitor (M : IM) :
    (comparison_tensorIso J R M (𝟙_ IM)).hom ≫
        (E).obj M ◁ (comparison_unitIso J R).hom ≫ (ρ_ _).hom =
      (E).map (ρ_ M).hom := by
  apply comparison_internalTensor_hom_ext J R M (𝟙_ IM)
  intro U x r
  change ((ρ_ ((E).obj M)).hom.val.app U)
      ((((E).obj M ◁ (comparison_unitIso J R).hom).val.app U)
        ((comparison_tensorIso J R M (𝟙_ IM)).hom.val.app U
          (comparison_internalTmul J R M (𝟙_ IM) U x r))) = _
  simp only [comparison_tensorIso_tmul, ← MonoidalCategory.id_tensorHom,
    comparison_sectionTmul_natural,
    comparison_unitIso_apply]
  exact comparison_sectionTmul_rightUnitor J R ((E).obj M) U x r |>.trans
    (comparison_internalTmul_rightUnitor J R M U x r).symm

private theorem comparison_acyclic
    (K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ) :
    K.Acyclic ↔ (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic := by
  exact forall_congr' fun n ↦
    ((K.sc n).exact_map_iff_of_faithful (sectionModuleEquivalence J R).functor).symm

omit [UnivLE.{max v w, u}] in
private noncomputable def comparison_totalIso
    {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
    [MonoidalCategory D] [MonoidalCategory D']
    [MonoidalPreadditive D] [MonoidalPreadditive D']
    (F : D ⥤ D') [F.Additive]
    (e : ∀ M N : D, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (he : ∀ (M M' N N' : D) (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (K L : CochainComplex D ℤ)
    [CochainComplex.HasMapBifunctor K L (curriedTensor D)]
    [CochainComplex.HasMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D')]
    [F.PreservesTotalComplex
      ((((curriedTensor D).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L)
      (.up ℤ)] :
    (F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor K L (curriedTensor D)) ≅
      CochainComplex.mapBifunctor
        ((F.mapHomologicalComplex (.up ℤ)).obj K)
        ((F.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D') := by
  let B := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let b : (F.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj B ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj L) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (K.X p) (L.X q))
        (by
          intro q q' hq
          change (e (K.X p) (L.X q)).hom ≫ F.obj (K.X p) ◁ F.map (L.d q q') =
            F.map (K.X p ◁ L.d q q') ≫ (e (K.X p) (L.X q')).hom
          simpa only [Functor.map_id, MonoidalCategory.id_tensorHom] using
            (he (K.X p) (K.X p) (L.X q) (L.X q') (𝟙 _) (L.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (K.X p) (L.X q)).hom ≫ F.map (K.d p p') ▷ F.obj (L.X q) =
          F.map (K.d p p' ▷ L.X q) ≫ (e (K.X p') (L.X q)).hom
        simpa only [Functor.map_id, MonoidalCategory.tensorHom_id] using
          (he (K.X p) (K.X p') (L.X q) (L.X q) (K.d p p') (𝟙 _)).symm)
  exact (HomologicalComplex₂.mapTotalIso F B (.up ℤ)).symm ≪≫
    HomologicalComplex₂.total.mapIso b (.up ℤ)


omit [UnivLE.{max v w, u}] in
private theorem comparison_totalIso_ι
    {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
    [MonoidalCategory D] [MonoidalCategory D']
    [MonoidalPreadditive D] [MonoidalPreadditive D']
    (F : D ⥤ D') [F.Additive]
    (e : ∀ M N : D, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (he : ∀ (M M' N N' : D) (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (K L : CochainComplex D ℤ)
    [CochainComplex.HasMapBifunctor K L (curriedTensor D)]
    [CochainComplex.HasMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D')]
    [F.PreservesTotalComplex
      ((((curriedTensor D).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L)
      (.up ℤ)]
    (p q n : ℤ) (h : p + q = n) :
    F.map (CochainComplex.ιMapBifunctor K L (curriedTensor D) p q n h) ≫
      (comparison_totalIso F e he K L).hom.f n =
      (e (K.X p) (L.X q)).hom ≫
        CochainComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D') p q n h := by
  simp [comparison_totalIso, HomologicalComplex₂.mapTotalIso,
    CochainComplex.ιMapBifunctor, HomologicalComplex.ιMapBifunctor]

local instance comparison_presheafCoproducts (I : Type u) :
    HasColimitsOfShape (Discrete I) (PresheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R)).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

private theorem comparison_kflat (K : CochainComplex IM ℤ) :
    (∀ A : CochainComplex IM ℤ,
      A.Acyclic → (CochainComplex.mapBifunctor A K (curriedTensor _)).Acyclic) ↔
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((E).mapHomologicalComplex (.up ℤ)).obj K) := by
  let e := (sectionModuleEquivalence J R).mapHomologicalComplex (.up ℤ)
  let T := (curriedTensor SM).map₂CochainComplex
  constructor
  · intro h
    change ∀ B : CochainComplex SM ℤ, B.Acyclic → _
    intro B hB
    let A := e.inverse.obj B
    let i : e.functor.obj A ≅ B := e.counitIso.app B
    have ha : A.Acyclic := (comparison_acyclic J R A).mpr (fun n ↦
      (hB n).of_iso i.symm)
    have ht := (comparison_acyclic J R _).mp (h A ha)
    let j := comparison_totalIso (E) (comparison_tensorIso J R)
      (comparison_tensorIso_natural J R) A K
    let k := ((T.mapIso i).app (e.functor.obj K))
    intro n
    exact ((ht n).of_iso j).of_iso k
  · intro h A hA
    change ∀ B : CochainComplex SM ℤ, B.Acyclic → _ at h
    have ht := h (((E).mapHomologicalComplex (.up ℤ)).obj A)
      ((comparison_acyclic J R A).mp hA)
    let j := comparison_totalIso (E) (comparison_tensorIso J R)
      (comparison_tensorIso_natural J R) A K
    exact (comparison_acyclic J R _).mpr (fun n ↦ (ht n).of_iso j.symm)

private theorem comparison_flat (M : IM) :
    exactFunctor _ _ (tensorRight M) ↔ SheafOfModules.IsFlatOnSite ((E).obj M) := by
  constructor
  · intro h
    apply (flat_iff_sectionModule J R M).mp
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight M).symm h, h⟩
  · intro h
    exact ((flat_iff_sectionModule J R M).mpr h).2

/-- The fixed internal-to-sectionwise equivalence is exact, symmetric monoidal with
its tensor comparison pinned on local pure tensors, and identifies the unbounded
sum-total tensors, acyclicity, flatness and K-flatness.

Source: Stacks Project, Modules on Sites, Tags 03EK, 0GMW and 03ER; Cohomology on
Sites, Definition 06YN (auxiliary; not a blueprint node).

Proof:
The fixed equivalence preserves finite limits and colimits. The normalized tensor
isomorphism comes from exists_sectionTensorIso, followed by the inverse of
SheafOfModules.tensorObjIsoSheafification. Both maps come from the balanced
pairing and sheafification universal properties, so the displayed pure tensors
are fixed. Naturality and coherence follow from tensor induction after cancelling
the coequalizer projections and sheafification comparisons. The unit comparison
is the identity on sections, and the unitors are the action maps.

The tensor comparisons give an isomorphism of tensor bicomplexes. Compose its
totalization with the inverse additive mapTotalIso; the coproduct injection
formulas give the asserted summand equation, including the differential signs.
Exactness of the short complexes in each degree is preserved and reflected by
the exact faithful equivalence. Flatness follows from flat_iff_sectionModule and
symmetry. For K-flatness transport every acyclic test using the termwise inverse
equivalence and its counit, then use the total-complex and acyclicity comparisons.
The argument applies to zero rings, empty sites and unbounded complexes.
-/
theorem internal_section_tensor_comparison :
    exactFunctor _ _ (sectionModuleEquivalence J R).functor ∧
    ∃ e : ∀ M N : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (sectionModuleEquivalence J R).functor.obj (M ⊗ N) ≅
        (sectionModuleEquivalence J R).functor.obj M ⊗
          (sectionModuleEquivalence J R).functor.obj N,
    ∃ e₀ : (sectionModuleEquivalence J R).functor.obj
        (𝟙_ (Mod (Sheaf J AddCommGrpCat.{u}) R)) ≅
      𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R))),
    (∀ (M N : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
        (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      ((e M N).hom.val.app U) (comparison_internalTmul J R M N U x y) =
        comparison_sectionTmul J R
          ((sectionModuleEquivalence J R).functor.obj M)
          ((sectionModuleEquivalence J R).functor.obj N) U x y) ∧
    (∀ (U : Cᵒᵖ) (r : R.obj.obj U), (e₀.hom.val.app U) r = r) ∧
    (∀ (M M' N N' : Mod (Sheaf J AddCommGrpCat.{u}) R) (f : M ⟶ M') (g : N ⟶ N'),
      (sectionModuleEquivalence J R).functor.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ ((sectionModuleEquivalence J R).functor.map f ⊗ₘ
          (sectionModuleEquivalence J R).functor.map g)) ∧
    (∀ M N P : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e (M ⊗ N) P).hom ≫
          (e M N).hom ▷ (sectionModuleEquivalence J R).functor.obj P ≫
          (α_ _ _ _).hom =
        (sectionModuleEquivalence J R).functor.map (α_ M N P).hom ≫
          (e M (N ⊗ P)).hom ≫
          (sectionModuleEquivalence J R).functor.obj M ◁ (e N P).hom) ∧
    (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e (𝟙_ _) M).hom ≫ e₀.hom ▷
          (sectionModuleEquivalence J R).functor.obj M ≫ (λ_ _).hom =
        (sectionModuleEquivalence J R).functor.map (λ_ M).hom) ∧
    (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e M (𝟙_ _)).hom ≫ (sectionModuleEquivalence J R).functor.obj M ◁
          e₀.hom ≫ (ρ_ _).hom =
        (sectionModuleEquivalence J R).functor.map (ρ_ M).hom) ∧
    (∀ M N : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e M N).hom ≫ (β_ _ _).hom =
        (sectionModuleEquivalence J R).functor.map (β_ M N).hom ≫ (e N M).hom) ∧
    (∀ K L : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
      ∃ t : ((sectionModuleEquivalence J R).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (CochainComplex.mapBifunctor K L (curriedTensor _)) ≅
        CochainComplex.mapBifunctor
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) (curriedTensor _),
      ∀ (p q n : ℤ) (h : p + q = n),
        (sectionModuleEquivalence J R).functor.map
            (CochainComplex.ιMapBifunctor K L (curriedTensor _) p q n h) ≫ t.hom.f n =
          (e (K.X p) (L.X q)).hom ≫ CochainComplex.ιMapBifunctor
            (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)
            (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L) (curriedTensor _) p q n h) ∧
    (∀ K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
      K.Acyclic ↔ (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic) ∧
    (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      exactFunctor _ _ (tensorRight M) ↔
        SheafOfModules.IsFlatOnSite ((sectionModuleEquivalence J R).functor.obj M)) ∧
    (∀ K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
      (∀ A : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
        A.Acyclic → (CochainComplex.mapBifunctor A K (curriedTensor _)).Acyclic) ↔
      CochainComplex.IsKFlatIndependentCoefficients
        (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) := by
  constructor
  · exact (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩
  refine ⟨comparison_tensorIso J R, ?_⟩
  refine ⟨comparison_unitIso J R, ?_⟩
  refine ⟨comparison_tensorIso_tmul J R, comparison_unitIso_apply J R,
    comparison_tensorIso_natural J R, comparison_tensorIso_assoc J R,
    comparison_tensorIso_leftUnitor J R, comparison_tensorIso_rightUnitor J R,
    comparison_tensorIso_braiding J R, ?_, comparison_acyclic J R, comparison_flat J R,
    comparison_kflat J R⟩
  · intro K L
    exact ⟨comparison_totalIso (E) (comparison_tensorIso J R)
      (comparison_tensorIso_natural J R) K L, comparison_totalIso_ι (E) (comparison_tensorIso J R)
        (comparison_tensorIso_natural J R) K L⟩

end CategoryTheory.InternalAbelianSheafModule
