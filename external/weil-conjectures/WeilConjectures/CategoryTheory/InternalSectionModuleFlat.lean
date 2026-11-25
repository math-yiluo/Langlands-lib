/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Flatness under the internal/section module equivalence

The tensor comparison is constructed explicitly using the two universal properties.
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
namespace CategoryTheory.InternalAbelianSheafModule
set_option backward.isDefEq.respectTransparency false
private noncomputable def restrictIdIso
    {C : Type v} [Category.{w} C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    𝟭 (PresheafOfModules.{u} R) ≅ PresheafOfModules.restrictScalars (𝟙 R) := Iso.refl _
private noncomputable def moduleSheafLift
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J RingCat.{u}) (P : PresheafOfModules.{u} R.obj)
    (M : SheafOfModules.{u} R) (p : P ⟶ M.val) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj P ⟶ M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (p ≫ (restrictIdIso R.obj).hom.app M.val)
private theorem moduleSheafLift_unit
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J RingCat.{u}) (P : PresheafOfModules.{u} R.obj)
    (M : SheafOfModules.{u} R) (p : P ⟶ M.val) :
    toSheafify J P.presheaf ≫ (sheafToPresheaf J AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf R).map (moduleSheafLift R P M p)) =
      (PresheafOfModules.toPresheaf R.obj).map p := by
  exact congrArg ((PresheafOfModules.toPresheaf R.obj).map)
    ((PresheafOfModules.sheafificationHomEquiv
      (P := P) (F := M) (𝟙 R.obj)).apply_symm_apply p)

private theorem sheafificationLift_naturality
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf J RingCat.{u}}
    {P Q : PresheafOfModules.{u} R.obj} {M N : SheafOfModules.{u} R}
    (f : P ⟶ Q) (g : M ⟶ N)
    (p : P ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val)
    (q : Q ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj N.val)
    (h : f ≫ q = p ≫ (PresheafOfModules.restrictScalars (𝟙 R.obj)).map g.val) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map f ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm q =
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm p ≫ g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  have heP : adj.homEquiv P M =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) :=
    Equiv.ext (fun t ↦ PresheafOfModules.sheafificationAdjunction_homEquiv_apply (𝟙 R.obj) t)
  have heQ : adj.homEquiv Q N =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) :=
    Equiv.ext (fun t ↦ PresheafOfModules.sheafificationAdjunction_homEquiv_apply (𝟙 R.obj) t)
  have hn := adj.homEquiv_naturality_right_square f q p g h
  rw [heP, heQ] at hn
  exact hn

private theorem moduleSheafLift_naturality
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf J RingCat.{u}}
    {P Q : PresheafOfModules.{u} R.obj} {M N : SheafOfModules.{u} R}
    (f : P ⟶ Q) (g : M ⟶ N) (p : P ⟶ M.val) (q : Q ⟶ N.val)
    (h : f ≫ q = p ≫ g.val) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map f ≫ moduleSheafLift R Q N q =
      moduleSheafLift R P M p ≫ g := by
  apply sheafificationLift_naturality (M := M) (N := N) f g
  rw [← Category.assoc, h]
  simpa only [Functor.id_map, Category.assoc] using
    congrArg (fun z ↦ p ≫ z) ((restrictIdIso R.obj).hom.naturality g.val)
attribute [irreducible] moduleSheafLift restrictIdIso

private theorem sheafification_hom_ext
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (M : Sheaf J AddCommGrpCat.{u})
    {f g : (presheafToSheaf J AddCommGrpCat.{u}).obj P ⟶ M}
    (h : toSheafify J P ≫ (sheafToPresheaf J AddCommGrpCat.{u}).map f =
      toSheafify J P ≫ (sheafToPresheaf J AddCommGrpCat.{u}).map g) : f = g := by
  apply ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv P M).injective
  simpa only [Adjunction.homEquiv_unit] using h

private theorem tensorAddHom_ext {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] {f g : TensorProduct ℤ M N →+ P}
    (h : ∀ m n, f (m ⊗ₜ[ℤ] n) = g (m ⊗ₜ[ℤ] n)) : f = g := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add z w hz hw => simp only [map_add, hz, hw]

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory Sheaf.symmetricCategory
variable [HasCoequalizers (Sheaf J AddCommGrpCat.{u})]
  [MonoidalClosed (Sheaf J AddCommGrpCat.{u})]
variable (R : Sheaf (J) AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]

private noncomputable def tensorPair (M N : Mod (Sheaf (J) AddCommGrpCat.{u}) R) :
    ((sheafToPresheaf (J) AddCommGrpCat.{u}).obj M.X ⊗
      (sheafToPresheaf (J) AddCommGrpCat.{u}).obj N.X) ⟶
      (sheafToPresheaf (J) AddCommGrpCat.{u}).obj (M ⊗ N).X :=
  Functor.LaxMonoidal.μ (sheafToPresheaf (J) AddCommGrpCat.{u}) M.X N.X ≫
    (sheafToPresheaf (J) AddCommGrpCat.{u}).map (Mod.tensorObjπ M N)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem tensorPair_balance (M N : Mod (Sheaf (J) AddCommGrpCat.{u}) R)
    (U : Cᵒᵖ) (r : (sectionRingSheaf.{u, v, w} (J) R).obj.obj U)
    (m : ((sectionModuleFunctor.{u, v, w} (J) R).obj M).val.obj U)
    (n : ((sectionModuleFunctor.{u, v, w} (J) R).obj N).val.obj U) :
    ((tensorPair J R M N).app U).hom ((r • m) ⊗ₜ[ℤ] n) =
      ((tensorPair J R M N).app U).hom (m ⊗ₜ[ℤ] (r • n)) := by
  have h := Mod.tensorObjπ_condition (R := R) M N
  let F := sheafToPresheaf (J) AddCommGrpCat.{u}
  have h' := congrArg (fun f ↦
    Functor.LaxMonoidal.μ F M.X R ▷ F.obj N.X ≫
    Functor.LaxMonoidal.μ F (M.X ⊗ R) N.X ≫ F.map f) h
  simp only [Functor.map_comp, Category.assoc] at h'
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc] at h'
  rw [← comp_whiskerRight_assoc] at h'
  rw [F.map_comp, Functor.LaxBraided.braided_assoc] at h'
  rw [Functor.LaxMonoidal.associativity_assoc] at h'
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc] at h'
  have he := congrArg (fun t ↦ (t.app U).hom ((m ⊗ₜ[ℤ] r) ⊗ₜ[ℤ] n)) h'
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply] at he
  exact he
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem tensorPair_smul (M N : Mod (Sheaf (J) AddCommGrpCat.{u}) R)
    (U : Cᵒᵖ) (r : (sectionRingSheaf.{u, v, w} (J) R).obj.obj U)
    (m : ((sectionModuleFunctor.{u, v, w} (J) R).obj M).val.obj U)
    (n : ((sectionModuleFunctor.{u, v, w} (J) R).obj N).val.obj U) :
    ((tensorPair J R M N).app U).hom ((r • m) ⊗ₜ[ℤ] n) =
      r • (show ((sectionModuleFunctor.{u, v, w} (J) R).obj (M ⊗ N)).val.obj U from
        ((tensorPair J R M N).app U).hom (m ⊗ₜ[ℤ] n)) := by
  have h := Mod.whiskerLeft_tensorπ_smul (R := R) M N
  let F := sheafToPresheaf (J) AddCommGrpCat.{u}
  have h' := congrArg (fun f ↦ F.obj R ◁ Functor.LaxMonoidal.μ F M.X N.X ≫
    Functor.LaxMonoidal.μ F R (M.X ⊗ N.X) ≫ F.map f) h
  simp only [Functor.map_comp] at h'
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc] at h'
  rw [Functor.LaxMonoidal.associativity_inv_assoc] at h'
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc] at h'
  have he := congrArg (fun t ↦ (t.app U).hom (r ⊗ₜ[ℤ] (m ⊗ₜ[ℤ] n))) h'
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply] at he
  exact he.symm
set_option hygiene false in
local notation "E" => sectionModuleFunctor.{u, v, w} J R
set_option hygiene false in
local notation "A" => (sectionRingSheaf.{u, v, w} J R).obj
set_option hygiene false in
local notation "IM" => Mod (Sheaf J AddCommGrpCat.{u}) R

private noncomputable def tensorPairLinear (M N : IM) (U : Cᵒᵖ) :
    ((E).obj M).val.obj U →ₗ[(A).obj U] ((E).obj N).val.obj U →ₗ[(A).obj U]
      ((E).obj (M ⊗ N)).val.obj U where
  toFun m :=
    { toFun := fun n ↦ ((tensorPair J R M N).app U).hom (m ⊗ₜ[ℤ] n)
      map_add' := by intros; simp only [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro r n
        rw [← tensorPair_balance J R M N U, tensorPair_smul J R M N U]
        rfl }
  map_add' := by
    intro m m'
    ext n
    change ((tensorPair J R M N).app U).hom ((m + m') ⊗ₜ[ℤ] n) = _
    simp only [TensorProduct.add_tmul, map_add]
    rfl
  map_smul' := by
    intro r m
    ext n
    exact tensorPair_smul J R M N U r m n

private noncomputable def sectionTensorToInternal (M N : IM) :
    SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val ⟶
      ((E).obj (M ⊗ N)).val where
  app U := ModuleCat.ofHom
    (X := (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val).obj U)
    (Y := ((E).obj (M ⊗ N)).val.obj U)
    (TensorProduct.lift (tensorPairLinear J R M N U))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    have h := congrArg (fun t ↦ t.hom (m ⊗ₜ[ℤ] n)) ((tensorPair J R M N).naturality f)
    exact h
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem sectionTensorToInternal_tmul (M N : IM) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((sectionTensorToInternal J R M N).app U).hom
        (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y) =
      ((Mod.tensorObjπ M N).hom.app U)
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X).app U)
          (x ⊗ₜ[ℤ] y)) := rfl

private noncomputable def sheafTensorLift
    (M N P : Sheaf J AddCommGrpCat.{u}) (p : M.obj ⊗ N.obj ⟶ P.obj) :
    M ⊗ N ⟶ P := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let φ := Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u}) M.obj N.obj ≫
    (adj.counit.app M ⊗ₘ adj.counit.app N)
  have : IsIso φ := by dsimp [φ]; infer_instance
  exact inv φ ≫ (adj.homEquiv _ _).symm p

omit [UnivLE.{max v w, u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoequalizers (Sheaf J AddCommGrpCat.{u})] [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem sheafTensorLift_spec
    (M N P : Sheaf J AddCommGrpCat.{u}) (p : M.obj ⊗ N.obj ⟶ P.obj) :
    Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map (sheafTensorLift J M N P p) = p := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let φ := Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u}) M.obj N.obj ≫
    (adj.counit.app M ⊗ₘ adj.counit.app N)
  have : IsIso φ := by dsimp [φ]; infer_instance
  have hμ : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N =
      adj.homEquiv _ _ φ := rfl
  change _ ≫ (sheafToPresheaf J AddCommGrpCat.{u}).map
    (inv φ ≫ (adj.homEquiv _ _).symm p) = _
  rw [hμ]
  erw [← adj.homEquiv_naturality_right]
  rw [IsIso.hom_inv_id_assoc]
  exact (adj.homEquiv _ _).apply_symm_apply p
private noncomputable abbrev sectionTensorSheaf (M N : IM) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, v, w} J R)) :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, v, w} J R)) (𝟙 _)).obj
      (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val)

private noncomputable def sheafTensorToInternal (M N : IM) :
    sectionTensorSheaf J R M N ⟶
      (E).obj (M ⊗ N) :=
  moduleSheafLift
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, v, w} J R))
    (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val)
    ((E).obj (M ⊗ N)) (sectionTensorToInternal J R M N)
private noncomputable def rawTensorQuotient (M N : IM) :
    M.X.obj ⊗ N.X.obj ⟶
      (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val).presheaf where
  app U := AddCommGrpCat.ofHom
    (TensorProduct.lift
      ((TensorProduct.mk ((A).obj U) (((E).obj M).val.obj U)
        (((E).obj N).val.obj U)).restrictScalars₁₂ ℤ ℤ)).toAddMonoidHom
  naturality {U V} f := by
    apply AddCommGrpCat.hom_ext
    apply tensorAddHom_ext
    intro m n
    rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoequalizers (Sheaf J AddCommGrpCat.{u})]
  [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem rawTensorQuotient_balance (M N : IM) :
    let F := sheafToPresheaf J AddCommGrpCat.{u}
    ((β_ (F.obj M.X) (F.obj R)).hom ≫
      Functor.LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X]) ▷ F.obj N.X ≫
      rawTensorQuotient J R M N =
    (α_ (F.obj M.X) (F.obj R) (F.obj N.X)).hom ≫
      F.obj M.X ◁ Functor.LaxMonoidal.μ F R N.X ≫ F.obj M.X ◁ F.map γ[R,N.X] ≫
      rawTensorQuotient J R M N := by
  dsimp only
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply tensorAddHom_ext
  intro t n
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [TensorProduct.add_tmul, map_add, ht, ht']
  | tmul m r =>
    exact TensorProduct.smul_tmul (R := (A).obj U)
      (show (A).obj U from r)
      (show ((E).obj M).val.obj U from m) (show ((E).obj N).val.obj U from n)

private noncomputable def sheafTensorUnderlyingPair (M N : IM) :
    M.X ⊗ N.X ⟶
      (SheafOfModules.toSheaf _).obj
        (sectionTensorSheaf J R M N) :=
  sheafTensorLift J M.X N.X _
    (rawTensorQuotient J R M N ≫ toSheafify J _)
omit [UnivLE.{max v w, u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoequalizers (Sheaf J AddCommGrpCat.{u})] [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem sheafTensorComparison_mem (M N : Sheaf J AddCommGrpCat.{u}) :
    (J).W (Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N) := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let φ := Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u}) M.obj N.obj ≫
    (adj.counit.app M ⊗ₘ adj.counit.app N)
  have : IsIso φ := by dsimp [φ]; infer_instance
  change (J).W (adj.homEquiv _ _ φ)
  rw [Adjunction.homEquiv_unit]
  exact (J).W.comp_mem _ _ ((J).W_adj_unit_app adj _) ((J).W.of_isIso _)

omit [UnivLE.{max v w, u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoequalizers (Sheaf J AddCommGrpCat.{u})] [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem sheafTriple_hom_ext
    (M N P Q : Sheaf J AddCommGrpCat.{u}) {f g : (M ⊗ N) ⊗ P ⟶ Q}
    (h : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N ▷ P.obj ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) (M ⊗ N) P ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map f =
      Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M N ▷ P.obj ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) (M ⊗ N) P ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map g) : f = g := by
  apply Sheaf.tensor_hom_ext
  exact (((J).W.whiskerRight_mem _ (sheafTensorComparison_mem J M N) P.obj) Q.obj
    Q.property).injective h
omit [HasCoequalizers (Sheaf J AddCommGrpCat.{u})]
  [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem sheafTensorUnderlyingPair_spec (M N : IM) :
    Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map
        (sheafTensorUnderlyingPair J R M N) =
      rawTensorQuotient J R M N ≫ toSheafify J _ :=
  sheafTensorLift_spec J M.X N.X _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem rawTensorQuotient_comp (M N : IM) :
    rawTensorQuotient J R M N ≫
      (PresheafOfModules.toPresheaf _).map (sectionTensorToInternal J R M N) =
      tensorPair J R M N := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply tensorAddHom_ext
  intro m n
  rfl

private theorem sheafTensorToInternal_unit (M N : IM) :
    toSheafify J
      (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val).presheaf ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf _).map (sheafTensorToInternal J R M N)) =
      (PresheafOfModules.toPresheaf _).map (sectionTensorToInternal J R M N) := by
  exact moduleSheafLift_unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, v, w} J R))
    (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val)
    ((E).obj (M ⊗ N)) (sectionTensorToInternal J R M N)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem sectionTensorToInternal_naturality
    {M M' : IM} (f : M ⟶ M') (N : IM) :
    SheafOfModules.siteTensorHom ((E).map f).val ((E).obj N).val ≫
        sectionTensorToInternal J R M' N =
      sectionTensorToInternal J R M N ≫ ((E).map (f ▷ N)).val := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h : tensorPair J R M N ≫ F.map (f ▷ N).hom =
      F.map f.hom ▷ F.obj N.X ≫ tensorPair J R M' N := by
    dsimp only [tensorPair]
    rw [Category.assoc, ← F.map_comp, Mod.tensorObjπ_whiskerRight,
      F.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  ext U : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  exact congrArg (fun t ↦ (t.app U).hom (m ⊗ₜ[ℤ] n)) h.symm

attribute [irreducible] sheafTensorUnderlyingPair tensorPairLinear sectionTensorToInternal

omit [HasCoequalizers (Sheaf J AddCommGrpCat.{u})]
  [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem sheafTensorUnderlyingPair_balance (M N : IM) :
    ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ sheafTensorUnderlyingPair J R M N =
      ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫
        sheafTensorUnderlyingPair J R M N := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h :
      Functor.LaxMonoidal.μ F M.X R ▷ F.obj N.X ≫
        Functor.LaxMonoidal.μ F (M.X ⊗ R) N.X ≫
        F.map (((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫
          sheafTensorUnderlyingPair J R M N) =
      Functor.LaxMonoidal.μ F M.X R ▷ F.obj N.X ≫
        Functor.LaxMonoidal.μ F (M.X ⊗ R) N.X ≫
        F.map (((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫
          sheafTensorUnderlyingPair J R M N) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
    rw [← comp_whiskerRight_assoc]
    rw [F.map_comp, Functor.LaxBraided.braided_assoc]
    rw [Functor.LaxMonoidal.associativity_assoc]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [sheafTensorUnderlyingPair_spec]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ toSheafify J _ ) (rawTensorQuotient_balance J R M N)
  exact sheafTriple_hom_ext J M.X R N.X _ h

private noncomputable def internalTensorToSheaf (M N : IM) :
    (M ⊗ N).X ⟶ (SheafOfModules.toSheaf _).obj
      (sectionTensorSheaf J R M N) :=
  coequalizer.desc (sheafTensorUnderlyingPair J R M N)
    (sheafTensorUnderlyingPair_balance J R M N)
private theorem sheafTensorUnderlyingPair_comp (M N : IM) :
    sheafTensorUnderlyingPair J R M N ≫
      (SheafOfModules.toSheaf _).map (sheafTensorToInternal J R M N) =
        Mod.tensorObjπ M N := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, ← Category.assoc, sheafTensorUnderlyingPair_spec, Category.assoc]
  erw [sheafTensorToInternal_unit]
  rw [rawTensorQuotient_comp]
  rfl

private theorem internalTensorToSheaf_comp (M N : IM) :
    internalTensorToSheaf J R M N ≫
      (SheafOfModules.toSheaf _).map (sheafTensorToInternal J R M N) = 𝟙 _ := by
  rw [← cancel_epi (Mod.tensorObjπ M N)]
  change Mod.tensorObjπ M N ≫ (coequalizer.desc _ _) ≫ _ = _
  dsimp only [Mod.tensorObjπ]
  erw [coequalizer.π_desc_assoc]
  exact (sheafTensorUnderlyingPair_comp J R M N).trans (Category.comp_id _).symm
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoequalizers (Sheaf J AddCommGrpCat.{u})] [MonoidalClosed (Sheaf J AddCommGrpCat.{u})] in
private theorem rawTensorQuotient_epi (M N : IM) : Epi (rawTensorQuotient J R M N) := by
  have (U : Cᵒᵖ) : Epi ((rawTensorQuotient J R M N).app U) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact ⟨m ⊗ₜ[ℤ] n, rfl⟩
    | add z w hz hw =>
      obtain ⟨z', hz'⟩ := hz
      obtain ⟨w', hw'⟩ := hw
      exact ⟨z' + w', by rw [map_add, hz', hw']⟩
  exact NatTrans.epi_of_epi_app _

private theorem sheafTensorToInternal_comp (M N : IM) :
    (SheafOfModules.toSheaf _).map (sheafTensorToInternal J R M N) ≫
      internalTensorToSheaf J R M N = 𝟙 _ := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  apply sheafification_hom_ext J
  simp only [Functor.map_comp]
  rw [← Category.assoc]
  refine (congrArg (fun z ↦ z ≫ F.map (internalTensorToSheaf J R M N))
    (sheafTensorToInternal_unit J R M N)).trans ?_
  have := rawTensorQuotient_epi J R M N
  rw [← cancel_epi (rawTensorQuotient J R M N), ← Category.assoc,
    rawTensorQuotient_comp]
  change Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫ _ = _
  erw [← F.map_comp]
  have h : Mod.tensorObjπ M N ≫ internalTensorToSheaf J R M N =
      sheafTensorUnderlyingPair J R M N := coequalizer.π_desc _ _
  rw [h, sheafTensorUnderlyingPair_spec]
  rfl

private noncomputable def sheafTensorIso (M N : IM) :
    sectionTensorSheaf J R M N ≅
      (E).obj (M ⊗ N) := by
  have h : IsIso ((SheafOfModules.toSheaf _).map (sheafTensorToInternal J R M N)) :=
    ⟨⟨internalTensorToSheaf J R M N, sheafTensorToInternal_comp J R M N,
      internalTensorToSheaf_comp J R M N⟩⟩
  have : IsIso (sheafTensorToInternal J R M N) :=
    isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  exact asIso (sheafTensorToInternal J R M N)
private noncomputable def comparison_presheafTensorIso (M N : IM) :
    ((E).obj M).val ⊗ ((E).obj N).val ≅
      SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    apply ModuleCat.hom_ext
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy])

/-- The sectionwise balanced tensor sheaf and the internal relative tensor have the
same universal pairing. Source: Stacks Project, Tag 03EK.
The inverse is the sheafification lift of the balanced pairing into the coequalizer.
The forward map is the coequalizer descent of the sectionwise tensor pairing; their
composites are identities by the two universal properties. The formula follows
from the sheafification unit equation.
(auxiliary; not a blueprint node) -/
theorem exists_sectionTensorIso (M N : IM) :
    ∃ e : (E).obj (M ⊗ N) ≅ (PresheafOfModules.sheafification
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (sectionRingSheaf J R)) (𝟙 _)).obj
        (((E).obj M).val ⊗ ((E).obj N).val),
    ∀ (U : Cᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (e.hom.val.app U)
          (((Mod.tensorObjπ M N).hom.app U)
            (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X).app U)
              (x ⊗ₜ[ℤ] y))) =
        ((toSheafify J ((((E).obj M).val ⊗ ((E).obj N).val).presheaf)).app U)
          (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y) := by
  let S := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R)) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R)) (𝟙 _)
  let i := comparison_presheafTensorIso J R M N
  let c := S.mapIso i ≪≫ sheafTensorIso J R M N
  refine ⟨c.symm, ?_⟩
  intro U x y
  have hf : (c.hom.val.app U)
      (((toSheafify J ((((E).obj M).val ⊗ ((E).obj N).val).presheaf)).app U)
        (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y)) =
      ((Mod.tensorObjπ M N).hom.app U)
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X).app U)
          (x ⊗ₜ[ℤ] y)) := by
    have hn := congrArg (fun f ↦ (f.app U)
        (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y)) (adj.unit.naturality i.hom)
    have h := congrArg (fun f ↦ (f.app U).hom
        (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))
      (sheafTensorToInternal_unit J R M N)
    change (sheafTensorToInternal J R M N).val.app U _ =
      ((sectionTensorToInternal J R M N).app U).hom _ at h
    rw [sectionTensorToInternal_tmul] at h
    change (sheafTensorToInternal J R M N).val.app U
      ((S.map i.hom).val.app U _) = _
    change ((toSheafify J
        (SheafOfModules.siteTensorPresheaf ((E).obj M).val ((E).obj N).val).presheaf).app U)
          (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y) =
        (S.map i.hom).val.app U
          (((toSheafify J ((((E).obj M).val ⊗ ((E).obj N).val).presheaf)).app U)
            (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y)) at hn
    exact (congrArg ((sheafTensorToInternal J R M N).val.app U) hn).symm.trans h
  have hc := congrArg (fun f ↦ (f.val.app U)
    (((toSheafify J ((((E).obj M).val ⊗ ((E).obj N).val).presheaf)).app U)
      (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))) c.hom_inv_id
  exact (congrArg (c.inv.val.app U) hf).symm.trans hc

private theorem sheafTensorToInternal_naturality
    {M M' : IM} (f : M ⟶ M') (N : IM) :
    (PresheafOfModules.sheafification (𝟙 _)).map
      (SheafOfModules.siteTensorHom ((E).map f).val ((E).obj N).val) ≫
        sheafTensorToInternal J R M' N =
      sheafTensorToInternal J R M N ≫ (E).map (f ▷ N) := by
  exact moduleSheafLift_naturality
    (M := (E).obj (M ⊗ N)) (N := (E).obj (M' ⊗ N))
    (SheafOfModules.siteTensorHom ((E).map f).val ((E).obj N).val)
    ((E).map (f ▷ N)) (sectionTensorToInternal J R M N)
    (sectionTensorToInternal J R M' N) (sectionTensorToInternal_naturality J R f N)

private noncomputable def tensorRightComparison (N : IM) :
    E ⋙ SheafOfModules.siteSheafTensorRight ((E).obj N) ≅ tensorRight N ⋙ E :=
  NatIso.ofComponents (fun M ↦ sheafTensorIso J R M N)
    (fun f ↦ sheafTensorToInternal_naturality J R f N)
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exact_tensorRight_iff (M : IM) :
    exactFunctor _ _ (tensorRight M) ↔
      exactFunctor _ _ (SheafOfModules.siteSheafTensorRight ((E).obj M)) := by
  let e := sectionModuleEquivalence J R
  let T := SheafOfModules.siteSheafTensorRight ((E).obj M)
  let t : e.functor ⋙ T ≅ tensorRight M ⋙ e.functor := tensorRightComparison J R M
  constructor
  · intro h
    have : PreservesFiniteLimits (tensorRight M) := h.1
    have : PreservesFiniteColimits (tensorRight M) := h.2
    let i : T ≅ e.inverse ⋙ tensorRight M ⋙ e.functor :=
      (Functor.leftUnitor T).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm T ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse t
    exact (exactFunctor _ _).prop_of_iso i.symm
      ((exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩)
  · intro h
    have : PreservesFiniteLimits T := h.1
    have : PreservesFiniteColimits T := h.2
    have : PreservesFiniteLimits (e.functor ⋙ T) := inferInstance
    have : PreservesFiniteColimits (e.functor ⋙ T) := inferInstance
    have : PreservesFiniteLimits (tensorRight M ⋙ e.functor) :=
      preservesFiniteLimits_of_natIso t
    have : PreservesFiniteColimits (tensorRight M ⋙ e.functor) :=
      preservesFiniteColimits_of_natIso t
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ e.functor,
      preservesFiniteColimits_of_reflects_of_preserves _ e.functor⟩

/-- Internal tensor flatness agrees with flatness for the sheafified section tensor product.
Source: Stacks Project, Modules on Sites, section Tensor product.
The canonical balanced map from section tensors to the relative tensor coequalizer
is invertible: its inverse sends a pure tensor to the sheafification unit of the
sectionwise balanced tensor. Both identities follow on pure tensors and descend
through sheafification and the coequalizer. These maps are natural, so the section
module equivalence transports exactness of right tensoring. The braiding supplies
left tensoring. Empty covers and zero modules are included by the same universal
properties. (auxiliary; not a blueprint node) -/
theorem flat_iff_sectionModule (M : IM) :
    ObjectProperty.flat M ↔ SheafOfModules.IsFlatOnSite ((E).obj M) := by
  constructor
  · intro h
    exact (exact_tensorRight_iff J R M).mp h.2
  · intro h
    have ht := (exact_tensorRight_iff J R M).mpr h
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight M).symm ht, ht⟩
end CategoryTheory.InternalAbelianSheafModule
