/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# K-flat complexes of modules on a ringed site

Source: the blueprint of the Weil conjectures, chapter `chap-The-Picard-scheme-of-a-curve`, unit
`lemma-triviality-fibres--2` (blueprint: def-pc-kflat-complex); Stacks Project, Cohomology on Sites,
Definition `sites-cohomology-definition-K-flat` (Tag 06YN), and the term "K-flat resolution" as
used in Lemma `sites-cohomology-lemma-K-flat-resolution` (Tag 06YS).

Let `R` be a sheaf of commutative rings on a site `(C, J)`. Sheaves of modules over `R` carry the
monoidal structure `SheafOfModules.monoidalCategory R` (the tensor product is the sheafification
of the tensor product of presheaves of modules); it is not an instance and is used here with
`letI`. The total tensor complex `Tot(F ⊗ K)` of two cochain complexes is
`CochainComplex.mapBifunctor F K (curriedTensor _)`.

## Main definitions

- `CochainComplex.IsKFlatTensor`: a complex `K` of `R`-modules is K-flat if `Tot(F ⊗ K)` is acyclic
  for every acyclic complex `F` of `R`-modules.
- `CochainComplex.IsKFlatTensorResolution`: a morphism `K ⟶ G` is a K-flat resolution of `G`
  if it is a quasi-isomorphism and `K` is K-flat.

## Main statements

- `SheafOfModules.preservesZeroMorphisms_curriedTensor`,
  `SheafOfModules.preservesZeroMorphisms_curriedTensor_obj`: the tensor product of sheaves of
  modules preserves zero morphisms in each variable (needed to form the total tensor complex).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Limits
open scoped ZeroObject

-- The tensor--Hom proof in the source fixes both site universes to the coefficient
-- universe. These private helpers give the same sectionwise construction for `max u v`.
-- Source: WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom, TensorHom.
namespace PresheafOfModules

open Opposite

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}

variable (M) in
private noncomputable def tmulRight_kf {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

@[local simp]
private lemma tmulRight_apply_kf {X : Cᵒᵖ} (p : P.obj X) (m : M.obj X) :
    tmulRight_kf M p m = m ⊗ₜ[R.obj X] p :=
  rfl

private noncomputable def tensorHomCurryApp_kf (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U)) :
    (restrictOver R U).obj M ⟶ (restrictOver R U).obj N where
  app W := tmulRight_kf M (P.map W.unop.hom.op p) ≫ φ.app (op W.unop.left)
  naturality {W W'} f := by
    ext m
    refine (congrArg (φ.app (op W'.unop.left)) ?_).trans
      (naturality_apply φ f.unop.left.op (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p))
    refine (congrArg (fun q : P.obj (op W'.unop.left) ↦
      TensorProduct.tmul (R := R.obj (op W'.unop.left))
        (M := M.obj (op W'.unop.left)) (N := P.obj (op W'.unop.left))
        (M.map f.unop.left.op m) q) ?_).trans
        (Monoidal.tensorObj_map_tmul f.unop.left.op m _).symm
    rw [← map_comp_apply, ← op_comp, Over.w]

@[local simp]
private lemma tensorHomCurryApp_app_apply_kf (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp_kf φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_add_kf (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp_kf φ (p + p') =
      tensorHomCurryApp_kf φ p + tensorHomCurryApp_kf φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply_kf,
    tensorHomCurryApp_app_apply_kf, tensorHomCurryApp_app_apply_kf, map_add, TensorProduct.tmul_add,
    map_add]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_smul_kf (φ : M ⊗ P ⟶ N) {U : C}
    (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp_kf φ (r • p) = r • tensorHomCurryApp_kf φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply_kf,
    tensorHomCurryApp_app_apply_kf, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_map_kf (φ : M ⊗ P ⟶ N) {U V : C} (g : V ⟶ U) (p : P.obj (op U)) :
    tensorHomCurryApp_kf (U := V) φ (P.map g.op p) =
      restrictOverMap g (tensorHomCurryApp_kf φ p) := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [restrictOverMap_app, tensorHomCurryApp_app_apply_kf, ← map_comp_apply]
  rfl

private noncomputable def tensorHomCurry_kf (φ : M ⊗ P ⟶ N) : P ⟶ homObj M N where
  app X := ModuleCat.ofHom (X := P.obj X) (Y := (homObj M N).obj X)
    { toFun p := tensorHomCurryApp_kf φ p
      map_add' := tensorHomCurryApp_add_kf φ
      map_smul' := tensorHomCurryApp_smul_kf φ }
  naturality {X Y} g := by
    ext p : 2
    exact tensorHomCurryApp_map_kf φ g.unop p

@[local simp]
private lemma tensorHomCurry_app_apply_kf (φ : M ⊗ P ⟶ N) (X : Cᵒᵖ) (p : P.obj X) :
    (tensorHomCurry_kf φ).app X p = tensorHomCurryApp_kf φ p :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (M N) in
private noncomputable def homObjEvalId_kf (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)] M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

@[local simp]
private lemma homObjEvalId_apply_apply_kf (U : C) (φ : (homObj M N).obj (op U)) (m : M.obj (op U)) :
    homObjEvalId_kf M N U φ m = φ.app (op (Over.mk (𝟙 U))) m :=
  rfl

private noncomputable def tensorHomUncurry_kf (ψ : P ⟶ homObj M N) : M ⊗ P ⟶ N where
  app X := ModuleCat.ofHom
    (TensorProduct.lift ((homObjEvalId_kf M N X.unop).comp (ψ.app X).hom).flip)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine (congrArg (fun ξ : (restrictOver R Y.unop).obj M ⟶ (restrictOver R Y.unop).obj N ↦
      ξ.app (op (Over.mk (𝟙 Y.unop))) (M.map f m)) (naturality_apply ψ f p)).trans ?_
    refine (restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply (ψ.app X p) (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

@[local simp]
private lemma tensorHomUncurry_app_tmul_kf (ψ : P ⟶ homObj M N) (X : Cᵒᵖ)
    (m : M.obj X) (p : P.obj X) :
    (tensorHomUncurry_kf ψ).app X (m ⊗ₜ[R.obj X] p) =
      (ψ.app X p).app (op (Over.mk (𝟙 X.unop))) m :=
  rfl

private noncomputable def homObjEquiv_kf (M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)) :
    (M ⊗ P ⟶ N) ≃ (P ⟶ homObj M N) where
  toFun := tensorHomCurry_kf
  invFun := tensorHomUncurry_kf
  left_inv φ := by
    ext X : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine congrArg (fun q : P.obj X ↦ φ.app X (m ⊗ₜ[R.obj X] q)) (?_ : P.map (𝟙 X) p = p)
    rw [map_id]
    rfl
  right_inv ψ := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
    refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
      fun W ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
    refine (congrArg (fun ξ : (restrictOver R W.unop.left).obj M ⟶
        (restrictOver R W.unop.left).obj N ↦ ξ.app (op (Over.mk (𝟙 W.unop.left))) m)
      (naturality_apply ψ W.unop.hom.op p)).trans ?_
    exact restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp W.unop.hom) m

private lemma homObjEquiv_whiskerLeft_comp_kf
    {M P P' N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}
    (f : P ⟶ P') (φ : M ⊗ P' ⟶ N) :
    homObjEquiv_kf M P N (M ◁ f ≫ φ) = f ≫ homObjEquiv_kf M P' N φ := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
    fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  exact congrArg (fun q : P'.obj (op W.unop.left) ↦
    φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] q)) (naturality_apply f W.unop.hom.op p)


end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
local notation "𝓡" => (sheafCompose J
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{max u v} (𝟙 (𝓡).obj)
set_option hygiene false in
local notation "𝓦" => J.W.inverseImage (PresheafOfModules.toPresheaf.{max u v} (𝓡).obj)

private lemma W_iff_bijective_comp_kf {P₁ P₂ : PresheafOfModules.{max u v} (𝓡).obj} (h : P₁ ⟶ P₂) :
    𝓦 h ↔ ∀ N : SheafOfModules.{max u v} 𝓡, Function.Bijective (fun φ : P₂ ⟶ N.val ↦ h ≫ φ) := by
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 _),
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun N ↦ ?_
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (𝓡).obj)
  have : (fun φ : P₂ ⟶ N.val ↦ h ≫ φ) = adj.homEquiv P₁ N ∘
      (fun x ↦ (𝓢).map h ≫ x) ∘
      (adj.homEquiv P₂ N).symm := by
    funext φ
    exact ((adj.homEquiv_naturality_left h _).trans
      (congrArg (h ≫ ·) ((adj.homEquiv P₂ N).apply_symm_apply φ))).symm
  rw [this]
  exact ((Equiv.bijective_comp _ _).trans (Equiv.comp_bijective _ _)).symm

private lemma W_whiskerLeft_kf (F : PresheafOfModules.{max u v} (𝓡).obj)
    {P₁ P₂ : PresheafOfModules.{max u v} (𝓡).obj} {g : P₁ ⟶ P₂}
    (hg : 𝓦 g) : 𝓦 (F ◁ g) := by
  rw [W_iff_bijective_comp_kf] at hg ⊢
  intro N
  have : (fun φ : F ⊗ P₂ ⟶ N.val ↦ F ◁ g ≫ φ) =
      (PresheafOfModules.homObjEquiv_kf (R := R.obj) F P₁ N.val).symm ∘ (fun ψ ↦ g ≫ ψ) ∘
      PresheafOfModules.homObjEquiv_kf (R := R.obj) F P₂ N.val := by
    funext φ
    exact (Equiv.eq_symm_apply _).2 (PresheafOfModules.homObjEquiv_whiskerLeft_comp_kf g φ)
  rw [this]
  exact ((Equiv.bijective_comp _ _).trans (Equiv.comp_bijective _ _)).2 <|
    hg ⟨PresheafOfModules.homObj (R := R.obj) F N.val,
      PresheafOfModules.isSheaf_homObj N.isSheaf⟩

/-- The tensor localization is monoidal also when the site's morphisms live in a
separate universe. Source: Stacks Project, Modules on Sites, Section 03EK;
Cohomology on Sites, Definition 06YN (blueprint: def-pc-kflat-complex).

Proof: use the sectionwise tensor/internal-Hom adjunction for presheaves of modules.
For a sheaf N the internal Hom into N is a sheaf. Thus tensoring a locally bijective
map induces bijections on morphisms into all sheaves, so its sheafification is an
isomorphism. Symmetry gives the same assertion in the other variable. This argument
is the proof of SheafOfModules.isMonoidal_W and does not require equal hom universes. -/
@[instance]
theorem isMonoidal_W_separateHomUniverse :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{max u v}
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).obj)).IsMonoidal :=
  by
    refine ⟨?_, ?_⟩
    · intro F P₁ P₂ g hg
      exact W_whiskerLeft_kf R F hg
    · intro P₁ P₂ f hf G
      exact ((𝓦).arrow_mk_iso_iff
        (Arrow.isoMk (β_ P₁ G) (β_ P₂ G))).2 (W_whiskerLeft_kf R G hf)

/-- (blueprint: def-pc-kflat-complex) The tensor product of sheaves of modules over a sheaf of
commutative rings `R` (`SheafOfModules.monoidalCategory R`) preserves zero morphisms in the first
variable: `0 ▷ M = 0`. Needed to form the total tensor complex of Stacks, Tag 06YN.

Proof: `M ↦ - ⊗ M` is, up to the counit isomorphism of sheafification, sheafification of the
tensor product of presheaves of modules, which is computed sectionwise in `ModuleCat`, where it
is additive (`MonoidalPreadditive (ModuleCat _)`); sheafification is a left adjoint, hence
preserves zero morphisms. -/
@[instance]
theorem preservesZeroMorphisms_curriedTensor :
    letI := monoidalCategory R
    (curriedTensor (SheafOfModules.{max u v}
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))).PreservesZeroMorphisms :=
  by
    let := monoidalCategory R
    let a := PresheafOfModules.sheafification.{max u v} (𝟙 (𝓡).obj)
    let i := SheafOfModules.forget (𝓡)
    have hzero (M : SheafOfModules.{max u v} (𝓡)) :
        IsZero ((0 : SheafOfModules.{max u v} (𝓡)) ⊗ M) := by
      have hp : IsZero ((0 : SheafOfModules.{max u v} (𝓡)).val) := by
        exact Functor.map_isZero i (isZero_zero _)
      have : (tensorRight M.val).PreservesZeroMorphisms := by
        refine ⟨fun P Q ↦ ?_⟩
        change (0 : P ⟶ Q) ▷ M.val = 0
        ext U : 1
        change whiskerRight (C := ModuleCat (R.obj.obj U)) ((0 : P ⟶ Q).app U) (M.val.obj U) = 0
        simp
      have ht : IsZero ((0 : SheafOfModules.{max u v} (𝓡)).val ⊗ M.val) := by
        exact Functor.map_isZero (tensorRight M.val) hp
      exact (Functor.map_isZero a ht).of_iso (tensorObjIsoSheafification (R := R)
        (0 : SheafOfModules.{max u v} (𝓡)) M)
    refine ⟨fun X Y ↦ ?_⟩
    apply NatTrans.ext
    funext M
    change (0 : X ⟶ Y) ▷ M = 0
    have hz := hzero M
    have h : (0 : X ⟶ Y) =
        (0 : X ⟶ (0 : SheafOfModules.{max u v} (𝓡))) ≫
          (0 : (0 : SheafOfModules.{max u v} (𝓡)) ⟶ Y) := by simp
    rw [h, comp_whiskerRight,
      hz.eq_of_src ((0 : (0 : SheafOfModules.{max u v} (𝓡)) ⟶ Y) ▷ M) 0,
      comp_zero]

/-- (blueprint: def-pc-kflat-complex) The tensor product of sheaves of modules over a sheaf of
commutative rings `R` (`SheafOfModules.monoidalCategory R`) preserves zero morphisms in the
second variable: `M ◁ 0 = 0`. Needed to form the total tensor complex of Stacks, Tag 06YN.

Proof: as for `SheafOfModules.preservesZeroMorphisms_curriedTensor`, or from it by the symmetry
`SheafOfModules.symmetricCategory R`. -/
@[instance]
theorem preservesZeroMorphisms_curriedTensor_obj
    (M : SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :
    letI := monoidalCategory R
    ((curriedTensor (SheafOfModules.{max u v}
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))).obj
        M).PreservesZeroMorphisms :=
  by
    let := monoidalCategory R
    let := symmetricCategory R
    refine ⟨fun X Y ↦ ?_⟩
    change M ◁ (0 : X ⟶ Y) = 0
    have h : (0 : X ⟶ Y) ▷ M = 0 :=
      congrArg (fun t ↦ t.app M) ((curriedTensor _).map_zero X Y)
    apply (cancel_mono (β_ M Y).hom).1
    rw [BraidedCategory.braiding_naturality_right, h, comp_zero, zero_comp]

end SheafOfModules

namespace CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max u v}}

-- The `max u v` module universe makes the `HasMapBifunctor` instance term exceed the default
-- `synthInstance.maxSize` of 128.
set_option synthInstance.maxSize 256 in
/-- (blueprint: def-pc-kflat-complex) Let `R` be a sheaf of commutative rings on a site `(C, J)`.
A cochain complex `K` of sheaves of `R`-modules is *K-flat* if for every acyclic complex `F` of
`R`-modules (all cohomology sheaves vanish, `F.Acyclic`) the total tensor complex
`Tot(F ⊗_R K) = mapBifunctor F K (curriedTensor _)` is acyclic (Stacks, Tag 06YN). The tensor
product is `SheafOfModules.monoidalCategory R`. The general notion `CochainComplex.KFlat`
(`CochainComplex.IsKFlat`) asks instead that tensoring with `K` on both sides preserve
quasi-isomorphisms; for a site whose morphisms live in the universe of the rings the two agree
(`CochainComplex.isKFlatTensor_iff_kFlat`, `CochainComplex.isKFlatTensor_iff_isKFlat`). -/
def IsKFlatTensor
    (K : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    Prop :=
  letI := SheafOfModules.monoidalCategory R
  ∀ F : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ,
    F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic

/-- (blueprint: def-pc-kflat-complex) Let `R` be a sheaf of commutative rings on a site `(C, J)`.
A *K-flat resolution* of a cochain complex `G` of sheaves of `R`-modules is a quasi-isomorphism
`f : K ⟶ G` of complexes of `R`-modules with `K` K-flat (`CochainComplex.IsKFlatTensor`); Stacks,
Tag 06YN, the term as used in Tag 06YS. -/
def IsKFlatTensorResolution
    {K G : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (f : K ⟶ G) : Prop :=
  QuasiIso f ∧ K.IsKFlatTensor

end CochainComplex
