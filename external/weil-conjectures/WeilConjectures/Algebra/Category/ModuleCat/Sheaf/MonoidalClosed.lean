/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# The tensor-hom adjunction for sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. For sheaves of modules `A`, `T` and
`N` over `R`, morphisms `A ⊗ T ⟶ N` correspond to morphisms `T ⟶ homObj A N`
(`SheafOfModules.tensorHomEquiv`), naturally in all three variables. In other words, tensoring
with `A` is left adjoint to the internal hom out of `A` (`SheafOfModules.tensorHomAdjunction`).

The bijection is the composite of the identification `A ⊗ T ≅ a(A ⊗ T)` of the tensor product
with the sheafification of the tensor product of the underlying presheaves, of the
sheafification adjunction, and of the tensor-hom adjunction for presheaves of modules
`PresheafOfModules.homObjEquiv`.

## Main definitions and results

- `SheafOfModules.tensorHomEquiv`: the bijection `(A ⊗ T ⟶ N) ≃ (T ⟶ homObj A N)`.
- `SheafOfModules.tensorHomEquiv_whiskerLeft_comp`,
  `SheafOfModules.tensorHomEquiv_comp_homObjMap`,
  `SheafOfModules.tensorHomEquiv_whiskerRight_comp`: its naturality in `T`, `N` and `A`.
- `SheafOfModules.tensorHomAdjunction`: the adjunction `tensorLeft A ⊣ homObj A`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The tensor-hom adjunction for presheaves of modules is natural in the target. -/
lemma homObjEquiv_comp_homObjMap {M P N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (φ : M ⊗ P ⟶ N) (g : N ⟶ N') :
    homObjEquiv M P N' (φ ≫ g) = homObjEquiv M P N φ ≫ homObjMap (𝟙 M) g := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N')
    fun W ↦ ?_
  rfl

/-- The tensor-hom adjunction for presheaves of modules is natural in the first variable. -/
lemma homObjEquiv_whiskerRight_comp {M M' P N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (f : M' ⟶ M) (φ : M ⊗ P ⟶ N) :
    homObjEquiv M' P N (f ▷ P ≫ φ) = homObjEquiv M P N φ ≫ homObjMap f (𝟙 N) := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M') (M₂ := (restrictOver R X.unop).obj N)
    fun W ↦ ?_
  rfl

end PresheafOfModules

namespace SheafOfModules

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] monoidalCategory symmetricCategory

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
@[reassoc]
lemma whiskerLeft_tensorObjIsoSheafification_hom (A : SheafOfModules.{u} 𝓡)
    {T T' : SheafOfModules.{u} 𝓡} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫ (𝓢).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
@[reassoc]
lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : SheafOfModules.{u} 𝓡}
    (f : A' ⟶ A) (T : SheafOfModules.{u} 𝓡) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫ (𝓢).map (f.val ▷ T.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- **The tensor-hom adjunction for sheaves of modules**: morphisms `A ⊗ T ⟶ N` correspond to
morphisms `T ⟶ homObj A N`. A morphism `A ⊗ T ⟶ N` is a morphism `a(A ⊗ T) ⟶ N` out of the
sheafification of the presheaf tensor product, i.e. a morphism of presheaves `A ⊗ T ⟶ N`, which
`PresheafOfModules.homObjEquiv` turns into a morphism `T ⟶ homObj A N`. -/
noncomputable def tensorHomEquiv (A T N : SheafOfModules.{u} 𝓡) :
    (A ⊗ T ⟶ N) ≃ (T ⟶ homObj A N) where
  toFun φ := ⟨PresheafOfModules.homObjEquiv (R := R.obj) A.val T.val N.val
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).homEquiv _ N
      ((tensorObjIsoSheafification A T).inv ≫ φ))⟩
  invFun ψ := (tensorObjIsoSheafification A T).hom ≫
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).homEquiv _ N).symm
      ((PresheafOfModules.homObjEquiv (R := R.obj) A.val T.val N.val).symm ψ.val)
  left_inv φ := by simp
  right_inv ψ := by
    ext1
    dsimp only
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma tensorHomEquiv_val (A T N : SheafOfModules.{u} 𝓡) (φ : A ⊗ T ⟶ N) :
    (tensorHomEquiv A T N φ).val = PresheafOfModules.homObjEquiv (R := R.obj) A.val T.val N.val
      ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).homEquiv _ N
        ((tensorObjIsoSheafification A T).inv ≫ φ)) :=
  rfl

/-- The tensor-hom adjunction for sheaves of modules is natural in `T`. -/
lemma tensorHomEquiv_whiskerLeft_comp (A : SheafOfModules.{u} 𝓡) {T T' N : SheafOfModules.{u} 𝓡}
    (f : T ⟶ T') (φ : A ⊗ T' ⟶ N) :
    tensorHomEquiv A T N (A ◁ f ≫ φ) = f ≫ tensorHomEquiv A T' N φ := by
  have h : (tensorObjIsoSheafification A T).inv ≫ A ◁ f =
      (𝓢).map (A.val ◁ f.val) ≫ (tensorObjIsoSheafification A T').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerLeft_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  rw [comp_val, tensorHomEquiv_val, tensorHomEquiv_val, ← Category.assoc, h, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.homObjEquiv_whiskerLeft_comp _ _

/-- The tensor-hom adjunction for sheaves of modules is natural in `N`. -/
lemma tensorHomEquiv_comp_homObjMap (A : SheafOfModules.{u} 𝓡) {T N N' : SheafOfModules.{u} 𝓡}
    (φ : A ⊗ T ⟶ N) (g : N ⟶ N') :
    tensorHomEquiv A T N' (φ ≫ g) = tensorHomEquiv A T N φ ≫ homObjMap (𝟙 A) g := by
  ext1
  rw [comp_val, tensorHomEquiv_val, tensorHomEquiv_val, ← Category.assoc,
    Adjunction.homEquiv_naturality_right]
  exact PresheafOfModules.homObjEquiv_comp_homObjMap _ _

/-- The tensor-hom adjunction for sheaves of modules is natural in `A`. -/
lemma tensorHomEquiv_whiskerRight_comp {A A' : SheafOfModules.{u} 𝓡} (f : A' ⟶ A)
    {T N : SheafOfModules.{u} 𝓡} (φ : A ⊗ T ⟶ N) :
    tensorHomEquiv A' T N (f ▷ T ≫ φ) = tensorHomEquiv A T N φ ≫ homObjMap f (𝟙 N) := by
  have h : (tensorObjIsoSheafification A' T).inv ≫ f ▷ T =
      (𝓢).map (f.val ▷ T.val) ≫ (tensorObjIsoSheafification A T).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerRight_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  rw [comp_val, tensorHomEquiv_val, tensorHomEquiv_val, ← Category.assoc, h, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.homObjEquiv_whiskerRight_comp _ _

variable (R) in
/-- **The tensor-hom adjunction for sheaves of modules**: tensoring with `A` is left adjoint to
the internal hom `homObj A`. -/
noncomputable def tensorHomAdjunction (A : SheafOfModules.{u} 𝓡) :
    tensorLeft A ⊣ (homFunctor R).obj (Opposite.op A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv A
      homEquiv_naturality_left_symm f g := by
        rw [Equiv.symm_apply_eq]
        exact ((congrArg (f ≫ ·) (Equiv.apply_symm_apply (tensorHomEquiv A _ _) g).symm).trans
          (tensorHomEquiv_whiskerLeft_comp A f _).symm)
      homEquiv_naturality_right f g := tensorHomEquiv_comp_homObjMap A f g }

/-- **Sheaves of modules form a monoidal closed category**, with internal hom `homObj`:
tensoring with `A` is left adjoint to `homObj A` (`SheafOfModules.tensorHomAdjunction`). -/
@[instance_reducible]
noncomputable def monoidalClosed : MonoidalClosed (SheafOfModules.{u} 𝓡) where
  closed A := { rightAdj := (homFunctor R).obj (Opposite.op A), adj := tensorHomAdjunction R A }

attribute [local instance] monoidalClosed

lemma ihom_obj (A N : SheafOfModules.{u} 𝓡) : (ihom A).obj N = homObj A N := rfl

lemma uncurry_eq_tensorHomEquiv_symm {A T N : SheafOfModules.{u} 𝓡} (g : T ⟶ homObj A N) :
    MonoidalClosed.uncurry g = (tensorHomEquiv A T N).symm g := by
  change ((tensorHomAdjunction R A).homEquiv _ _).symm g = _
  rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

lemma ihom_ev_app (A N : SheafOfModules.{u} 𝓡) :
    (ihom.ev A).app N = (tensorHomEquiv A ((ihom A).obj N) N).symm (𝟙 _) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_eq_tensorHomEquiv_symm]

/-- The functoriality `MonoidalClosed.pre` of the internal hom in its first variable is
`homObjMap`. -/
lemma pre_app {A A' : SheafOfModules.{u} 𝓡} (f : A' ⟶ A) (N : SheafOfModules.{u} 𝓡) :
    (MonoidalClosed.pre f).app N = homObjMap f (𝟙 N) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre, uncurry_eq_tensorHomEquiv_symm, Equiv.eq_symm_apply,
    tensorHomEquiv_whiskerRight_comp, ihom_ev_app, Equiv.apply_symm_apply, Category.id_comp]

end SheafOfModules
