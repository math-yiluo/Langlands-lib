/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechFreeResolution

/-!
# Čech complexes of injective presheaves

Let `X` be an object of a category `C` and `U : ι → Over X` a family of objects over `X`
(with `ι : Type w`). For a presheaf `P : Cᵒᵖ ⥤ AddCommGrpCat.{max v w}`, the Čech cochains of
degree `n` of `(Over.forget X).op ⋙ P` with respect to `U` (Mathlib's
`CategoryTheory.cechComplexFunctor`) are the morphisms `ℤ_𝔘[n] ⟶ P` from the
free presheaf `CategoryTheory.Presheaf.cechFree U n`, compatibly with the differentials.
As the complex `ℤ_𝔘[•]` is exact, the Čech complex of an injective presheaf is exact in
positive degrees.

## Main definitions

- `CategoryTheory.Presheaf.cechFreeHomEquiv`: the identification of morphisms `ℤ_𝔘[n] ⟶ P` with
  Čech cochains of degree `n`.

## Main statements

- `CategoryTheory.Presheaf.cechFreeHomEquiv_cechFreeD_comp`: compatibility with the differentials.
- `CategoryTheory.Presheaf.exact_cechComplexFunctor_of_injective`: the Čech complex of an
  injective presheaf is exact in positive degrees.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Simplicial

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {X : C} [HasFiniteProducts (Over X)] {ι : Type w}
  (U : ι → Over X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max v w})

/-- The factor `P(U (y 0) ×_X ⋯ ×_X U (y n))` of the Čech cochains of degree `n`. -/
noncomputable abbrev cechFactor (n : ℕ) (y : Fin (n + 1) → ι) : AddCommGrpCat.{max v w} :=
  P.obj (op (cechNerveObj U y).left)

/-- The Čech complex of `(Over.forget X).op ⋙ P` with respect to `U`. -/
noncomputable abbrev cechOver : CochainComplex AddCommGrpCat.{max v w} ℕ :=
  (cechComplexFunctor U).obj ((Over.forget X).op ⋙ P)

lemma cechOver_X (n : ℕ) : (cechOver U P).X n = ∏ᶜ cechFactor U P n :=
  rfl

/-- The component of a Čech cochain at a tuple `y`. -/
noncomputable def cechCochainπ (n : ℕ) (y : Fin (n + 1) → ι) :
    (cechOver U P).X n ⟶ cechFactor U P n y :=
  Pi.π (cechFactor U P n) y

/-- The Čech cochain with given components. -/
noncomputable def cechCochainMk (n : ℕ) (c : ∀ y, cechFactor U P n y) : (cechOver U P).X n :=
  (Concrete.productEquiv (cechFactor U P n)).symm c

@[simp]
lemma cechCochainπ_mk (n : ℕ) (c : ∀ y, cechFactor U P n y) (y : Fin (n + 1) → ι) :
    cechCochainπ U P n y (cechCochainMk U P n c) = c y :=
  Concrete.productEquiv_symm_apply_π _ _ _

lemma cechCochain_ext {n : ℕ} {c c' : (cechOver U P).X n}
    (h : ∀ y, cechCochainπ U P n y c = cechCochainπ U P n y c') : c = c' := by
  apply (Concrete.productEquiv (cechFactor U P n)).injective
  funext y
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply]
  exact h y

lemma cechOver_δ_π (n : ℕ) (i : Fin (n + 2)) (y : Fin (n + 2) → ι) :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        ((Over.forget X).op ⋙ P)).δ i ≫ cechCochainπ U P (n + 1) y =
      cechCochainπ U P n (y ∘ i.succAbove) ≫ P.map (cechNerveMap U y i.succAbove).left.op := by
  erw [Pi.lift_comp_π]
  rfl

lemma cechCochainπ_d (n : ℕ) (c : (cechOver U P).X n) (y : Fin (n + 2) → ι) :
    cechCochainπ U P (n + 1) y ((cechOver U P).d n (n + 1) c) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (cechNerveMap U y i.succAbove).left.op (cechCochainπ U P n (y ∘ i.succAbove) c) := by
  rw [← ConcreteCategory.comp_apply, cechComplexFunctor_obj_d, Preadditive.sum_comp,
    AddCommGrpCat.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp]
  erw [cechOver_δ_π]
  rfl

variable {U P}

lemma cechFree_app_of {n : ℕ} (φ : cechFree U n ⟶ P) {T : Cᵒᵖ} (y : Fin (n + 1) → ι)
    (g : T.unop ⟶ (cechNerveObj U y).left) :
    φ.app T (FreeAbelianGroup.of ⟨y, g⟩) =
      P.map g.op (φ.app (op (cechNerveObj U y).left) (FreeAbelianGroup.of ⟨y, 𝟙 _⟩)) := by
  have := ConcreteCategory.congr_hom (φ.naturality g.op) (FreeAbelianGroup.of ⟨y, 𝟙 _⟩)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  refine Eq.trans ?_ this
  congr 1
  change _ = FreeAbelianGroup.map _ (FreeAbelianGroup.of _)
  rw [FreeAbelianGroup.map_of_apply]
  congr
  exact (Category.comp_id g).symm

variable (U P)

/-- **Čech cochains are morphisms from the free resolution.** Morphisms `ℤ_𝔘[n] ⟶ P` are the Čech
cochains of degree `n` of `(Over.forget X).op ⋙ P`: a morphism `φ` corresponds to the cochain
`y ↦ φ(y, 𝟙)`. -/
noncomputable def cechFreeHomEquiv (n : ℕ) : (cechFree U n ⟶ P) ≃+ (cechOver U P).X n where
  toFun φ := cechCochainMk U P n fun y ↦
    φ.app (op (cechNerveObj U y).left) (FreeAbelianGroup.of ⟨y, 𝟙 _⟩)
  invFun c :=
    { app T := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun s ↦
        P.map s.2.op (cechCochainπ U P n s.1 c))
      naturality T T' g := by
        apply AddCommGrpCat.hom_ext
        refine FreeAbelianGroup.lift_ext _ _ fun s ↦ ?_
        change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of s)) =
          P.map g (FreeAbelianGroup.lift _ (FreeAbelianGroup.of s))
        rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
          FreeAbelianGroup.lift_apply_of]
        change P.map (g.unop ≫ s.2).op _ = _
        rw [op_comp, P.map_comp]
        rfl }
  left_inv φ := by
    ext T : 2
    apply AddCommGrpCat.hom_ext
    refine FreeAbelianGroup.lift_ext _ _ fun s ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.of s) = _
    rw [FreeAbelianGroup.lift_apply_of, cechCochainπ_mk]
    exact (cechFree_app_of φ s.1 s.2).symm
  right_inv c := cechCochain_ext U P fun y ↦ by
    rw [cechCochainπ_mk]
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.of _) = _
    rw [FreeAbelianGroup.lift_apply_of]
    simp
  map_add' φ φ' := cechCochain_ext U P fun y ↦ by
    simp only [cechCochainπ_mk, map_add, NatTrans.app_add, AddCommGrpCat.hom_add,
      AddMonoidHom.add_apply]

lemma cechCochainπ_cechFreeHomEquiv (n : ℕ) (φ : cechFree U n ⟶ P) (y : Fin (n + 1) → ι) :
    cechCochainπ U P n y (cechFreeHomEquiv U P n φ) =
      φ.app (op (cechNerveObj U y).left) (FreeAbelianGroup.of ⟨y, 𝟙 _⟩) :=
  cechCochainπ_mk U P n (fun y ↦ φ.app _ (FreeAbelianGroup.of ⟨y, 𝟙 _⟩)) y

/-- The identification `cechFreeHomEquiv` is compatible with the differentials. -/
lemma cechFreeHomEquiv_cechFreeD_comp (n : ℕ) (φ : cechFree U n ⟶ P) :
    cechFreeHomEquiv U P (n + 1) (cechFreeD U n ≫ φ) =
      (cechOver U P).d n (n + 1) (cechFreeHomEquiv U P n φ) := by
  refine cechCochain_ext U P fun y ↦ ?_
  rw [cechCochainπ_d, cechCochainπ_cechFreeHomEquiv, NatTrans.comp_app,
    ConcreteCategory.comp_apply, cechFreeD_app_of, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, cechCochainπ_cechFreeHomEquiv, cechNerveSigmaMap_app_apply]
  congr 1
  exact (cechFree_app_of φ _ _).trans (by rw [Category.id_comp])

/-- **Čech complexes of injective presheaves are exact in positive degrees.** For an injective
presheaf of abelian groups `P` on `C`, the Čech complex of `(Over.forget X).op ⋙ P` with respect
to any family `U` of objects of `Over X` is exact in degree `n + 1`. -/
theorem exact_cechComplexFunctor_of_injective [Injective P] (n : ℕ) :
    ((cechOver U P).sc' n (n + 1) (n + 2)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro c hc
  obtain ⟨φ, rfl⟩ := (cechFreeHomEquiv U P (n + 1)).surjective c
  have hφ : cechFreeD U (n + 1) ≫ φ = 0 := (cechFreeHomEquiv U P (n + 2)).injective (by
    rw [cechFreeHomEquiv_cechFreeD_comp, map_zero]
    exact hc)
  have hS := exact_cechFreeD U n
  refine ⟨cechFreeHomEquiv U P n (hS.descToInjective φ hφ), ?_⟩
  change (cechOver U P).d n (n + 1) _ = _
  rw [← cechFreeHomEquiv_cechFreeD_comp]
  congr 1
  exact hS.comp_descToInjective φ hφ

end CategoryTheory.Presheaf
