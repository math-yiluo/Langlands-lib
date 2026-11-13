import Langlands.Representation.Hecke.MackeyCurrying
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Products.Basic

/-! # Abstract Mackey isomorphisms from currying and adjunctions

Yoneda arguments behind Renard III.2.11 (displays III.2.11.1–10), for an
arbitrary tensor–Hom currying datum on two categories.
-/

namespace Langlands.Hecke.Mackey

open CategoryTheory CategoryTheory.Prod Opposite

universe w₁ w₂ w₃ u₁ u₂ u₃

section Yoneda

variable {C : Type u₁} [Category.{w₁} C] {J : Type u₃} [Category.{w₃} J]

/-- A natural isomorphism from bijections of maps out of the values, natural in the
target and in the index. -/
def isoOfHomFromEquiv {A B : J ⥤ C} (e : ∀ (j : J) (X : C), (A.obj j ⟶ X) ≃ (B.obj j ⟶ X))
    (he : ∀ (j : J) {X X' : C} (k : X ⟶ X') (f : A.obj j ⟶ X), e j X' (f ≫ k) = e j X f ≫ k)
    (hj : ∀ {j j' : J} (u : j ⟶ j') (X : C) (f : A.obj j' ⟶ X),
      e j X (A.map u ≫ f) = B.map u ≫ e j' X f) :
    A ≅ B :=
  have hs : ∀ (j : J) {X X' : C} (k : X ⟶ X') (g : B.obj j ⟶ X),
      (e j X').symm (g ≫ k) = (e j X).symm g ≫ k := by
    intro j X X' k g
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
  NatIso.ofComponents
    (fun j =>
      { hom := (e j _).symm (𝟙 _)
        inv := e j _ (𝟙 _)
        hom_inv_id := by rw [← hs, Category.id_comp, Equiv.symm_apply_apply]
        inv_hom_id := by rw [← he, Category.id_comp, Equiv.apply_symm_apply] })
    (by
      intro j j' u
      dsimp
      rw [← hs, Category.id_comp, Equiv.eq_symm_apply, hj, Equiv.apply_symm_apply,
        Category.comp_id])

end Yoneda

section Currying

variable {C : Type u₁} [Category.{w₁} C]

/-- A tensor–Hom currying datum: maps `T(E,V) → X` correspond to maps
`E → Hm(V,X)`, naturally in `E`, `V` and `X`. The Hom variable `V` lives in `Cᵒᵖ`. -/
structure Currying (T : C × C ⥤ C) (Hm : Cᵒᵖ × C ⥤ C) where
  /-- The currying bijection. -/
  equiv (E : C) (V : Cᵒᵖ) (X : C) : (T.obj (E, V.unop) ⟶ X) ≃ (E ⟶ Hm.obj (V, X))
  /-- Naturality in all three variables. -/
  equiv_naturality {E E' : C} {V V' : Cᵒᵖ} {X X' : C} (h : E' ⟶ E) (j : V ⟶ V')
    (k : X ⟶ X') (f : T.obj (E, V.unop) ⟶ X) :
    equiv E' V' X' (T.map (h ×ₘ j.unop) ≫ f ≫ k) = h ≫ equiv E V X f ≫ Hm.map (j ×ₘ k)

namespace Currying

variable {T : C × C ⥤ C} {Hm : Cᵒᵖ × C ⥤ C} (c : Currying T Hm)

theorem equiv_symm_naturality {E E' : C} {V V' : Cᵒᵖ} {X X' : C} (h : E' ⟶ E)
    (j : V ⟶ V') (k : X ⟶ X') (g : E ⟶ Hm.obj (V, X)) :
    (c.equiv E' V' X').symm (h ≫ g ≫ Hm.map (j ×ₘ k)) =
      T.map (h ×ₘ j.unop) ≫ (c.equiv E V X).symm g ≫ k := by
  rw [Equiv.symm_apply_eq, c.equiv_naturality, Equiv.apply_symm_apply]

theorem equiv_naturality_left {E E' : C} (h : E' ⟶ E) (V : Cᵒᵖ) (X : C)
    (f : T.obj (E, V.unop) ⟶ X) :
    c.equiv E' V X (T.map (h ×ₘ 𝟙 V.unop) ≫ f) = h ≫ c.equiv E V X f := by
  have := c.equiv_naturality h (𝟙 V) (𝟙 X) f
  simpa only [unop_id, ← prod_id, CategoryTheory.Functor.map_id, Category.comp_id] using this

theorem equiv_symm_naturality_left {E E' : C} (h : E' ⟶ E) (V : Cᵒᵖ) (X : C)
    (g : E ⟶ Hm.obj (V, X)) :
    (c.equiv E' V X).symm (h ≫ g) = T.map (h ×ₘ 𝟙 V.unop) ≫ (c.equiv E V X).symm g := by
  rw [Equiv.symm_apply_eq, c.equiv_naturality_left, Equiv.apply_symm_apply]

theorem equiv_naturality_right (E : C) {V V' : Cᵒᵖ} {X X' : C} (j : V ⟶ V') (k : X ⟶ X')
    (f : T.obj (E, V.unop) ⟶ X) :
    c.equiv E V' X' (T.map (𝟙 E ×ₘ j.unop) ≫ f ≫ k) = c.equiv E V X f ≫ Hm.map (j ×ₘ k) := by
  have := c.equiv_naturality (𝟙 E) j k f
  simpa only [Category.id_comp] using this

theorem equiv_symm_naturality_right (E : C) {V V' : Cᵒᵖ} {X X' : C} (j : V ⟶ V')
    (k : X ⟶ X') (g : E ⟶ Hm.obj (V, X)) :
    (c.equiv E V' X').symm (g ≫ Hm.map (j ×ₘ k)) =
      T.map (𝟙 E ×ₘ j.unop) ≫ (c.equiv E V X).symm g ≫ k := by
  rw [Equiv.symm_apply_eq, c.equiv_naturality_right, Equiv.apply_symm_apply]

end Currying

end Currying

section Abstract

variable {C : Type u₁} [Category.{w₁} C] {D : Type u₂} [Category.{w₂} D]
  {TC : C × C ⥤ C} {HC : Cᵒᵖ × C ⥤ C} (cC : Currying TC HC)
  {TD : D × D ⥤ D} {HD : Dᵒᵖ × D ⥤ D} (cD : Currying TD HD)

section HomMackey

variable {R : C ⥤ D} {I : D ⥤ C} (adj : R ⊣ I) (μ : TC ⋙ R ≅ R.prod R ⋙ TD)

/-- The chain of bijections (III.2.11.1)–(III.2.11.5):
`Hom(E, Hom(V, I W)) ≃ Hom(E, I Hom(R V, W))`. -/
def homMackeyEquiv (V : Cᵒᵖ) (W : D) (E : C) :
    (E ⟶ HC.obj (V, I.obj W)) ≃ (E ⟶ I.obj (HD.obj (R.op.obj V, W))) :=
  (cC.equiv E V (I.obj W)).symm.trans <|
    (adj.homEquiv _ _).symm.trans <|
      (μ.app (E, V.unop)).homFromEquiv.trans <|
        (cD.equiv (R.obj E) (R.op.obj V) W).trans (adj.homEquiv _ _)

theorem homMackeyEquiv_apply (V : Cᵒᵖ) (W : D) (E : C) (f : E ⟶ HC.obj (V, I.obj W)) :
    homMackeyEquiv cC cD adj μ V W E f =
      adj.homEquiv _ _ (cD.equiv (R.obj E) (R.op.obj V) W
        (μ.inv.app (E, V.unop) ≫ (adj.homEquiv _ _).symm ((cC.equiv E V _).symm f))) :=
  rfl

theorem homMackeyEquiv_naturality_source (V : Cᵒᵖ) (W : D) {E E' : C} (h : E' ⟶ E)
    (f : E ⟶ HC.obj (V, I.obj W)) :
    homMackeyEquiv cC cD adj μ V W E' (h ≫ f) = h ≫ homMackeyEquiv cC cD adj μ V W E f := by
  rw [homMackeyEquiv_apply, homMackeyEquiv_apply, cC.equiv_symm_naturality_left,
    Adjunction.homEquiv_naturality_left_symm, ← Category.assoc]
  have := μ.inv.naturality (h ×ₘ 𝟙 V.unop)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, CategoryTheory.Functor.map_id] at this
  rw [← this, Category.assoc, ← Adjunction.homEquiv_naturality_left,
    ← cD.equiv_naturality_left]
  rfl

theorem homMackeyEquiv_naturality_index {V V' : Cᵒᵖ} {W W' : D} (u₁ : V ⟶ V') (u₂ : W ⟶ W')
    (E : C) (f : E ⟶ HC.obj (V, I.obj W)) :
    homMackeyEquiv cC cD adj μ V' W' E (f ≫ HC.map (u₁ ×ₘ I.map u₂)) =
      homMackeyEquiv cC cD adj μ V W E f ≫ I.map (HD.map (R.op.map u₁ ×ₘ u₂)) := by
  rw [homMackeyEquiv_apply, homMackeyEquiv_apply, cC.equiv_symm_naturality_right,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    ← Category.assoc]
  have := μ.inv.naturality (𝟙 E ×ₘ u₁.unop)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, CategoryTheory.Functor.map_id] at this
  rw [← this, Category.assoc]
  have key := cD.equiv_naturality_right (R.obj E) (R.op.map u₁) u₂
    (μ.inv.app (E, V.unop) ≫ (adj.homEquiv _ _).symm ((cC.equiv E V _).symm f))
  simp only [CategoryTheory.Functor.op_map, Quiver.Hom.unop_op, Category.assoc] at key
  rw [key, Adjunction.homEquiv_naturality_right]
  rfl

/-- Abstract Hom Mackey isomorphism: `Hom(V, I W) ≅ I Hom(R V, W)`, natural in both. -/
def homMackeyIso :
    (𝟭 Cᵒᵖ).prod I ⋙ HC ≅ R.op.prod (𝟭 D) ⋙ HD ⋙ I :=
  Homomorphism.isoOfNaturalHomEquiv _ _
    (fun E j => homMackeyEquiv cC cD adj μ j.1 j.2 E)
    (fun {_ _} j h f => homMackeyEquiv_naturality_source cC cD adj μ j.1 j.2 h f)
    (fun E {_ _} u f => homMackeyEquiv_naturality_index cC cD adj μ u.1 u.2 E f)

end HomMackey

section TensorMackey

variable {P : D ⥤ C} {R : C ⥤ D} (adj : P ⊣ R) (ν : HC ⋙ R ≅ R.op.prod R ⋙ HD)

/-- The chain of bijections (III.2.11.6)–(III.2.11.10):
`Hom(P W ⊗ V, X) ≃ Hom(P(W ⊗ R V), X)`. -/
def tensorMackeyEquiv (W : D) (V : C) (X : C) :
    (TC.obj (P.obj W, V) ⟶ X) ≃ (P.obj (TD.obj (W, R.obj V)) ⟶ X) :=
  (cC.equiv (P.obj W) (op V) X).trans <|
    (adj.homEquiv _ _).trans <|
      (ν.app (op V, X)).homToEquiv.trans <|
        (cD.equiv W (R.op.obj (op V)) (R.obj X)).symm.trans (adj.homEquiv _ _).symm

theorem tensorMackeyEquiv_apply (W : D) (V : C) (X : C) (f : TC.obj (P.obj W, V) ⟶ X) :
    tensorMackeyEquiv cC cD adj ν W V X f =
      (adj.homEquiv _ _).symm ((cD.equiv W (R.op.obj (op V)) (R.obj X)).symm
        (adj.homEquiv _ _ (cC.equiv (P.obj W) (op V) X f) ≫ ν.hom.app (op V, X))) :=
  rfl

theorem tensorMackeyEquiv_naturality_target (W : D) (V : C) {X X' : C} (k : X ⟶ X')
    (f : TC.obj (P.obj W, V) ⟶ X) :
    tensorMackeyEquiv cC cD adj ν W V X' (f ≫ k) = tensorMackeyEquiv cC cD adj ν W V X f ≫ k := by
  rw [tensorMackeyEquiv_apply, tensorMackeyEquiv_apply]
  have h1 := cC.equiv_naturality_right (P.obj W) (𝟙 (op V)) k f
  simp only [unop_id, unop_op, ← prod_id, CategoryTheory.Functor.map_id, Category.id_comp] at h1
  rw [h1, Adjunction.homEquiv_naturality_right, Category.assoc]
  have := ν.hom.naturality (𝟙 (op V) ×ₘ k)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, CategoryTheory.Functor.map_id] at this
  rw [this, ← Category.assoc]
  have h2 := cD.equiv_symm_naturality_right W (𝟙 (R.op.obj (op V))) (R.map k)
    (adj.homEquiv _ _ (cC.equiv (P.obj W) (op V) X f) ≫ ν.hom.app (op V, X))
  simp only [unop_id, ← prod_id, CategoryTheory.Functor.map_id, Category.id_comp] at h2
  rw [h2, Adjunction.homEquiv_naturality_right_symm]

theorem tensorMackeyEquiv_naturality_index {W W' : D} {V V' : C} (a : W ⟶ W') (b : V ⟶ V')
    (X : C) (f : TC.obj (P.obj W', V') ⟶ X) :
    tensorMackeyEquiv cC cD adj ν W V X (TC.map (P.map a ×ₘ b) ≫ f) =
      P.map (TD.map (a ×ₘ R.map b)) ≫ tensorMackeyEquiv cC cD adj ν W' V' X f := by
  rw [tensorMackeyEquiv_apply]
  have h1 := cC.equiv_naturality (P.map a) b.op (𝟙 X) f
  simp only [Quiver.Hom.unop_op, Category.comp_id] at h1
  rw [h1, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have := ν.hom.naturality (b.op ×ₘ 𝟙 X)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map, CategoryTheory.Functor.map_id] at this
  rw [Category.assoc, Category.assoc, this]
  have h2 := cD.equiv_symm_naturality a (R.op.map b.op) (𝟙 (R.obj X))
    (adj.homEquiv _ _ (cC.equiv (P.obj W') (op V') X f) ≫ ν.hom.app (op V', X))
  simp only [Category.assoc, Category.comp_id] at h2
  rw [h2, Adjunction.homEquiv_naturality_left_symm]
  rfl

/-- Abstract tensor Mackey isomorphism: `P W ⊗ V ≅ P(W ⊗ R V)`, natural in both. -/
def tensorMackeyIso :
    P.prod (𝟭 C) ⋙ TC ≅ (𝟭 D).prod R ⋙ TD ⋙ P :=
  isoOfHomFromEquiv (fun j X => tensorMackeyEquiv cC cD adj ν j.1 j.2 X)
    (fun j _ _ k f => tensorMackeyEquiv_naturality_target cC cD adj ν j.1 j.2 k f)
    (fun u X f => tensorMackeyEquiv_naturality_index cC cD adj ν u.1 u.2 X f)

end TensorMackey

end Abstract

end Langlands.Hecke.Mackey
