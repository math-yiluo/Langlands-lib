/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficients
public import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# The Čech complex of an injective presheaf with coefficients in an abelian category

Let `C` be a category, `V` an object of `C` such that `Over V` has finite products, `U₀` an
object of `Over V` and `A` an abelian category. We show that the Čech complex
`CategoryTheory.Presheaf.overCechComplex U₀` of an injective presheaf (or of an injective sheaf)
with values in `A` is exact in positive degrees.

The proof reduces to the case of abelian groups: a complex in `A` is exact as soon as all the
complexes of abelian groups obtained by applying the functors `Hom(a, -)` are exact, and
`Hom(a, -)` sends the Čech complex of `P` to the Čech complex of the abelian presheaf
`Hom(a, P(-))`. An injective presheaf `P` is a retract of the presheaf
`Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` (`CategoryTheory.Presheaf.piCofree`), which `Hom(a, -)` sends to the
cofree abelian presheaf `CategoryTheory.Presheaf.cofree`, whose Čech complex is exact.

## Main definitions

- `CategoryTheory.Presheaf.overCechComplexMapPreadditiveCoyonedaIso`: the isomorphism between
  `Hom(a, Č(U₀, P))` and the Čech complex of the abelian presheaf `Hom(a, P(-))`.
- `CategoryTheory.Presheaf.piCofree`: the presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)`.

## Main statements

- `CategoryTheory.Presheaf.exactAt_overCechComplex_of_forall_exactAt_cechComplex`: the Čech
  complex `Č(U₀, P)` is exact if all the Čech complexes of the abelian presheaves `Hom(a, P(-))`
  are exact.
- `CategoryTheory.Presheaf.exactAt_overCechComplex_of_injective`: the Čech complex of an
  injective presheaf is exact in positive degrees.
- `CategoryTheory.Sheaf.exactAt_overCechComplex_of_injective`: the Čech complex of an injective
  sheaf is exact in positive degrees.
-/

@[expose] public section

universe w v u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {A : Type u'} [Category.{max w v} A]

section Coyoneda

variable [Preadditive A] {V : C} [HasFiniteProducts (Over V)] (U₀ : Over V) (a : A)
  (P : Cᵒᵖ ⥤ A)

/-- The isomorphism between the morphisms from `a` to the term of degree `k` of the Čech
complex `Č(U₀, P)` and the Čech cochains of degree `k` with values in `Hom(a, P(-))`. -/
noncomputable def overCechComplexHomAddEquiv (k : ℕ) :
    (a ⟶ ((overCechComplex U₀).obj P).X k) ≃+
      CechCochain (fun _ : Fin 1 ↦ U₀) (P ⋙ preadditiveCoyoneda.obj (op a)) k where
  toFun f _ := f
  invFun c := c fun _ ↦ 0
  left_inv _ := rfl
  right_inv c := funext fun y ↦ by
    obtain rfl : y = fun _ ↦ 0 := Subsingleton.elim _ _
    rfl
  map_add' _ _ := rfl

/-- The functor `Hom(a, -)` sends the Čech complex `Č(U₀, P)` to the Čech complex of the
abelian presheaf `Hom(a, P(-))`. -/
noncomputable def overCechComplexMapPreadditiveCoyonedaIso :
    ((preadditiveCoyoneda.obj (op a)).mapHomologicalComplex _).obj ((overCechComplex U₀).obj P) ≅
      (cechComplex (fun _ : Fin 1 ↦ U₀)).obj (P ⋙ preadditiveCoyoneda.obj (op a)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (overCechComplexHomAddEquiv U₀ a P k).toAddCommGrpIso) (by
      rintro k _ rfl
      refine AddCommGrpCat.ext fun f ↦ funext fun y ↦ ?_
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, cechComplex_d_apply]
      refine Eq.trans ?_ (congrArg (f ≫ ·) (overCechComplex_obj_d U₀ P k)).symm
      rw [Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Preadditive.comp_zsmul]
      rfl)

end Coyoneda

/-! ### The cofree presheaf with values in `A` -/

section PiCofree

variable [HasProducts.{max w v} A] (P : Cᵒᵖ ⥤ A)

/-- The presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` with values in `A`, with restriction by
precomposition. It is the `A`-valued analogue of `CategoryTheory.Presheaf.cofree`. -/
@[simps]
noncomputable def piCofree : Cᵒᵖ ⥤ A where
  obj Y := ∏ᶜ fun x : Σ Z : C, (Z ⟶ Y.unop) ↦ P.obj (op x.1)
  map {Y Y'} h := Pi.lift fun x : Σ Z : C, (Z ⟶ Y'.unop) ↦
    Pi.π (fun x : Σ Z : C, (Z ⟶ Y.unop) ↦ P.obj (op x.1)) ⟨x.1, x.2 ≫ h.unop⟩
  map_id Y := Pi.hom_ext _ _ fun x ↦ by
    rw [Pi.lift_comp_π, unop_id, Category.comp_id, Category.id_comp]
  map_comp h h' := Pi.hom_ext _ _ fun x ↦ by
    rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π, unop_comp, Category.assoc]

/-- The embedding of a presheaf into `CategoryTheory.Presheaf.piCofree`, with components the
restrictions `P(g) : P(Y) ⟶ P(Z)` along all the morphisms `g : Z ⟶ Y`. -/
@[simps]
noncomputable def toPiCofree : P ⟶ piCofree P where
  app Y := Pi.lift fun x : Σ Z : C, (Z ⟶ Y.unop) ↦ P.map x.2.op
  naturality Y Y' h := Pi.hom_ext _ _ fun x ↦ by
    rw [Category.assoc, Pi.lift_comp_π, piCofree_map, Category.assoc, Pi.lift_comp_π,
      Pi.lift_comp_π, op_comp, Quiver.Hom.op_unop, P.map_comp]

instance : Mono (toPiCofree P) := by
  have (Y : Cᵒᵖ) : IsSplitMono ((toPiCofree P).app Y) :=
    IsSplitMono.mk' ⟨Pi.π (fun x : Σ Z : C, (Z ⟶ Y.unop) ↦ P.obj (op x.1)) ⟨Y.unop, 𝟙 _⟩, by
      rw [toPiCofree_app, Pi.lift_comp_π, op_id, P.map_id]⟩
  exact NatTrans.mono_of_mono_app _

variable [Preadditive A]

/-- The morphisms from `a` to `∏_{Z, g : Z ⟶ Y} P(Z)` are the families of morphisms
`a ⟶ P(Z)` indexed by the morphisms `g : Z ⟶ Y`. -/
noncomputable def piCofreeHomAddEquiv (a : A) (Y : Cᵒᵖ) :
    (a ⟶ (piCofree P).obj Y) ≃+ ∀ (Z : C) (_ : Z ⟶ Y.unop), a ⟶ P.obj (op Z) where
  toFun φ Z g := φ ≫ Pi.π (fun x : Σ Z : C, (Z ⟶ Y.unop) ↦ P.obj (op x.1)) ⟨Z, g⟩
  invFun c := Pi.lift fun x ↦ c x.1 x.2
  left_inv _ := Pi.hom_ext _ _ fun _ ↦ Pi.lift_comp_π _ _
  right_inv _ := funext fun _ ↦ funext fun _ ↦ Pi.lift_comp_π _ _
  map_add' _ _ := funext fun _ ↦ funext fun _ ↦ Preadditive.add_comp _ _ _ _ _ _

/-- The functor `Hom(a, -)` sends `CategoryTheory.Presheaf.piCofree P` to the cofree abelian
presheaf of `Hom(a, P(-))`. -/
noncomputable def piCofreeCompPreadditiveCoyonedaIso (a : A) :
    piCofree P ⋙ preadditiveCoyoneda.obj (op a) ≅ cofree (P ⋙ preadditiveCoyoneda.obj (op a)) :=
  NatIso.ofComponents (fun Y ↦ (piCofreeHomAddEquiv P a Y).toAddCommGrpIso) fun h ↦
    AddCommGrpCat.ext fun φ ↦ funext fun _ ↦ funext fun _ ↦ by
      exact (Category.assoc _ _ _).trans (congrArg (φ ≫ ·) (Pi.lift_comp_π _ _))

end PiCofree

/-! ### Exactness of the Čech complex of an injective presheaf -/

section Abelian

variable [Abelian A] {V : C} [HasFiniteProducts (Over V)] (U₀ : Over V) (P : Cᵒᵖ ⥤ A)

/-- The Čech complex `Č(U₀, P)` is exact at `n` if, for every object `a`, the Čech complex of the
abelian presheaf `Hom(a, P(-))` is exact at `n`. -/
theorem exactAt_overCechComplex_of_forall_exactAt_cechComplex (n : ℕ)
    (h : ∀ a : A,
      ((cechComplex (fun _ : Fin 1 ↦ U₀)).obj (P ⋙ preadditiveCoyoneda.obj (op a))).ExactAt n) :
    ((overCechComplex U₀).obj P).ExactAt n :=
  HomologicalComplex.exactAt_of_forall_exactAt_map_preadditiveCoyoneda _ n fun a ↦
    (h a).of_iso (overCechComplexMapPreadditiveCoyonedaIso U₀ a P).symm

/-- For an injective presheaf `P` with values in an abelian category and an object `a`, the
Čech complex of the abelian presheaf `Hom(a, P(-))` is exact in positive degrees: it is a
retract of the cofree abelian presheaf `Hom(a, piCofree P (-))`, whose Čech complex is exact. -/
theorem exactAt_cechComplex_comp_preadditiveCoyoneda_of_injective [HasProducts.{max w v} A]
    [Injective P] (a : A) (q : ℕ) :
    ((cechComplex (fun _ : Fin 1 ↦ U₀)).obj
      (P ⋙ preadditiveCoyoneda.obj (op a))).ExactAt (q + 1) := by
  let F := (Functor.whiskeringRight _ _ _).obj (preadditiveCoyoneda.obj (op a)) ⋙
    cechComplex (fun _ : Fin 1 ↦ U₀)
  refine HomologicalComplex.ExactAt.of_retraction (F.map (toPiCofree P))
    (F.map (Injective.factorThru (𝟙 P) (toPiCofree P))) ?_ ?_
  · rw [← F.map_comp, Injective.comp_factorThru, F.map_id]
  · exact (exactAt_cechComplex_cofree _ _ q).of_iso
      ((cechComplex _).mapIso (piCofreeCompPreadditiveCoyonedaIso P a)).symm

/-- The Čech complex of an injective presheaf with values in an abelian category is exact in
positive degrees (`exactAt_cechComplex_comp_preadditiveCoyoneda_of_injective`). -/
theorem exactAt_overCechComplex_of_injective [HasProducts.{max w v} A] [Injective P] (q : ℕ) :
    ((overCechComplex U₀).obj P).ExactAt (q + 1) :=
  exactAt_overCechComplex_of_forall_exactAt_cechComplex U₀ P _ fun a ↦
    exactAt_cechComplex_comp_preadditiveCoyoneda_of_injective U₀ P a q

end Abelian

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{max w v} A] [Abelian A] [HasProducts.{max w v} A] [HasSheafify J A]

/-- The Čech complex of an injective sheaf with values in an abelian category is exact in
positive degrees. -/
theorem exactAt_overCechComplex_of_injective {V : C} [HasFiniteProducts (Over V)] (U₀ : Over V)
    (I : Sheaf J A) [Injective I] (q : ℕ) :
    ((Presheaf.overCechComplex U₀).obj I.obj).ExactAt (q + 1) :=
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  Presheaf.exactAt_overCechComplex_of_injective U₀ I.obj q

/-- For an injective sheaf `I` with values in an abelian category and an object `a`, the Čech
complex of the abelian presheaf `Hom(a, I(-))` is exact in positive degrees. -/
theorem exactAt_cechComplex_comp_preadditiveCoyoneda_of_injective {V : C}
    [HasFiniteProducts (Over V)] (U₀ : Over V) (I : Sheaf J A) [Injective I] (a : A) (q : ℕ) :
    ((Presheaf.cechComplex (fun _ : Fin 1 ↦ U₀)).obj
      (I.obj ⋙ preadditiveCoyoneda.obj (op a))).ExactAt (q + 1) :=
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  Presheaf.exactAt_cechComplex_comp_preadditiveCoyoneda_of_injective U₀ I.obj a q

end CategoryTheory.Sheaf
