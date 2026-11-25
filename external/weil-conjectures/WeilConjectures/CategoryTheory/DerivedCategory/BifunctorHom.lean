/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# The derived hom of a bifunctor

Let `H : Aᵒᵖ ⥤ B ⥤ C` be a bifunctor between abelian categories, additive in each variable, with
`C` having countable products, and suppose that `A` has K-injective resolutions. For a cochain
complex `Y` in `B` this file defines the functor

`RHom_H(-, Y) : D(A)ᵒᵖ ⥤ D(C)`, `K ↦ bifunctorHomObj H K' Y`

where `K'` is a K-injective complex representing `K`
(`DerivedCategory.bifunctorRHomOfComplex`). It is well defined since the hom complex is
invariant under homotopies in the first variable
(`CochainComplex.bifunctorHomMapLeftHomotopy`) and the K-injective complexes, up to homotopy,
form a category equivalent to `D(A)` (`HomotopyCategory.KInjectives.Qh`). For `Y` a K-injective
complex representing an object `L` of `D(B)` this is the derived hom `RHom_H(-, L)`
(`DerivedCategory.bifunctorRHom`).

Replacing the first variable by a K-injective complex is a choice that makes the definition a
functor without any computation: that the hom complex into a K-injective complex sends
quasi-isomorphisms in the first variable to quasi-isomorphisms is not needed for the definition.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Abelian

namespace CochainComplex

variable {A B C : Type*} [Category A] [Category B] [Category C] [Abelian A] [Abelian B]
  [Abelian C] [HasCountableProducts C] [HasDerivedCategory C] (H : Aᵒᵖ ⥤ B ⥤ C)
  [∀ X, (H.obj X).Additive] [H.Additive]

/-- The hom complex `K ↦ bifunctorHomObj H K Y`, as a functor from cochain complexes to the
opposite of the derived category. -/
noncomputable def bifunctorHomComplexFunctor (Y : CochainComplex B ℤ) :
    CochainComplex A ℤ ⥤ (DerivedCategory C)ᵒᵖ where
  obj K := op (DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient _ _).obj (bifunctorHomObj H K Y)))
  map f := (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
    (bifunctorHomMapLeft f))).op
  map_id K := by
    rw [bifunctorHomMapLeft_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      op_id]
  map_comp f g := by
    rw [bifunctorHomMapLeft_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, op_comp]

/-- The hom complex `K ↦ bifunctorHomObj H K Y`, as a functor from the homotopy category to the
opposite of the derived category. -/
noncomputable def bifunctorHomHomotopyFunctor (Y : CochainComplex B ℤ) :
    HomotopyCategory A (.up ℤ) ⥤ (DerivedCategory C)ᵒᵖ :=
  CategoryTheory.Quotient.lift _ (bifunctorHomComplexFunctor H Y) (fun _ _ _ _ ⟨h⟩ ↦ by
    simp only [bifunctorHomComplexFunctor,
      HomotopyCategory.eq_of_homotopy _ _ (bifunctorHomMapLeftHomotopy h)])

@[simp]
lemma bifunctorHomHomotopyFunctor_obj (Y : CochainComplex B ℤ) (K : CochainComplex A ℤ) :
    (bifunctorHomHomotopyFunctor H Y).obj ((HomotopyCategory.quotient _ _).obj K) =
      op (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj (bifunctorHomObj H K Y))) :=
  rfl

@[simp]
lemma bifunctorHomHomotopyFunctor_map (Y : CochainComplex B ℤ) {K K' : CochainComplex A ℤ}
    (f : K ⟶ K') :
    (bifunctorHomHomotopyFunctor H Y).map ((HomotopyCategory.quotient _ _).map f) =
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (bifunctorHomMapLeft f))).op :=
  rfl

end CochainComplex

namespace DerivedCategory

open CochainComplex

variable {A B C : Type*} [Category A] [Category B] [Category C] [Abelian A] [Abelian B]
  [Abelian C] [HasCountableProducts C] [HasDerivedCategory A] [HasDerivedCategory C]
  [HasKInjectiveResolutions A] (H : Aᵒᵖ ⥤ B ⥤ C) [∀ X, (H.obj X).Additive] [H.Additive]

/-- The derived hom `RHom_H(-, Y) : D(A)ᵒᵖ ⥤ D(C)` into a fixed cochain complex `Y`: an object of
`D(A)` is represented by a K-injective complex `K`, unique up to homotopy equivalence, and sent
to the hom complex `bifunctorHomObj H K Y`. -/
noncomputable def bifunctorRHomOfComplex (Y : CochainComplex B ℤ) :
    (DerivedCategory A)ᵒᵖ ⥤ DerivedCategory C :=
  ((HomotopyCategory.KInjectives.Qh (C := A)).inv ⋙ HomotopyCategory.KInjectives.ι ⋙
    bifunctorHomHomotopyFunctor H Y).leftOp

/-- On a K-injective complex `K`, the derived hom is the hom complex. -/
noncomputable def bifunctorRHomOfComplexObjIso (Y : CochainComplex B ℤ)
    (K : CochainComplex A ℤ) [K.IsKInjective] :
    (bifunctorRHomOfComplex H Y).obj (op (Q.obj K)) ≅ Q.obj (bifunctorHomObj H K Y) :=
  ((bifunctorHomHomotopyFunctor H Y).mapIso (HomotopyCategory.KInjectives.ι.mapIso
    ((HomotopyCategory.KInjectives.Qh (C := A)).inv.mapIso ((quotientCompQhIso A).app K).symm ≪≫
      ((HomotopyCategory.KInjectives.Qh (C := A)).asEquivalence.unitIso.app
        (HomotopyCategory.KInjectives.mk K)).symm))).symm.unop ≪≫
    (quotientCompQhIso C).app _

variable [HasDerivedCategory B] [HasKInjectiveResolutions B]

/-- A K-injective complex representing an object `L` of `D(B)`. -/
noncomputable def kInjectiveRep (L : DerivedCategory B) : CochainComplex B ℤ :=
  (exists_iso_Q_obj_of_isKInjective L).choose

instance (L : DerivedCategory B) : (kInjectiveRep L).IsKInjective :=
  (exists_iso_Q_obj_of_isKInjective L).choose_spec.choose

/-- The K-injective complex `kInjectiveRep L` represents `L`. -/
noncomputable def kInjectiveRepIso (L : DerivedCategory B) : L ≅ Q.obj (kInjectiveRep L) :=
  (exists_iso_Q_obj_of_isKInjective L).choose_spec.choose_spec.some

/-- The derived hom `RHom_H(-, L) : D(A)ᵒᵖ ⥤ D(C)` into an object `L` of `D(B)`, computed by the
hom complex between K-injective complexes representing the two variables. -/
noncomputable def bifunctorRHom (L : DerivedCategory B) :
    (DerivedCategory A)ᵒᵖ ⥤ DerivedCategory C :=
  bifunctorRHomOfComplex H (kInjectiveRep L)

end DerivedCategory
