import Langlands.Algebra.RenardInvertibleEndomorphismCategory
import Langlands.Algebra.RenardLocalModuleFunctor
import Mathlib.CategoryTheory.Whiskering

/-! # Raised sources and the transported chosen endomorphism-localization arrow -/

set_option autoImplicit false

universe u v w

open CategoryTheory Polynomial Langlands.Algebra.PolynomialEndomorphism

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization.ChosenComparison

variable (R : Type u) [CommRing R]

/-- The exact published chosen localization followed by the restricted equivalence. -/
abbrev chosenFunctor :
    EndomorphismCat.{u, v} R ⥤ InvertibleEndomorphismCat.{u, max u v w} R :=
  toPolynomial R ⋙ ModuleLocalization.chosenLocalFunctor.{u, v, w} (powersX R) ⋙
    localFromPolynomial.{u, max u v w} R

/-- The specified chosen object is transported through the actual restricted functor. -/
theorem chosenFunctor_obj (A : EndomorphismCat.{u, v} R) :
    (chosenFunctor.{u, v, w} R).obj A =
      (localFromPolynomial R).obj
        (ModuleLocalization.canonicalLocalObject.{u, v, w} (powersX R)
          ((toPolynomial R).obj A)) := rfl

/-- Every chosen morphism is the published localized polynomial morphism. -/
theorem chosenFunctor_map {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    (chosenFunctor.{u, v, w} R).map f =
      (localFromPolynomial R).map
        (ModuleLocalization.chosenLocalMap.{u, v, w} (powersX R)
          ((toPolynomial R).map f)) := rfl

/-- The exact raised polynomial source, with polynomial scalars then restricted along constants. -/
abbrev polynomialRaisedFunctor : EndomorphismCat.{u, v} R ⥤ EndomorphismCat.{u, max u v w} R :=
  toPolynomial R ⋙ ModuleLocalization.sourceRaisingFunctor.{u, v, w} (R := R[X]) ⋙
    fromPolynomial R

/-- Raise the original module and its specified endomorphism directly. -/
def raisedFunctor : EndomorphismCat.{u, v} R ⥤ EndomorphismCat.{u, max u v w} R where
  obj A :=
    { a := ModuleCat.of R (ULift.{max u w} A.a)
      str := (ModuleCat.uliftFunctor.{max u w, v} R).map A.str }
  map {A B} f :=
    { f := (ModuleCat.uliftFunctor.{max u w, v} R).map f.f
      h := by
        ext x
        change B.str (f.f x.down) = f.f (A.str x.down)
        exact ((intertwining_iff R A B f.f).mp f.h x.down).symm }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem raisedFunctor_str (A : EndomorphismCat.{u, v} R)
    (x : ((raisedFunctor.{u, v, w} R).obj A).a) :
    ((raisedFunctor.{u, v, w} R).obj A).str x = ULift.up (A.str x.down) := rfl

@[simp] theorem raisedFunctor_map_apply {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B)
    (x : ((raisedFunctor.{u, v, w} R).obj A).a) :
    ((raisedFunctor.{u, v, w} R).map f).f x = ULift.up (f.f x.down) := rfl

/-- The AEval carrier identification, linear for the actual restricted constant action. -/
def sourceLinearEquiv (A : EndomorphismCat.{u, v} R) :
    ((raisedFunctor.{u, v, w} R).obj A).a ≃ₗ[R]
      ((polynomialRaisedFunctor.{u, v, w} R).obj A).a where
  toFun x := ULift.up (Module.AEval'.of (endomorphism R A) x.down)
  invFun x := ULift.up ((Module.AEval'.of (endomorphism R A)).symm x.down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by rfl
  map_smul' r x := by
    change ULift.up (Module.AEval'.of (endomorphism R A) (r • x.down)) =
      ULift.up ((C r : R[X]) • Module.AEval'.of (endomorphism R A) x.down)
    rw [toPolynomial_C_smul]

/-- The source comparison intertwines the raised operator with the actual lifted X-action. -/
theorem sourceLinearEquiv_intertwines (A : EndomorphismCat.{u, v} R)
    (x : ((raisedFunctor.{u, v, w} R).obj A).a) :
    sourceLinearEquiv.{u, v, w} R A (((raisedFunctor.{u, v, w} R).obj A).str x) =
      ((polynomialRaisedFunctor.{u, v, w} R).obj A).str
        (sourceLinearEquiv.{u, v, w} R A x) := by
  change ULift.up (Module.AEval'.of (endomorphism R A) (A.str x.down)) =
    ULift.up ((X : R[X]) • Module.AEval'.of (endomorphism R A) x.down)
  rw [toPolynomial_X_smul]

/-- The actual pair isomorphism beta at a source object. -/
def sourceIso (A : EndomorphismCat.{u, v} R) :
    (raisedFunctor.{u, v, w} R).obj A ≅ (polynomialRaisedFunctor.{u, v, w} R).obj A :=
  Endofunctor.Algebra.isoMk (sourceLinearEquiv.{u, v, w} R A).toModuleIso (by
    ext x
    exact (sourceLinearEquiv_intertwines R A x).symm)

/-- The AEval source comparison is natural for every original intertwiner. -/
def sourceComparison : raisedFunctor.{u, v, w} R ≅ polynomialRaisedFunctor.{u, v, w} R :=
  NatIso.ofComponents (sourceIso R) (fun _ => by ext x; rfl)

@[simp] theorem sourceComparison_hom_up (A : EndomorphismCat.{u, v} R) (x : A.a) :
    ((sourceComparison.{u, v, w} R).hom.app A).f (ULift.up x) =
      ULift.up (Module.AEval'.of (endomorphism R A) x) := rfl

@[simp] theorem sourceComparison_inv_up (A : EndomorphismCat.{u, v} R)
    (m : Module.AEval' (endomorphism R A)) :
    ((sourceComparison.{u, v, w} R).inv.app A).f (ULift.up m) =
      ULift.up ((Module.AEval'.of (endomorphism R A)).symm m) := rfl

@[simp] theorem sourceComparison_hom_inv (A : EndomorphismCat.{u, v} R) :
    (sourceComparison.{u, v, w} R).hom.app A ≫ (sourceComparison R).inv.app A =
      𝟙 ((raisedFunctor.{u, v, w} R).obj A) :=
  (sourceComparison R).hom_inv_id_app A

@[simp] theorem sourceComparison_inv_hom (A : EndomorphismCat.{u, v} R) :
    (sourceComparison.{u, v, w} R).inv.app A ≫ (sourceComparison R).hom.app A =
      𝟙 ((polynomialRaisedFunctor.{u, v, w} R).obj A) :=
  (sourceComparison R).inv_hom_id_app A

/-- Theta is the published canonical localization transformation, transported by fromPolynomial. -/
def polynomialArrow :
    polynomialRaisedFunctor.{u, v, w} R ⟶
      chosenFunctor.{u, v, w} R ⋙ invertibleEndomorphismInclusion R :=
  Functor.whiskerLeft (toPolynomial R)
    (Functor.whiskerRight (ModuleLocalization.chosenLocalizationUnit.{u, v, w} (powersX R))
      (fromPolynomial R))

/-- The transported component is precisely fromPolynomial applied to the chosen module map. -/
theorem polynomialArrow_app (A : EndomorphismCat.{u, v} R) :
    (polynomialArrow.{u, v, w} R).app A =
      (fromPolynomial R).map
        (ModuleLocalization.canonicalModuleMap.{u, v, w} (powersX R)
          ((toPolynomial R).obj A)) := rfl

@[simp] theorem polynomialArrow_up (A : EndomorphismCat.{u, v} R)
    (m : Module.AEval' (endomorphism R A)) :
    ((polynomialArrow.{u, v, w} R).app A).f (ULift.up m) =
      ULift.up (LocalizedModule.mk m 1) := rfl

/-- Lambda is the chosen arrow with its domain identified with the raised original pair. -/
def chosenArrow :
    raisedFunctor.{u, v, w} R ⟶
      chosenFunctor.{u, v, w} R ⋙ invertibleEndomorphismInclusion R :=
  (sourceComparison R).hom ≫ polynomialArrow R

@[simp] theorem chosenArrow_up (A : EndomorphismCat.{u, v} R) (x : A.a) :
    ((chosenArrow.{u, v, w} R).app A).f (ULift.up x) =
      ULift.up (LocalizedModule.mk (Module.AEval'.of (endomorphism R A) x) 1) := rfl

/-- Explicit naturality of the chosen arrow on every original linear intertwiner. -/
theorem chosenArrow_naturality {A B : EndomorphismCat.{u, v} R} (f : A ⟶ B) :
    (raisedFunctor.{u, v, w} R).map f ≫ (chosenArrow R).app B =
      (chosenArrow R).app A ≫
        (invertibleEndomorphismInclusion R).map ((chosenFunctor R).map f) :=
  (chosenArrow R).naturality f

/-- The exact chosen composite for arbitrary fields, with no dimension restriction. -/
abbrev fieldChosenFunctor (k : Type u) [Field k] :
    EndomorphismCat.{u, v} k ⥤ InvertibleEndomorphismCat.{u, max u v w} k :=
  chosenFunctor k

end Langlands.Renard.EndomorphismLocalization.ChosenComparison
