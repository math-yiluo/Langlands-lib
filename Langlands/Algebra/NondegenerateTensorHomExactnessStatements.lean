import Langlands.Algebra.NonUnitalModuleTensor
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.Renard.HomExactnessComparisonStatements
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Renard I.2.2: exactness of the tensor and Hom functors on nondegenerate modules

Renard (9 July 2026), I.2.2, the Proposition on printed p.15 / PDF21. The functor
`• ⊗_A X : M(A)_d → ℤ-mod` below is a helper construction on the published balanced tensor;
the Hom functors are the published integer-module-valued Hom functors of A.VIII.2 on `M(A)`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra.NondegenerateTensorHomExactness

universe uA uX uY uM

section Functor

variable (A : Type uA) [NonUnitalRing A] (X : Type uX) [AddCommGroup X] [NonUnitalModule A X]

/-- Renard's `• ⊗_A X : M(A)_d → ℤ-mod` for a left module `X`: a nondegenerate right module `Y`
goes to the published balanced tensor `Y ⊗_A X`, and `f : Y ⟶ Y'` to `f ⊗ id_X`. -/
def tensorFunctor : NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ ⥤ ModuleCat.{max uY uX} ℤ where
  obj Y := ModuleCat.of ℤ (NonUnitalModuleTensor.Tensor A Y.obj X)
  map f := ModuleCat.ofHom
    (NonUnitalModuleTensor.map A f.hom (NonUnitalModuleHom.id A X)).toIntLinearMap
  map_id Y := by
    ext t
    exact DFunLike.congr_fun (NonUnitalModuleTensor.map_id A (X := Y.obj) (Y := X)) t
  map_comp f g := by
    ext t
    exact (DFunLike.congr_fun (NonUnitalModuleTensor.map_comp A f.hom
      (NonUnitalModuleHom.id A X) g.hom (NonUnitalModuleHom.id A X)) t).symm

@[simp] theorem tensorFunctor_obj (Y : NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ) :
    (tensorFunctor A X).obj Y = ModuleCat.of ℤ (NonUnitalModuleTensor.Tensor A Y.obj X) := rfl

theorem tensorFunctor_map_hom {Y Y' : NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ} (f : Y ⟶ Y') :
    ((tensorFunctor A X).map f).hom =
      (NonUnitalModuleTensor.map A f.hom (NonUnitalModuleHom.id A X)).toIntLinearMap := rfl

/-- `f ↦ f ⊗ id_X` is additive. -/
theorem map_add_id {Y Y' : NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ} (f g : Y ⟶ Y') :
    NonUnitalModuleTensor.map A (f + g).hom (NonUnitalModuleHom.id A X) =
      NonUnitalModuleTensor.map A f.hom (NonUnitalModuleHom.id A X) +
        NonUnitalModuleTensor.map A g.hom (NonUnitalModuleHom.id A X) :=
  NonUnitalModuleTensor.hom_ext A (X := Y.obj) (Y := X) (fun _ x =>
    NonUnitalModuleTensor.add_tmul A Y'.obj X _ _ x)

instance tensorFunctor_additive : (tensorFunctor.{uA, uX, uY} A X).Additive where
  map_add {_ _} f g := by
    ext t
    exact DFunLike.congr_fun (map_add_id A X f g) t

end Functor

/-- Renard I.2.2, Proposition, first line: for an idempotented ring `A` and a nondegenerate left
module `X`, the covariant functor `• ⊗_A X` on nondegenerate right modules is right exact. -/
def TensorRightExactStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (X : Type uX) [AddCommGroup X] [NonUnitalModule A X] (_hX : IsNondegenerate A X),
    letI := NondegenerateModuleCat.abelian.{uA, uY} Aᵐᵒᵖ hA.op
    Langlands.Renard.SequenceRightExact (tensorFunctor.{uA, uX, uY} A X)

/-- Renard I.2.2, Proposition, second line: for idempotented `A` and a nondegenerate module `X`,
the contravariant functor `Hom_A(•, X)` on `M(A)` is left exact. -/
def ContravariantHomLeftExactStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (X : NondegenerateModuleCat.{uA, uM} A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    Langlands.Renard.ContravariantSequenceLeftExact
      (Langlands.CategoryTheory.Renard.preadditiveYonedaInt X)

/-- Renard I.2.2, Proposition, third line: for idempotented `A` and a nondegenerate module `X`,
the covariant functor `Hom_A(X, •)` on `M(A)` is left exact. -/
def CovariantHomLeftExactStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (X : NondegenerateModuleCat.{uA, uM} A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    Langlands.Renard.SequenceLeftExact
      (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt X)

/-- The Proposition of I.2.2: its three lines together. -/
def Statements : Prop :=
  TensorRightExactStatement.{uA, uX, uY} ∧ ContravariantHomLeftExactStatement.{uA, uM} ∧
    CovariantHomLeftExactStatement.{uA, uM}

end Langlands.Algebra.NondegenerateTensorHomExactness
