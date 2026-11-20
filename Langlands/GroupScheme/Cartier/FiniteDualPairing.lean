import Langlands.GroupScheme.Cartier.FiniteDualAlgebra
import Langlands.TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Mathlib.Algebra.Group.Units.Hom

/-! # The character pairing on affine algebra points -/

noncomputable section

open Module TensorProduct WithConv Coalgebra
open scoped TensorProduct

namespace Langlands.GroupScheme.Cartier.FiniteDual

section Coefficients

variable (R A C : Type*) [CommRing R] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R C] [Module.Finite R A] [Module.Projective R A]

/-- Coefficient tensors represent linear maps from the convolution dual. -/
def coefficients : A ⊗[R] C ≃ₗ[R] (Dual R A →ₗ[R] C) :=
  (TensorProduct.congr ((bidualLinear R A).trans (WithConv.linearEquiv R _))
    (LinearEquiv.refl R C)).trans (dualTensorHomEquiv R (Dual R A) C)

variable {R A C}

@[simp] theorem coefficients_tmul (a : A) (c : C) (f : Dual R A) :
    coefficients R A C (a ⊗ₜ[R] c) f = f a • c := by
  simp [coefficients]

theorem coefficients_ext {t s : A ⊗[R] C}
    (h : ∀ f : Dual R A, coefficients R A C t f = coefficients R A C s f) :
    t = s :=
  (coefficients R A C).injective (LinearMap.ext h)

variable {B : Type*} [CommRing B] [Algebra R B]

@[simp] theorem coefficients_map (h : C →ₐ[R] B) (t : A ⊗[R] C) (f : Dual R A) :
    coefficients R A B (Algebra.TensorProduct.map (AlgHom.id R A) h t) f =
      h (coefficients R A C t f) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add t s ht hs => simp [ht, hs]

theorem coefficients_symm_map (h : C →ₐ[R] B) (y : Dual R A →ₗ[R] C) :
    (coefficients R A B).symm (h.toLinearMap.comp y) =
      Algebra.TensorProduct.map (AlgHom.id R A) h ((coefficients R A C).symm y) := by
  apply coefficients_ext
  intro f
  simp

end Coefficients

section GroupLike

variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
  [Bialgebra R A] [Algebra R C] [Module.Finite R A] [Module.Projective R A]

/-- Evaluation of a coefficient tensor at a point. -/
def evalTensor (x : A →ₐ[R] C) : A ⊗[R] C →ₐ[R] C :=
  Algebra.TensorProduct.lift x (AlgHom.id R C) fun _ _ => Commute.all _ _

omit [Module.Finite R A] [Module.Projective R A] in
@[simp] theorem evalTensor_tmul (x : A →ₐ[R] C) (a : A) (c : C) :
    evalTensor x (a ⊗ₜ[R] c) = x a * c := rfl

omit [Module.Finite R A] [Module.Projective R A] in
theorem evalTensor_postcomp {B : Type*} [CommRing B] [Algebra R B] (h : C →ₐ[R] B)
    (x : A →ₐ[R] C) (t : A ⊗[R] C) :
    evalTensor (h.comp x) (Algebra.TensorProduct.map (AlgHom.id R A) h t) =
      h (evalTensor x t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add t s ht hs => simp [ht, hs]

variable (R A C)

/-- Comultiplication on the coordinate algebra with coefficients in `C`. -/
def Δ : A ⊗[R] C →ₐ[R] (A ⊗[R] A) ⊗[R] C :=
  Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A) (AlgHom.id R C)

/-- The first coordinate pullback on the tensor product with coefficients. -/
def incl₁ : A ⊗[R] C →ₐ[R] (A ⊗[R] A) ⊗[R] C :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft (AlgHom.id R C)

/-- The second coordinate pullback on the tensor product with coefficients. -/
def incl₂ : A ⊗[R] C →ₐ[R] (A ⊗[R] A) ⊗[R] C :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id R C)

variable {R A C}

/-- The two equations for a group-like coefficient, written as coordinate pullbacks. -/
def IsGroupLikeCoeff (t : A ⊗[R] C) : Prop :=
  evalTensor (1 : WithConv (A →ₐ[R] C)).ofConv t = 1 ∧
    Δ R A C t = incl₁ R A C t * incl₂ R A C t

@[simp] theorem evalTensor_one (t : A ⊗[R] C) :
    evalTensor (1 : WithConv (A →ₐ[R] C)).ofConv t =
      coefficients R A C t (1 : Dual R A) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [AlgHom.convOne_def, Algebra.smul_def]
  | add t s ht hs => simp [ht, hs]

private def test (t : (A ⊗[R] A) ⊗[R] C) (f g : Dual R A) : C :=
  coefficients R (A ⊗[R] A) C t (toConv (tensorDual (f ⊗ₜ[R] g)))

private theorem test_ext {t s : (A ⊗[R] A) ⊗[R] C}
    (h : ∀ f g : Dual R A, test t f g = test s f g) :
    t = s := by
  apply coefficients_ext
  intro z
  let e : Dual R A ⊗[R] Dual R A ≃ₗ[R] Dual R (A ⊗[R] A) :=
    tensorDual.trans (WithConv.linearEquiv R _).symm
  have he : (coefficients R (A ⊗[R] A) C t).comp e.toLinearMap =
      (coefficients R (A ⊗[R] A) C s).comp e.toLinearMap :=
    TensorProduct.ext' fun f g => h f g
  obtain ⟨p, rfl⟩ := e.surjective z
  exact LinearMap.congr_fun he p

private theorem test_Δ (t : A ⊗[R] C) (f g : Dual R A) :
    test (Δ R A C t) f g = coefficients R A C t (f * g) := by
  have h : tensorDual (f ⊗ₜ[R] g) = (WithConv.mulTensor f g).ofConv :=
    TensorProduct.ext' fun a b => by simp
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    simp only [test, Δ, Algebra.TensorProduct.map_tmul, Bialgebra.comulAlgHom_apply,
      AlgHom.id_apply, coefficients_tmul, ofConv_toConv, h, WithConv.mulTensor,
      LinearMap.comp_apply, LinearMap.convMul_apply]
  | add t s ht hs =>
    simp only [test, map_add, LinearMap.add_apply] at ht hs ⊢
    rw [ht, hs]

private theorem test_mul (t s : A ⊗[R] C) (f g : Dual R A) :
    test (incl₁ R A C t * incl₂ R A C s) f g =
      coefficients R A C t f * coefficients R A C s g := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    induction s using TensorProduct.inductionOn with
    | tmul b d =>
      simp [test, incl₁, incl₂, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def,
        mul_mul_mul_comm]
    | add s t hs ht =>
      simp only [test, map_add, mul_add, LinearMap.add_apply] at hs ht ⊢
      rw [hs, ht]
  | add t u ht hu =>
    simp only [test, map_add, add_mul, LinearMap.add_apply] at ht hu ⊢
    rw [ht, hu]

/-- The coefficient equations express that the associated linear map is an algebra map. -/
theorem isGroupLikeCoeff_iff (t : A ⊗[R] C) :
    IsGroupLikeCoeff t ↔ coefficients R A C t (1 : Dual R A) = 1 ∧
      ∀ f g : Dual R A, coefficients R A C t (f * g) =
        coefficients R A C t f * coefficients R A C t g := by
  simp only [IsGroupLikeCoeff, evalTensor_one]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun f g => ?_⟩
    rw [← test_Δ, h₂, test_mul]
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, test_ext fun f g => ?_⟩
    rw [test_Δ, test_mul, h₂]

/-- The algebra map associated with a group-like coefficient tensor. -/
def algHomOfCoeff (t : A ⊗[R] C) (h : IsGroupLikeCoeff t) : Dual R A →ₐ[R] C :=
  AlgHom.ofLinearMap (coefficients R A C t)
    ((isGroupLikeCoeff_iff t).mp h).1 ((isGroupLikeCoeff_iff t).mp h).2

@[simp] theorem algHomOfCoeff_toLinearMap (t : A ⊗[R] C) (h : IsGroupLikeCoeff t) :
    (algHomOfCoeff t h).toLinearMap = coefficients R A C t := rfl

theorem isGroupLikeCoeff_symm (y : Dual R A →ₐ[R] C) :
    IsGroupLikeCoeff ((coefficients R A C).symm y.toLinearMap) := by
  rw [isGroupLikeCoeff_iff, LinearEquiv.apply_symm_apply]
  exact ⟨map_one y, map_mul y⟩

end GroupLike

section Pairing

open Algebra.TensorProduct (productMap)

variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
  [HopfAlgebra R A] [Algebra R C] [Module.Finite R A] [Module.Projective R A]

omit [Module.Finite R A] [Module.Projective R A] in
theorem evalTensor_mul (x z : WithConv (A →ₐ[R] C)) (t : A ⊗[R] C) :
    evalTensor (x * z).ofConv t =
      evalTensor (productMap x.ofConv z.ofConv) (Δ R A C t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [Δ, AlgHom.convMul_def, Algebra.TensorProduct.productMap_eq_comp_map]
  | add t s ht hs => simp [ht, hs]

omit [Module.Finite R A] [Module.Projective R A] in
@[simp] theorem evalTensor_incl₁ (x z : A →ₐ[R] C) (t : A ⊗[R] C) :
    evalTensor (productMap x z) (incl₁ R A C t) = evalTensor x t := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [incl₁]
  | add t s ht hs => simp [ht, hs]

omit [Module.Finite R A] [Module.Projective R A] in
@[simp] theorem evalTensor_incl₂ (x z : A →ₐ[R] C) (t : A ⊗[R] C) :
    evalTensor (productMap x z) (incl₂ R A C t) = evalTensor z t := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp [incl₂]
  | add t s ht hs => simp [ht, hs]

/-- A point of the dual algebra determines a character of the original point group. -/
def pointCharacter (y : WithConv (Dual R A →ₐ[R] C)) :
    WithConv (A →ₐ[R] C) →* Cˣ := by
  let t := (coefficients R A C).symm y.ofConv.toLinearMap
  have ht := isGroupLikeCoeff_symm y.ofConv
  let f : WithConv (A →ₐ[R] C) →* C :=
    { toFun := fun x => evalTensor x.ofConv t
      map_one' := ht.1
      map_mul' := fun x z => by
        change evalTensor (x * z).ofConv t = evalTensor x.ofConv t * evalTensor z.ofConv t
        rw [evalTensor_mul, ht.2, map_mul, evalTensor_incl₁, evalTensor_incl₂] }
  exact MonoidHom.toHomUnits (G := WithConv (A →ₐ[R] C)) (M := C) f

@[simp] theorem pointCharacter_val (y : WithConv (Dual R A →ₐ[R] C))
    (x : WithConv (A →ₐ[R] C)) :
    (pointCharacter y x : C) = evalTensor x.ofConv ((coefficients R A C).symm y.ofConv.toLinearMap) :=
  rfl

/-- The value after extending coefficients is obtained by evaluating the same tensor. -/
theorem pointCharacter_baseChange_val {B : Type*} [CommRing B] [Algebra R B] (h : C →ₐ[R] B)
    (y : WithConv (Dual R A →ₐ[R] C)) (x : WithConv (A →ₐ[R] B)) :
    (pointCharacter (toConv (h.comp y.ofConv)) x : B) =
      productMap x.ofConv h ((coefficients R A C).symm y.ofConv.toLinearMap) := by
  simp only [pointCharacter_val, AlgHom.comp_toLinearMap, coefficients_symm_map]
  generalize (coefficients R A C).symm y.ofConv.toLinearMap = t
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add t s ht hs => simp [ht, hs]

theorem pointCharacter_postcomp {B : Type*} [CommRing B] [Algebra R B] (h : C →ₐ[R] B)
    (y : WithConv (Dual R A →ₐ[R] C)) (x : WithConv (A →ₐ[R] C)) :
    pointCharacter (toConv (h.comp y.ofConv)) (toConv (h.comp x.ofConv)) =
      Units.map h.toMonoidHom (pointCharacter y x) := by
  apply Units.ext
  change evalTensor (h.comp x.ofConv) ((coefficients R A B).symm (h.comp y.ofConv).toLinearMap) =
    h (evalTensor x.ofConv ((coefficients R A C).symm y.ofConv.toLinearMap))
  rw [AlgHom.comp_toLinearMap, coefficients_symm_map, evalTensor_postcomp]

variable [Coalgebra.IsCocomm R A]

private def universalTensor (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] [Coalgebra.IsCocomm R A] : A ⊗[R] Dual R A :=
  (coefficients R A (Dual R A)).symm LinearMap.id

@[simp] private theorem coefficients_universalTensor (f : Dual R A) :
    coefficients R A (Dual R A) (universalTensor R A) f = f := by
  simp [universalTensor]

private theorem pointCharacter_productMap (y : WithConv (Dual R A →ₐ[R] C))
    (x : WithConv (A →ₐ[R] C)) :
    (pointCharacter y x : C) = productMap x.ofConv y.ofConv (universalTensor R A) := by
  have ht : (coefficients R A C).symm y.ofConv.toLinearMap =
      Algebra.TensorProduct.map (AlgHom.id R A) y.ofConv (universalTensor R A) := by
    apply coefficients_ext
    intro f
    simp
  rw [pointCharacter_val, ht]
  generalize universalTensor R A = t
  induction t using TensorProduct.inductionOn with
  | tmul a f => simp
  | add t s ht hs => simp [ht, hs]

private theorem universalTensor_bidual :
    universalTensor R (Dual R A) =
      Algebra.TensorProduct.map (AlgHom.id R (Dual R A)) (bidualEquiv R A).toAlgEquiv.toAlgHom
        (TensorProduct.comm R A (Dual R A) (universalTensor R A)) := by
  let l : A ⊗[R] Dual R A →ₗ[R] Dual R A ⊗[R] Dual R (Dual R A) :=
    (Algebra.TensorProduct.map (AlgHom.id R (Dual R A))
      (bidualEquiv R A).toAlgEquiv.toAlgHom).toLinearMap.comp
        (TensorProduct.comm R A (Dual R A)).toLinearMap
  change universalTensor R (Dual R A) = l (universalTensor R A)
  apply coefficients_ext
  intro g
  apply WithConv.ext
  apply LinearMap.ext
  intro f
  have h (t : A ⊗[R] Dual R A) :
      (coefficients R (Dual R A) _ (l t) g).ofConv f =
        g.ofConv (coefficients R A (Dual R A) t f) := by
    induction t using TensorProduct.inductionOn with
    | tmul a k => simp [l, smul_eq_mul, mul_comm]
    | add t s ht hs =>
      rw [l.map_add, (coefficients R (Dual R A) (Dual R (Dual R A))).map_add,
        (coefficients R A (Dual R A)).map_add]
      simp only [LinearMap.add_apply, ofConv_add, map_add]
      rw [ht, hs]
  simpa only [coefficients_universalTensor] using (h (universalTensor R A)).symm

/-- Evaluation is symmetric under the canonical identification with the double dual. -/
theorem pointCharacter_bidual (y : WithConv (Dual R A →ₐ[R] C))
    (x : WithConv (A →ₐ[R] C)) :
    pointCharacter (A := Dual R A)
      (toConv (x.ofConv.comp (bidualEquiv R A).symm.toAlgEquiv.toAlgHom)) y =
        pointCharacter y x := by
  apply Units.ext
  rw [pointCharacter_productMap, pointCharacter_productMap, universalTensor_bidual]
  generalize universalTensor R A = t
  induction t using TensorProduct.inductionOn with
  | tmul a f => simp [AlgHom.comp_apply, mul_comm]
  | add t s ht hs => simp [ht, hs]

/-- The pairing is multiplicative in the dual point. -/
theorem pointCharacter_mul (y z : WithConv (Dual R A →ₐ[R] C))
    (x : WithConv (A →ₐ[R] C)) :
    pointCharacter (y * z) x = pointCharacter y x * pointCharacter z x := by
  rw [← pointCharacter_bidual (y * z) x, ← pointCharacter_bidual y x,
    ← pointCharacter_bidual z x, map_mul]

@[simp] theorem pointCharacter_one (x : WithConv (A →ₐ[R] C)) :
    pointCharacter (1 : WithConv (Dual R A →ₐ[R] C)) x = 1 := by
  rw [← pointCharacter_bidual (1 : WithConv (Dual R A →ₐ[R] C)) x, map_one]

end Pairing

end Langlands.GroupScheme.Cartier.FiniteDual
