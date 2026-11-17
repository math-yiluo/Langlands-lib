import Langlands.Algebra.AdicDiagonalAlgebraization
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Algebraization of compatible maps into group algebras -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.AdicGroupAlgebra

attribute [local instance] Classical.propDecidable

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {C : Type v} [CommRing C] [Algebra A C] {M : Type w} [AddCommGroup M]

/-- The coefficient linear map of an algebra map into a group algebra. -/
def coefficientLinearMap {Q : Type*} [CommRing Q] [Algebra A Q]
    (g : C →ₐ[A] AddMonoidAlgebra Q M) : C →ₗ[A] (M →₀ Q) :=
  (AddMonoidAlgebra.coeffLinearEquiv A).toLinearMap.comp g.toLinearMap

/-- The coefficient function of an algebra map into a group algebra. -/
def coefficientFunction {Q : Type*} [CommRing Q] [Algebra A Q]
    (g : C →ₐ[A] AddMonoidAlgebra Q M) : C →ₗ[A] (M → Q) :=
  (Finsupp.lcoeFun (R := A)).comp (coefficientLinearMap g)

@[simp] theorem coefficientLinearMap_apply {Q : Type*} [CommRing Q] [Algebra A Q]
    (g : C →ₐ[A] AddMonoidAlgebra Q M) (x : C) (m : M) :
    coefficientLinearMap g x m = (g x).coeff m := rfl

@[simp] theorem coefficientFunction_apply {Q : Type*} [CommRing Q] [Algebra A Q]
    (g : C →ₐ[A] AddMonoidAlgebra Q M) (x : C) (m : M) :
    coefficientFunction g x m = (g x).coeff m := rfl

/-- Coefficientwise reduction of the group algebra. -/
def reduce (n : ℕ) : AddMonoidAlgebra A M →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ n) M :=
  AddMonoidAlgebra.mapAlgHom M (Ideal.Quotient.mkₐ A (I ^ n))

@[simp] theorem reduce_coeff (n : ℕ) (x : AddMonoidAlgebra A M) (m : M) :
    (reduce I n x).coeff m = Ideal.Quotient.mk (I ^ n) (x.coeff m) := by
  simp [reduce]

/-- A group-algebra element is determined by all its adic reductions. -/
theorem eq_of_reduce_eq [IsHausdorff I A] {x y : AddMonoidAlgebra A M}
    (h : ∀ n : ℕ, reduce I n x = reduce I n y) : x = y := by
  ext m
  apply congrFun (IsHausdorff.funext' I
    (f := fun _ : Unit => x.coeff m) (g := fun _ : Unit => y.coeff m) ?_) ()
  intro n _
  simpa only [reduce_coeff] using congrArg (fun z => z.coeff m) (h n)

omit [AddCommGroup M] in
@[simp] theorem tensorEquiv_coeff_tmul (x y : AddMonoidAlgebra A M) (m k : M) :
    (AddMonoidAlgebra.tensorEquiv A (x ⊗ₜ[A] y)).coeff (m, k) =
      x.coeff m * y.coeff k := by
  simp [AddMonoidAlgebra.tensorEquiv]

/-- Matrix entries of the tensor of two coefficient maps. -/
theorem tensorEquiv_map_coeff (g : C →ₐ[A] AddMonoidAlgebra A M)
    (t : C ⊗[A] C) (m k : M) :
    (AddMonoidAlgebra.tensorEquiv A
      (TensorProduct.map g.toLinearMap g.toLinearMap t)).coeff (m, k) =
        AdicDiagonalAlgebraization.tensorCoefficient (coefficientFunction g) m k t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add t s ht hs => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ht, hs]

/-- The standard group-algebra coproduct is diagonal on coefficients. -/
theorem comul_coeff (x : AddMonoidAlgebra A M) (m k : M) :
    (AddMonoidAlgebra.tensorEquiv A (Coalgebra.comul (R := A) x)).coeff (m, k) =
      if m = k then x.coeff m else 0 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
      split_ifs <;> simp
  | single p a =>
      simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply,
        AddMonoidAlgebra.tensorEquiv_single_tmul_single, one_mul]
      by_cases hmk : m = k
      · subst k
        by_cases hpm : p = m <;> simp [hpm]
      · simp [hmk]
        by_cases hpm : p = m <;> by_cases hpk : p = k <;> simp_all

/-- Reduction commutes with the group-algebra counit. -/
theorem counit_reduce (n : ℕ) (x : AddMonoidAlgebra A M) :
    Coalgebra.counit (R := A ⧸ I ^ n) (reduce I n x) =
      Ideal.Quotient.mk (I ^ n) (Coalgebra.counit (R := A) x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp [reduce]

variable (d : C →ₗ[A] C ⊗[A] C)

/-- Compatible algebra maps satisfying the diagonal coproduct equations. -/
structure System where
  map : (n : ℕ) → C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ n) M
  compatible : ∀ {n k : ℕ} (h : n ≤ k) (x : C) (m : M),
    Ideal.Quotient.factorPow I h ((map k x).coeff m) = (map n x).coeff m
  diagonal : ∀ (n : ℕ) (x : C) (m k : M),
    AdicDiagonalAlgebraization.tensorCoefficient (coefficientFunction (map n)) m k (d x) =
      if m = k then (map n x).coeff m else 0

namespace System

variable {I d} (f : System I d (M := M))

/-- Forget the algebra structure and retain the compatible coefficient maps. -/
def toCoefficientSystem : AdicDiagonalAlgebraization.System I (C := C) (M := M) where
  map n := coefficientLinearMap (f.map n)
  compatible h x m := f.compatible h x m

variable [IsAdicComplete I A] [IsNoetherianRing A]

/-- The finite-support adic lift, viewed as a map into the group algebra. -/
def liftLinear : C →ₗ[A] AddMonoidAlgebra A M :=
  (AddMonoidAlgebra.coeffLinearEquiv A).symm.toLinearMap.comp
    (f.toCoefficientSystem.lift d f.diagonal)

@[simp] theorem mk_liftLinear_coeff (n : ℕ) (x : C) (m : M) :
    Ideal.Quotient.mk (I ^ n) ((f.liftLinear x).coeff m) = (f.map n x).coeff m :=
  f.toCoefficientSystem.mk_lift d f.diagonal n x m

@[simp] theorem reduce_liftLinear (n : ℕ) (x : C) :
    reduce I n (f.liftLinear x) = f.map n x := by
  ext m
  simp

/-- Algebraization of compatible diagonal algebra maps. -/
def liftAlgHom : C →ₐ[A] AddMonoidAlgebra A M :=
  AlgHom.ofLinearMap f.liftLinear
    (eq_of_reduce_eq I (fun n => by simp))
    (fun x y => eq_of_reduce_eq I (fun n => by simp))

@[simp] theorem liftAlgHom_apply (x : C) : f.liftAlgHom x = f.liftLinear x := rfl

@[simp] theorem reduce_liftAlgHom (n : ℕ) (x : C) :
    reduce I n (f.liftAlgHom x) = f.map n x := by
  simp

/-- The algebra map realizing the quotient system is unique. -/
theorem liftAlgHom_unique (g : C →ₐ[A] AddMonoidAlgebra A M)
    (hg : ∀ (n : ℕ) (x : C), reduce I n (g x) = f.map n x) : g = f.liftAlgHom := by
  apply AlgHom.ext
  intro x
  apply eq_of_reduce_eq I
  intro n
  rw [hg, reduce_liftAlgHom]

@[simp] theorem coefficientFunction_liftAlgHom :
    coefficientFunction f.liftAlgHom = f.toCoefficientSystem.coefficients := by
  apply LinearMap.ext
  intro x
  funext m
  rfl

/-- The algebraized map respects the supplied coproduct. -/
theorem map_d (x : C) :
    TensorProduct.map f.liftAlgHom.toLinearMap f.liftAlgHom.toLinearMap (d x) =
      Coalgebra.comul (R := A) (f.liftAlgHom x) := by
  apply (AddMonoidAlgebra.tensorEquiv A).injective
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro p
  rcases p with ⟨m, k⟩
  rw [tensorEquiv_map_coeff, comul_coeff, coefficientFunction_liftAlgHom,
    f.toCoefficientSystem.tensorCoefficient_diagonal d f.diagonal]
  rfl

/-- The counit equation also passes to the algebraized map. -/
theorem counit_liftAlgHom (e : C →ₗ[A] A)
    (he : ∀ (n : ℕ) (x : C), Coalgebra.counit (R := A ⧸ I ^ n) (f.map n x) =
      Ideal.Quotient.mk (I ^ n) (e x)) (x : C) :
    Coalgebra.counit (R := A) (f.liftAlgHom x) = e x := by
  apply congrFun (IsHausdorff.funext' I
    (f := fun _ : Unit => Coalgebra.counit (R := A) (f.liftAlgHom x))
    (g := fun _ : Unit => e x) ?_) ()
  intro n _
  rw [← counit_reduce, reduce_liftAlgHom, he]

end System

section Bialgebra

variable {D : Type v} [CommRing D] [Bialgebra A D]
variable [IsAdicComplete I A] [IsNoetherianRing A]
variable (f : System I (Coalgebra.comul (R := A) (A := D)) (M := M))
variable (he : ∀ (n : ℕ) (x : D), Coalgebra.counit (R := A ⧸ I ^ n) (f.map n x) =
  Ideal.Quotient.mk (I ^ n) (Coalgebra.counit (R := A) x))

/-- Algebraization as an actual bialgebra homomorphism. -/
def liftBialgHom : D →ₐc[A] AddMonoidAlgebra A M :=
  BialgHom.ofAlgHom f.liftAlgHom
    (AlgHom.ext (f.counit_liftAlgHom (Coalgebra.counit (R := A)) he))
    (AlgHom.ext f.map_d)

@[simp] theorem reduce_liftBialgHom (n : ℕ) (x : D) :
    reduce I n (liftBialgHom I f he x) = f.map n x :=
  f.reduce_liftAlgHom n x

/-- Uniqueness also holds among bialgebra homomorphisms. -/
theorem liftBialgHom_unique (g : D →ₐc[A] AddMonoidAlgebra A M)
    (hg : ∀ (n : ℕ) (x : D), reduce I n (g x) = f.map n x) :
    g = liftBialgHom I f he :=
  BialgHom.coe_toAlgHom_injective (f.liftAlgHom_unique g.toAlgHom hg)

end Bialgebra

end Langlands.AdicGroupAlgebra
