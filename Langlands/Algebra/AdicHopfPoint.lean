import Langlands.Algebra.AdicGroupAlgebra
import Langlands.Algebra.HopfPointBridge

/-! # Adic algebraization in the existing Hopf-point coordinates -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.AdicHopfPoint

open Langlands.Algebra.HopfPointExtension

attribute [local instance] Classical.propDecidable

variable {A : Type u} [CommRing A] {C : Type v} [CommRing C] [Bialgebra A C]
variable {M : Type w} [AddCommGroup M] {Q : Type*} [CommRing Q] [Algebra A Q]

/-- The two inclusions of group algebras multiply to the tensor-coordinate map. -/
theorem inl_mul_inr (x y : AddMonoidAlgebra Q M) :
    inlMap A Q M x * inrMap A Q M y = AddMonoidAlgebra.tensorEquiv Q (x ⊗ₜ[Q] y) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, add_mul, TensorProduct.add_tmul, hx, hx']
  | single m a =>
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, mul_add, TensorProduct.tmul_add, hy, hy']
      | single k b => simp [inlMap, inrMap, AddMonoidAlgebra.single_mul_single]

/-- The pair map is the tensor coefficient pairing. -/
theorem pairMap_coeff (f : C →ₐ[A] AddMonoidAlgebra Q M) (t : C ⊗[A] C) (m k : M) :
    (pairMap f t).coeff (m, k) = AdicDiagonalAlgebraization.tensorCoefficient
      (AdicGroupAlgebra.coefficientFunction f) m k t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [pairMap, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      rw [inl_mul_inr, AdicGroupAlgebra.tensorEquiv_coeff_tmul]
      rfl
  | add t s ht hs =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ht, hs]

/-- The diagonal group-algebra map has exactly the expected diagonal coefficients. -/
theorem diagMap_coeff (x : AddMonoidAlgebra Q M) (m k : M) :
    (diagMap A Q M x).coeff (m, k) = if m = k then x.coeff m else 0 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
      split_ifs <;> simp
  | single p a =>
      by_cases hmk : m = k
      · subst k
        by_cases hpm : p = m <;> simp [diagMap, hpm]
      · by_cases hpm : p = m <;> by_cases hpk : p = k <;> simp_all [diagMap]

/-- The Hopf-point counit agrees with the standard group-algebra counit. -/
theorem groupCounit_eq (x : AddMonoidAlgebra Q M) :
    groupCounit A Q M x = Coalgebra.counit (R := Q) x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp [groupCounit, AddMonoidAlgebra.lift_single]

/-- A Hopf point supplies the diagonal coefficient identities. -/
theorem diagonal (f : C →ₐ[A] AddMonoidAlgebra Q M) (hf : IsHopfPoint f)
    (x : C) (m k : M) :
    AdicDiagonalAlgebraization.tensorCoefficient (AdicGroupAlgebra.coefficientFunction f)
      m k (Coalgebra.comul (R := A) x) = if m = k then (f x).coeff m else 0 := by
  rw [← pairMap_coeff]
  have h := congrArg (fun g : C →ₐ[A] AddMonoidAlgebra Q (M × M) => (g x).coeff (m, k)) hf.comul
  exact h.trans (diagMap_coeff (A := A) (f x) m k)

/-- A Hopf point supplies the scalar counit equation. -/
theorem counit (f : C →ₐ[A] AddMonoidAlgebra Q M) (hf : IsHopfPoint f) (x : C) :
    Coalgebra.counit (R := Q) (f x) = algebraMap A Q (Coalgebra.counit (R := A) x) := by
  rw [← groupCounit_eq (A := A)]
  exact congrArg (fun g : C →ₐ[A] Q => g x) hf.counit

variable (I : Ideal A)

/-- Compatible Hopf points in group-algebra coordinates. -/
structure System where
  map (n : ℕ) : C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ n) M
  hopf (n : ℕ) : IsHopfPoint (map n)
  compatible : ∀ {n k : ℕ} (h : n ≤ k) (x : C) (m : M),
    Ideal.Quotient.factorPow I h ((map k x).coeff m) = (map n x).coeff m

namespace System

variable {I} (f : System I (C := C) (M := M))

/-- Extend a successive positive-power Hopf-point family over the zero quotient. -/
def ofSucc
    (F : (n : ℕ) → C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M)
    (hF : ∀ n, IsHopfPoint (F n))
    (hcomp : ∀ (n : ℕ) (x : C) (m : M),
      Ideal.Quotient.factorPow I (n + 1).le_succ ((F (n + 1) x).coeff m) =
        (F n x).coeff m) : System I (C := C) (M := M) := by
  have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let g : (n : ℕ) → C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ n) M
    | 0 => default
    | n + 1 => F n
  refine ⟨g, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        constructor <;> apply AlgHom.ext <;> intro x <;> exact Subsingleton.elim _ _
    | succ n => exact hF n
  · intro n k h x m
    symm
    refine Ideal.Quotient.eq_factor_of_eq_factor_succ
      (fun _ _ h => Ideal.pow_le_pow_right h) (fun j => (g j x).coeff m) ?_ h
    intro j
    cases j with
    | zero => exact Subsingleton.elim _ _
    | succ j => exact (hcomp j x m).symm

@[simp] theorem ofSucc_map
    (F : (n : ℕ) → C →ₐ[A] AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M)
    (hF : ∀ n, IsHopfPoint (F n))
    (hcomp : ∀ (n : ℕ) (x : C) (m : M),
      Ideal.Quotient.factorPow I (n + 1).le_succ ((F (n + 1) x).coeff m) =
        (F n x).coeff m) (n : ℕ) : (ofSucc F hF hcomp).map (n + 1) = F n := rfl

/-- The native Hopf-point equations feed the coefficient effectivity construction. -/
def toAlgebraSystem : AdicGroupAlgebra.System I (Coalgebra.comul (R := A) (A := C))
    (M := M) where
  map := f.map
  compatible := f.compatible
  diagonal n := diagonal (f.map n) (f.hopf n)

variable [IsAdicComplete I A] [IsNoetherianRing A]

/-- Algebraization of a compatible family of native Hopf points. -/
def lift : C →ₐc[A] AddMonoidAlgebra A M :=
  AdicGroupAlgebra.liftBialgHom I f.toAlgebraSystem
    (fun n x => counit (f.map n) (f.hopf n) x)

@[simp] theorem reduce_lift (n : ℕ) (x : C) :
    AdicGroupAlgebra.reduce I n (f.lift x) = f.map n x :=
  AdicGroupAlgebra.reduce_liftBialgHom I f.toAlgebraSystem _ n x

/-- Uniqueness of the genuine bialgebra map realizing a Hopf-point family. -/
theorem lift_unique (g : C →ₐc[A] AddMonoidAlgebra A M)
    (hg : ∀ (n : ℕ) (x : C), AdicGroupAlgebra.reduce I n (g x) = f.map n x) :
    g = f.lift :=
  AdicGroupAlgebra.liftBialgHom_unique I f.toAlgebraSystem _ g hg

end System

end Langlands.AdicHopfPoint
