import Langlands.AlgebraicGeometry.GroupoidCoactionInvariants
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Coactions induced from modules over the invariant ring -/

universe u v w

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable (t : B →+* C)
variable (N : Type v) [AddCommGroup N] [Module (invariantRing t) N]

/-- Extension of scalars from the invariant ring, with its canonical coaction. -/
def inducedCoactionMap :
    B ⊗[invariantRing t] N →+ C ⊗[B] (B ⊗[invariantRing t] N) :=
  liftAddHom
    { toFun := fun b =>
        { toFun := fun n => t b ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] n)
          map_zero' := by simp
          map_add' := fun n n' => by simp [tmul_add] }
      map_zero' := by ext n; simp
      map_add' := fun b b' => by ext n; simp [add_tmul] }
    (fun a b n => by
      change t ((a : B) * b) ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] n) =
        t b ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] (a • n))
      rw [map_mul, a.property, ← Algebra.smul_def, smul_tmul]
      congr 1
      rw [smul_tmul', tmul_smul]
      rfl)

@[simp]
lemma inducedCoactionMap_tmul (b : B) (n : N) :
    inducedCoactionMap t N (b ⊗ₜ[invariantRing t] n) =
      t b ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] n) :=
  rfl

lemma inducedCoactionMap_smul (b : B) (x : B ⊗[invariantRing t] N) :
    inducedCoactionMap t N (b • x) = t b • inducedCoactionMap t N x := by
  induction x with
  | tmul b' n => simp [smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- A module over the invariant ring gives a coaction after extension of scalars. -/
def induced : GroupoidCoaction t (B ⊗[invariantRing t] N) where
  coaction := inducedCoactionMap t N
  map_smul := inducedCoactionMap_smul t N
  counit T _ _ φ h x := by
    have ht (b : B) : φ (t b) = algebraMap B T b :=
      DFunLike.congr_fun h b
    induction x with
    | tmul b n =>
        simp only [inducedCoactionMap_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          ht]
        rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
        congr 1
        simp [smul_tmul', smul_eq_mul]
    | add x y hx hy => simp [hx, hy, tmul_add]
  coassoc T _ _ φ₁ φ₂ φ₃ h ht x := by
    have htb (b : B) : φ₃ (t b) = φ₁ (t b) :=
      DFunLike.congr_fun ht b
    induction x with
    | tmul b n => simp [coactionCompose_tmul, htb, smul_tmul', smul_eq_mul]
    | add x y hx hy => simp [hx, hy]

@[simp]
lemma induced_coaction_tmul (b : B) (n : N) :
    (induced t N).coaction (b ⊗ₜ[invariantRing t] n) =
      t b ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] n) :=
  rfl

/-- The canonical element of an extended module is invariant. -/
lemma induced_one_tmul_mem_invariants (n : N) :
    (1 : B) ⊗ₜ[invariantRing t] n ∈ (induced t N).invariants := by
  change inducedCoactionMap t N ((1 : B) ⊗ₜ[invariantRing t] n) =
    (1 : C) ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] n)
  simp

/-- The unit into the invariant module of extension of scalars. -/
def inducedUnit : N →ₗ[invariantRing t] (induced t N).invariantSubmodule where
  toFun n := ⟨(1 : B) ⊗ₜ[invariantRing t] n, induced_one_tmul_mem_invariants t N n⟩
  map_add' n n' := Subtype.ext (tmul_add _ _ _)
  map_smul' a n := by
    apply Subtype.ext
    change (1 : B) ⊗ₜ[invariantRing t] (a • n) =
      a • ((1 : B) ⊗ₜ[invariantRing t] n)
    rw [tmul_smul, smul_tmul']

@[simp]
lemma inducedUnit_coe (n : N) :
    (inducedUnit t N n : B ⊗[invariantRing t] N) =
      (1 : B) ⊗ₜ[invariantRing t] n :=
  rfl

variable {N}
variable {N' : Type v} [AddCommGroup N'] [Module (invariantRing t) N']

/-- Extension of scalars of a linear map is equivariant for the induced coactions. -/
lemma induced_isHom_baseChange (f : N →ₗ[invariantRing t] N') :
    (induced t N).IsHom (induced t N') (f.baseChange B) := by
  intro x
  induction x with
  | tmul b n => simp [LinearMap.baseChange_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Naturality of the unit for linear maps over the invariant ring. -/
lemma inducedUnit_natural (f : N →ₗ[invariantRing t] N') :
    ((induced t N).invariantsMap (induced t N') (f.baseChange B)
      (induced_isHom_baseChange t f)).comp (inducedUnit t N) =
      (inducedUnit t N').comp f := by
  ext n
  rfl

variable {ι : Type w} (basis : Module.Basis ι (invariantRing t) N)

private lemma induced_coord_coaction (x : B ⊗[invariantRing t] N) (i : ι) :
    TensorProduct.rid B C
        (LinearMap.lTensor C ((basis.baseChange B).coord i) ((induced t N).coaction x)) =
      t ((basis.baseChange B).repr x i) := by
  induction x with
  | tmul b n =>
      simp only [induced_coaction_tmul, LinearMap.lTensor_tmul, Module.Basis.coord_apply,
        Module.Basis.baseChange_repr_tmul, TensorProduct.rid_tmul,
        Algebra.smul_def, mul_one]
      change algebraMap B C (basis.repr n i : B) * t b =
        t ((basis.repr n i : B) * b)
      rw [map_mul, (basis.repr n i).property]
  | add x y hx hy => simp [hx, hy]

/-- An invariant in an extended free module has all coefficients in the invariant ring. -/
lemma induced_repr_mem_invariantRing (x : B ⊗[invariantRing t] N)
    (hx : x ∈ (induced t N).invariants) (i : ι) :
    (basis.baseChange B).repr x i ∈ invariantRing t := by
  have h := congrArg
    (fun y => TensorProduct.rid B C (LinearMap.lTensor C ((basis.baseChange B).coord i) y))
    hx
  rw [induced_coord_coaction] at h
  simpa [Module.Basis.coord_apply, Algebra.smul_def] using h

include basis in
/-- The unit for an extended free module is injective, as seen on basis coefficients. -/
lemma inducedUnit_injective_of_basis : Function.Injective (inducedUnit t N) := by
  intro n n' h
  apply basis.repr.injective
  ext i
  have h' := congrArg
    (fun x : (induced t N).invariantSubmodule => (basis.baseChange B).repr x.val i) h
  simpa [Algebra.smul_def] using h'

include basis in
/-- The unit for an extended free module is surjective: invariant coefficients descend. -/
lemma inducedUnit_surjective_of_basis : Function.Surjective (inducedUnit t N) := by
  intro x
  classical
  let coeff := (basis.baseChange B).repr (x : B ⊗[invariantRing t] N)
  let a : ι →₀ invariantRing t :=
    { support := coeff.support
      toFun := fun i => ⟨coeff i, induced_repr_mem_invariantRing t basis x x.property i⟩
      mem_support_toFun := by
        intro i
        simp only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
        exact Finsupp.mem_support_iff }
  refine ⟨basis.repr.symm a, ?_⟩
  apply Subtype.ext
  apply (basis.baseChange B).repr.injective
  ext i
  simp [a, coeff, Algebra.smul_def]
  rfl

/-- The canonical unit is bijective for every free module over the invariant ring. -/
lemma inducedUnit_bijective [Module.Free (invariantRing t) N] :
    Function.Bijective (inducedUnit t N) := by
  obtain ⟨ι, basis⟩ := Module.Free.exists_basis (R := invariantRing t) (M := N)
  exact ⟨inducedUnit_injective_of_basis t basis, inducedUnit_surjective_of_basis t basis⟩

end Langlands.AlgebraicGeometry.GroupoidCoaction
