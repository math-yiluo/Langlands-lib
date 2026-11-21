import Langlands.Representation.Archimedean.SmoothUnitAction

/-! # Orthonormal square sums of genuine derivatives and their unit covariance -/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section Bilinear

variable {V N : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup N] [Module ℝ N]
  (B : LinearMap.BilinForm ℝ V)

/-- In an orthonormal basis, coordinates are pairings with the basis vectors. -/
theorem repr_eq_of_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (x : V) (l : ι) : b.repr x l = B x (b l) := by
  have h := congrArg (fun y => B y (b l)) (b.sum_repr x)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hb, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

/-- The diagonal sum of a bilinear map over an orthonormal basis of a symmetric form does not
depend on the orthonormal basis. -/
theorem sum_bilin_eq_of_orthonormal (hB : ∀ x y, B x y = B y x)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (hc : ∀ i j, B (c i) (c j) = if i = j then 1 else 0)
    (f : V →ₗ[ℝ] V →ₗ[ℝ] N) :
    ∑ i, f (b i) (b i) = ∑ j, f (c j) (c j) := by
  have hcr := repr_eq_of_orthonormal B c hc
  have hbr := repr_eq_of_orthonormal B b hb
  have hexp (i : ι) : f (b i) (b i) =
      ∑ j, ∑ l, (B (b i) (c j) * B (b i) (c l)) • f (c j) (c l) := by
    conv_lhs => rw [← c.sum_repr (b i)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      smul_smul, hcr]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have horth (j l : κ) : ∑ i, B (b i) (c j) * B (b i) (c l) = if j = l then 1 else 0 := by
    rw [← hc j l]
    conv_rhs => rw [← b.sum_repr (c j)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hbr]
    exact Finset.sum_congr rfl fun i _ => by rw [hB (c j) (b i)]
  calc ∑ i, f (b i) (b i)
      = ∑ i, ∑ j, ∑ l, (B (b i) (c j) * B (b i) (c l)) • f (c j) (c l) :=
        Finset.sum_congr rfl fun i _ => hexp i
    _ = ∑ j, ∑ l, (∑ i, B (b i) (c j) * B (b i) (c l)) • f (c j) (c l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ j, f (c j) (c j) := by
        simp only [horth, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]

end Bilinear

namespace DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

theorem operator_add_apply (X Y : A) (v : D) :
    operator 𝓜 R (X + Y) v = operator 𝓜 R X v + operator 𝓜 R Y v := by
  apply (toSmooth 𝓜 R).injective
  change (smoothLieDerivativeDirection 𝓜 R (X + Y)) (toSmooth 𝓜 R v) =
    smoothLieDerivativeDirection 𝓜 R X (toSmooth 𝓜 R v) +
      smoothLieDerivativeDirection 𝓜 R Y (toSmooth 𝓜 R v)
  rw [map_add, LinearMap.add_apply]

theorem operator_smul_apply (c : ℝ) (X : A) (v : D) :
    operator 𝓜 R (c • X) v = c • operator 𝓜 R X v := by
  apply (toSmooth 𝓜 R).injective
  change (smoothLieDerivativeDirection 𝓜 R (c • X)) (toSmooth 𝓜 R v) =
    c • smoothLieDerivativeDirection 𝓜 R X (toSmooth 𝓜 R v)
  rw [map_smul, LinearMap.smul_apply]

/-- The real bilinear map `(X, Y) ↦ dR(X) dR(Y) w`. -/
def operatorPairing (w : D) : A →ₗ[ℝ] A →ₗ[ℝ] D :=
  LinearMap.mk₂ ℝ (fun X Y => operator 𝓜 R X (operator 𝓜 R Y w))
    (fun X X' Y => operator_add_apply R X X' _)
    (fun c X Y => operator_smul_apply R c X _)
    (fun X Y Y' => by rw [operator_add_apply, map_add])
    (fun c X Y => by rw [operator_smul_apply, LinearMap.map_smul_of_tower])

@[simp]
theorem operatorPairing_apply (w : D) (X Y : A) :
    operatorPairing R w X Y = operator 𝓜 R X (operator 𝓜 R Y w) := rfl

/-- The sum over a finite basis of the squared genuine derivatives. -/
def basisSquareSum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A) : Module.End ℂ D :=
  ∑ i, operator 𝓜 R (b i) * operator 𝓜 R (b i)

theorem basisSquareSum_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A) (w : D) :
    basisSquareSum R b w = ∑ i, operator 𝓜 R (b i) (operator 𝓜 R (b i) w) := by
  simp [basisSquareSum, LinearMap.sum_apply]

variable (B : LinearMap.BilinForm ℝ A)

/-- Square sums over two orthonormal bases of the same symmetric form coincide. -/
theorem basisSquareSum_eq_of_orthonormal (hB : ∀ x y, B x y = B y x)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℝ A) (c : Module.Basis κ ℝ A)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (hc : ∀ i j, B (c i) (c j) = if i = j then 1 else 0) :
    basisSquareSum R b = basisSquareSum R c := by
  apply LinearMap.ext
  intro w
  rw [basisSquareSum_apply, basisSquareSum_apply]
  exact sum_bilin_eq_of_orthonormal B hB b c hb hc (operatorPairing R w)

/-- Conjugation by the inverse of a unit as a real linear equivalence. -/
def inverseConjugationEquiv (g : Aˣ) : A ≃ₗ[ℝ] A :=
  LinearEquiv.ofLinearMap (inverseConjugationCLM g).toLinearMap
    (inverseConjugationCLM g⁻¹).toLinearMap
    (by
      apply LinearMap.ext
      intro X
      simp [inverseConjugationCLM_apply, mul_assoc])
    (by
      apply LinearMap.ext
      intro X
      simp [inverseConjugationCLM_apply, mul_assoc])

/-- If conjugation by the inverse of `g` preserves a symmetric form, the square sum over an
orthonormal basis of that form commutes with the genuine action of `g`. -/
theorem basisSquareSum_representation (hB : ∀ x y, B x y = B y x)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ A)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (g : Aˣ)
    (hg : ∀ X Y, B (inverseConjugationCLM g X) (inverseConjugationCLM g Y) = B X Y) (w : D) :
    basisSquareSum R b (representation 𝓜 R g w) =
      representation 𝓜 R g (basisSquareSum R b w) := by
  let b' := b.map (inverseConjugationEquiv g)
  have hb' : ∀ i j, B (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    change B (inverseConjugationCLM g (b i)) (inverseConjugationCLM g (b j)) = _
    rw [hg, hb]
  have hsum : basisSquareSum R b = basisSquareSum R b' :=
    basisSquareSum_eq_of_orthonormal R B hB b b' hb hb'
  rw [basisSquareSum_apply, hsum, basisSquareSum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change operator 𝓜 R (b i) (operator 𝓜 R (b i) (representation 𝓜 R g w)) =
    representation 𝓜 R g (operator 𝓜 R (inverseConjugationCLM g (b i))
      (operator 𝓜 R (inverseConjugationCLM g (b i)) w))
  rw [operator_representation_units, operator_representation_units]

end DerivativeSmoothVectors

end Langlands.Archimedean
