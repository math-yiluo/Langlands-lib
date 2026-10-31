import Langlands.Global.ArchimedeanSymmetricAlgebraSymmetrization
import Langlands.Algebra.LieCasimir
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Full-group invariant enveloping elements are central -/

noncomputable section
universe u
open scoped Classical TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

private def realGenerator : RealLieAlgebra K n →ₗ⁅ℝ⁆ EnvelopingAlgebra K n :=
  { ((envelopingGenerator K n).toLinearMap.restrictScalars ℝ).comp
      (complexify K n).toLinearMap with
    map_lie' := by
      intro X Y
      change envelopingGenerator K n (complexify K n ⁅X, Y⁆) =
        ⁅envelopingGenerator K n (complexify K n X),
          envelopingGenerator K n (complexify K n Y)⁆
      rw [(complexify K n).map_lie, (envelopingGenerator K n).map_lie] }

omit [NumberField K] in
private theorem realGenerator_apply (X : RealLieAlgebra K n) :
    realGenerator K n X = envelopingGenerator K n (complexify K n X) := rfl

private def realLieExpUnits (Y : RealLieAlgebra K n) (t : ℝ) : ArchimedeanGL K n where
  val := NormedSpace.exp (t • realLieAlgebraToMatrix K n Y)
  inv := NormedSpace.exp (-(t • realLieAlgebraToMatrix K n Y))
  val_inv := by
    rw [← NormedSpace.exp_add_of_commute
      (Commute.refl (t • realLieAlgebraToMatrix K n Y)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← NormedSpace.exp_add_of_commute
      (Commute.refl (t • realLieAlgebraToMatrix K n Y)).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]

/-- The full archimedean exponential curve in a real matrix Lie direction. -/
def realLieExponentialCurve (Y : RealLieAlgebra K n) (t : ℝ) : InfiniteAdelicGL K n :=
  (archimedeanGLCoordinates K n).symm (realLieExpUnits K n Y t)

@[simp] theorem realLieExponentialCurve_zero (Y : RealLieAlgebra K n) :
    realLieExponentialCurve K n Y 0 = 1 := by
  apply (archimedeanGLCoordinates K n).injective
  apply Units.ext
  simp [realLieExponentialCurve, realLieExpUnits]

/-- Actual matrix conjugation along the exponential has commutator derivative. -/
theorem exponentialCurve_adjoint_deriv (Y X : RealLieAlgebra K n) :
    HasDerivAt
      (fun t => realLieAlgebraToMatrix K n
        (realLieConjugation K n (realLieExponentialCurve K n Y t) X))
      (realLieAlgebraToMatrix K n ⁅Y, X⁆) 0 := by
  let A := realLieAlgebraToMatrix K n Y
  let B := realLieAlgebraToMatrix K n X
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hm : HasDerivAt (fun t : ℝ => NormedSpace.exp (-(t • A))) (-A) 0 := by
    simpa only [smul_neg, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (-A) (0 : ℝ)
  have h := (hp.mul_const B).fun_mul hm
  simp only [zero_smul, neg_zero, NormedSpace.exp_zero, mul_one, one_mul,
    mul_neg, ← sub_eq_add_neg] at h
  have he :
      (fun t => realLieAlgebraToMatrix K n
        (realLieConjugation K n (realLieExponentialCurve K n Y t) X)) =
      (fun t => NormedSpace.exp (t • A) * B * NormedSpace.exp (-(t • A))) := by
    funext t
    rw [realLieAlgebraToMatrix_realLieConjugation, realLieExponentialCurve,
      ContinuousMulEquiv.apply_symm_apply, map_inv]
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl
  rw [he, realLieAlgebraToMatrix_lie]
  exact h

private def exponentialWeakDerivative (Y : RealLieAlgebra K n) :
    Submodule ℂ (EnvelopingAlgebra K n) where
  carrier := {a | ∀ ℓ : EnvelopingAlgebra K n →ₗ[ℂ] ℂ,
    HasDerivAt (fun t => ℓ (envelopingConjugation K n
      (realLieExponentialCurve K n Y t) a))
      (ℓ (realGenerator K n Y * a - a * realGenerator K n Y)) 0}
  zero_mem' := by
    intro ℓ
    simpa only [map_zero, mul_zero, zero_mul, sub_self] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  add_mem' := by
    intro a b ha hb ℓ
    simpa only [map_add, mul_add, add_mul, add_sub_add_comm, Pi.add_apply] using
      (ha ℓ).fun_add (hb ℓ)
  smul_mem' := by
    intro z a ha ℓ
    simpa only [map_smul, mul_smul_comm, smul_mul_assoc, ← smul_sub, Pi.smul_apply] using
      (ha ℓ).fun_const_smul z

private theorem one_mem_exponentialWeakDerivative (Y : RealLieAlgebra K n) :
    1 ∈ exponentialWeakDerivative K n Y := by
  intro ℓ
  simpa only [map_one, mul_one, one_mul, sub_self, map_zero] using
    hasDerivAt_const (0 : ℝ) (ℓ 1)

private theorem realGenerator_mul_mem_exponentialWeakDerivative
    (Y X : RealLieAlgebra K n) {a : EnvelopingAlgebra K n}
    (ha : a ∈ exponentialWeakDerivative K n Y) :
    a * realGenerator K n X ∈ exponentialWeakDerivative K n Y := by
  classical
  intro ℓ
  let b := Module.finBasis ℝ (ArchimedeanMatrix K n)
  let e := fun i => realGenerator K n ((realLieAlgebraToMatrix K n).symm (b i))
  let c := fun t => realLieExponentialCurve K n Y t
  let V := fun t => realLieAlgebraToMatrix K n (realLieConjugation K n (c t) X)
  let W := realGenerator K n Y * a - a * realGenerator K n Y
  let T (v : EnvelopingAlgebra K n) : ArchimedeanMatrix K n →ₗ[ℝ] ℂ :=
    (ℓ.restrictScalars ℝ).comp ((LinearMap.mulLeft ℝ v).comp
      ((realGenerator K n).toLinearMap.comp
        (realLieAlgebraToMatrix K n).symm.toLinearMap))
  have hs (v : EnvelopingAlgebra K n) (Z : RealLieAlgebra K n) :
      ∑ i, b.repr (realLieAlgebraToMatrix K n Z) i • ℓ (v * e i) =
        ℓ (v * realGenerator K n Z) := by
    have h := congrArg (T v) (b.sum_repr (realLieAlgebraToMatrix K n Z))
    simpa only [map_sum, map_smul, T, e, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LieHom.coe_toLinearMap] using h
  have hcoeff (i) : HasDerivAt (fun t => b.repr (V t) i)
      (b.repr (realLieAlgebraToMatrix K n ⁅Y, X⁆) i) 0 := by
    let L : ArchimedeanMatrix K n →L[ℝ] ℝ :=
      { b.coord i with cont := (b.coord i).continuous_of_finiteDimensional }
    exact L.hasFDerivAt.comp_hasDerivAt 0 (exponentialCurve_adjoint_deriv K n Y X)
  have hfactor (i) : HasDerivAt (fun t => ℓ (envelopingConjugation K n (c t) a * e i))
      (ℓ (W * e i)) 0 :=
    ha (ℓ.comp (LinearMap.mulRight ℂ (e i)))
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hcoeff i).fun_smul (hfactor i))
  have hf : (fun t => ∑ i, b.repr (V t) i •
        ℓ (envelopingConjugation K n (c t) a * e i)) =
      (fun t => ℓ (envelopingConjugation K n (c t)
        (a * realGenerator K n X))) := by
    funext t
    rw [hs]
    simp only [map_mul, realGenerator_apply, envelopingConjugation_generator,
      complexLieConjugation_complexify]
  rw [hf] at hd
  have hzero : V 0 = realLieAlgebraToMatrix K n X := by
    simp only [V, c, realLieExponentialCurve_zero, realLieConjugation_one,
      LieEquiv.refl_apply]
  simp only [hzero, Finset.sum_add_distrib, hs, c,
    envelopingConjugation_one, realLieExponentialCurve_zero, AlgEquiv.coe_refl,
    id_eq] at hd
  have hbracket : realGenerator K n ⁅Y, X⁆ =
      realGenerator K n Y * realGenerator K n X -
        realGenerator K n X * realGenerator K n Y :=
    (realGenerator K n).map_lie Y X
  convert hd using 1
  rw [← map_add, hbracket]
  congr 1
  dsimp [W]
  noncomm_ring

omit [NumberField K] in
private theorem generator_tmul (z : ℂ) (X : RealLieAlgebra K n) :
    envelopingGenerator K n (z ⊗ₜ[ℝ] X) = z • realGenerator K n X := by
  rw [realGenerator_apply, ← map_smul, complexify_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem generator_mul_mem_exponentialWeakDerivative
    (Y : RealLieAlgebra K n) (X : ComplexLieAlgebra K n)
    {a : EnvelopingAlgebra K n} (ha : a ∈ exponentialWeakDerivative K n Y) :
    a * envelopingGenerator K n X ∈ exponentialWeakDerivative K n Y := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    rw [generator_tmul, mul_smul_comm]
    exact (exponentialWeakDerivative K n Y).smul_mem z
      (realGenerator_mul_mem_exponentialWeakDerivative K n Y X ha)
  | add X Z hX hZ =>
    simpa only [map_add, mul_add] using
      (exponentialWeakDerivative K n Y).add_mem hX hZ

private theorem mem_exponentialWeakDerivative
    (Y : RealLieAlgebra K n) (a : EnvelopingAlgebra K n) :
    a ∈ exponentialWeakDerivative K n Y := by
  obtain ⟨d, hd⟩ := exists_mem_envelopingDegreeFiltration K n a
  induction hd using Submodule.pow_induction_on_right' with
  | algebraMap z =>
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (exponentialWeakDerivative K n Y).smul_mem z
        (one_mem_exponentialWeakDerivative K n Y)
  | add x y i hx hy ihx ihy =>
    exact (exponentialWeakDerivative K n Y).add_mem ihx ihy
  | mul_mem i x hx ih m hm =>
    obtain ⟨c, hc, v, hv, rfl⟩ := Submodule.mem_sup.mp hm
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hc
    obtain ⟨X, rfl⟩ := hv
    rw [mul_add]
    apply (exponentialWeakDerivative K n Y).add_mem
    · simpa only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] using
        (exponentialWeakDerivative K n Y).smul_mem z ih
    · exact generator_mul_mem_exponentialWeakDerivative K n Y X ih

/-- Scalar differentiation of the actual conjugation orbit of every enveloping element. -/
theorem exponentialCurve_enveloping_deriv (Y : RealLieAlgebra K n)
    (a : EnvelopingAlgebra K n) (ℓ : EnvelopingAlgebra K n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => ℓ (envelopingConjugation K n
      (realLieExponentialCurve K n Y t) a))
      (ℓ (envelopingGenerator K n (complexify K n Y) * a -
        a * envelopingGenerator K n (complexify K n Y))) 0 := by
  simpa only [realGenerator_apply] using mem_exponentialWeakDerivative K n Y a ℓ

/-- Every genuine enveloping element fixed by the full archimedean group is central. -/
theorem envelopingGroupInvariants_le_center :
    envelopingGroupInvariants K n ≤ Subalgebra.center ℂ (EnvelopingAlgebra K n) := by
  intro a ha
  have hreal (Y : RealLieAlgebra K n) :
      realGenerator K n Y * a = a * realGenerator K n Y := by
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro ℓ
    have hd := mem_exponentialWeakDerivative K n Y a ℓ
    have hc : (fun t => ℓ (envelopingConjugation K n
        (realLieExponentialCurve K n Y t) a)) = (fun _ : ℝ => ℓ a) := by
      funext t
      rw [(mem_envelopingGroupInvariants K n a).mp ha]
    rw [hc] at hd
    exact hd.unique (hasDerivAt_const (0 : ℝ) (ℓ a))
  let S := Subalgebra.centralizer ℂ {a}
  have hcomplex (X : ComplexLieAlgebra K n) : envelopingGenerator K n X ∈ S := by
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      rw [generator_tmul]
      apply S.smul_mem
      apply (Subalgebra.mem_centralizer_iff ℂ).mpr
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact (hreal X).symm
    | add X Z hX hZ =>
      simpa only [map_add] using S.add_mem hX hZ
  have hle : Algebra.adjoin ℂ (Set.range (envelopingGenerator K n)) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨X, rfl⟩
    exact hcomplex X
  have htop : Algebra.adjoin ℂ (Set.range (envelopingGenerator K n)) = ⊤ :=
    Langlands.Algebra.LieCasimir.enveloping_adjoin_range
  rw [htop] at hle
  apply Subalgebra.mem_center_iff.mpr
  intro b
  exact ((Subalgebra.mem_centralizer_iff ℂ).mp
    (hle (show b ∈ (⊤ : Subalgebra ℂ (EnvelopingAlgebra K n)) from trivial)) _
    (Set.mem_singleton a)).symm

/-- The actual algebra inclusion of full-group invariant elements into the center. -/
def envelopingGroupInvariantToCenter :
    envelopingGroupInvariants K n →ₐ[ℂ] EnvelopingCenter K n :=
  (envelopingGroupInvariants K n).inclusion
    (envelopingGroupInvariants_le_center K n)

@[simp] theorem envelopingGroupInvariantToCenter_coe
    (a : envelopingGroupInvariants K n) :
    (envelopingGroupInvariantToCenter K n a : EnvelopingAlgebra K n) = a.val := rfl

/-- Full-group invariant symmetric tensors symmetrize to actual central elements. -/
def lieSymmetricGroupInvariantCentralSymmetrize :
    lieSymmetricGroupInvariants K n →ₗ[ℂ] EnvelopingCenter K n :=
  (envelopingGroupInvariantToCenter K n).toLinearMap.comp
    (lieSymmetricGroupInvariantSymmetrize K n)

@[simp] theorem lieSymmetricGroupInvariantCentralSymmetrize_coe
    (P : lieSymmetricGroupInvariants K n) :
    (lieSymmetricGroupInvariantCentralSymmetrize K n P : EnvelopingAlgebra K n) =
      lieSymmetricAlgebraSymmetrize K n P.val := rfl

end Langlands.Global.ArchimedeanGL
