import Langlands.GroupScheme.Quaternionic.AlternatingConjugation
import Langlands.GroupScheme.FiniteAlgebraUnits
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Quaternion conjugation from the original orthogonal-involution dimensions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)

omit [Algebra.IsCentral K D] in
/-- Rank-nullity gives the dimension of the alternating line, including in characteristic two. -/
theorem finrank_alternatingSubspace_of_dimensions
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) :
    Module.finrank K σ.alternatingSubspace = 1 := by
  have hk : LinearMap.ker (LinearMap.id - σ.toLinearMap) = σ.symmetricSubspace := by
    ext a
    change a - σ a = 0 ↔ σ a - a = 0
    rw [sub_eq_zero, sub_eq_zero]
    exact eq_comm
  have h := (LinearMap.id - σ.toLinearMap).finrank_range_add_finrank_ker
  rw [hk, hsym, hdim] at h
  change Module.finrank K σ.alternatingSubspace + 3 = 4 at h
  omega

omit [Algebra.IsCentral K D] in
private theorem exists_alternatingUnit
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) :
    ∃ l : Dˣ, (l : D) ∈ σ.alternatingSubspace := by
  have hline := σ.finrank_alternatingSubspace_of_dimensions hdim hsym
  have hne : σ.alternatingSubspace ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hline
    norm_num at hline
  obtain ⟨l, hl, hl0⟩ := σ.alternatingSubspace.ne_bot_iff.mp hne
  exact ⟨Units.mk0 l hl0, hl⟩

/-- An actual invertible generator chosen from the alternating line. -/
def quaternionAlternatingUnit
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) : Dˣ :=
  Classical.choose (σ.exists_alternatingUnit hdim hsym)

omit [Algebra.IsCentral K D] in
theorem quaternionAlternatingUnit_mem
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) :
    (σ.quaternionAlternatingUnit hdim hsym : D) ∈ σ.alternatingSubspace :=
  Classical.choose_spec (σ.exists_alternatingUnit hdim hsym)

/-- The actual conjugation obtained by twisting the supplied orthogonal involution. -/
def quaternionConjugation
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) :
    Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D :=
  σ.alternatingTwist (σ.quaternionAlternatingUnit hdim hsym)
    (σ.map_eq_neg_of_mem_alternating (σ.quaternionAlternatingUnit_mem hdim hsym))

/-- The original dimension-four hypothesis gives reduced degree two. -/
theorem reducedDegree_eq_two_of_finrank_four (hdim : Module.finrank K D = 4) :
    Langlands.CentralSimple.reducedDegree K D = 2 := by
  have h := Langlands.CentralSimple.reducedNorm_degree_spec K D
  rw [hdim] at h
  nlinarith [h.1]

/-- The constructed conjugation has the canonical reduced norm as its conjugate product. -/
theorem quaternionConjugation_norm
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) (a : D) :
    a * σ.quaternionConjugation hdim hsym a =
      algebraMap K D (Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a)) := by
  rw [← σ.alternatingNorm_eq_reducedNorm
    (σ.finrank_alternatingSubspace_of_dimensions hdim hsym)
    (σ.quaternionAlternatingUnit hdim hsym)
    (σ.quaternionAlternatingUnit_mem hdim hsym)
    (reducedDegree_eq_two_of_finrank_four hdim)]
  exact (σ.alternatingNorm_spec
    (σ.finrank_alternatingSubspace_of_dimensions hdim hsym)
    (σ.quaternionAlternatingUnit hdim hsym)
    (σ.quaternionAlternatingUnit_mem hdim hsym) a).symm

section PolynomialExtension

variable [Infinite K]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
private theorem polynomialTensor_eq_zero {n : ℕ} (b : Module.Basis (Fin n) K D)
    (y : MvPolynomial (Fin n) K ⊗[K] D)
    (hy : ∀ c : Fin n → K,
      Algebra.TensorProduct.map (MvPolynomial.aeval c) (AlgHom.id K D) y = 0) :
    y = 0 := by
  apply (b.baseChange (MvPolynomial (Fin n) K)).repr.injective
  apply Finsupp.ext
  intro j
  simp only [_root_.map_zero, Finsupp.zero_apply]
  apply MvPolynomial.funext
  intro c
  have h := congrArg (fun z : K ⊗[K] D => (b.baseChange K).repr z j) (hy c)
  rw [Langlands.ReducedNorm.coordinates_naturality] at h
  simpa only [MvPolynomial.aeval_eq_eval, _root_.map_zero, Finsupp.zero_apply] using h

omit [Infinite K] in
private theorem norm_identity_ground_tensor
    (τ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)
    (hτ : ∀ a : D, a * τ a =
      algebraMap K D (Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a)))
    (z : K ⊗[K] D) :
    z * τ.baseChange K z =
      algebraMap K (K ⊗[K] D) (Langlands.CentralSimple.reducedNorm K D K z) := by
  obtain ⟨a, rfl⟩ := (Algebra.TensorProduct.lid K D).symm.surjective z
  change ((1 : K) ⊗ₜ[K] a) * τ.baseChange K ((1 : K) ⊗ₜ[K] a) =
    algebraMap K (K ⊗[K] D)
      (Langlands.CentralSimple.reducedNorm K D K ((1 : K) ⊗ₜ[K] a))
  rw [τ.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hτ]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp

omit [Infinite K] in
private theorem norm_identity_map_defect
    (τ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)
    {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (x : R ⊗[K] D) :
    Algebra.TensorProduct.map f (AlgHom.id K D)
      (x * τ.baseChange R x -
        algebraMap R (R ⊗[K] D) (Langlands.CentralSimple.reducedNorm K D R x)) =
      Algebra.TensorProduct.map f (AlgHom.id K D) x *
        τ.baseChange S (Algebra.TensorProduct.map f (AlgHom.id K D) x) -
          algebraMap S (S ⊗[K] D)
            (Langlands.CentralSimple.reducedNorm K D S
              (Algebra.TensorProduct.map f (AlgHom.id K D) x)) := by
  rw [_root_.map_sub, _root_.map_mul, τ.map_baseChange,
    Langlands.CentralSimple.reducedNorm_naturality]
  rfl

/-- A conjugate-product reduced-norm identity over an infinite field extends to every
commutative coefficient algebra, including nonreduced ones. -/
theorem conjugation_norm_baseChange
    (τ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)
    (hτ : ∀ a : D, a * τ a =
      algebraMap K D (Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a)))
    (R : Type u) [CommRing R] [Algebra K R] (x : R ⊗[K] D) :
    x * τ.baseChange R x =
      algebraMap R (R ⊗[K] D) (Langlands.CentralSimple.reducedNorm K D R x) := by
  let b := Module.finBasis K D
  let P := FiniteAlgebraUnits.coordinateRing K (Module.finrank K D)
  let g : P ⊗[K] D := FiniteAlgebraUnits.genericElement b
  have hgen : g * τ.baseChange P g -
      algebraMap P (P ⊗[K] D) (Langlands.CentralSimple.reducedNorm K D P g) = 0 := by
    apply polynomialTensor_eq_zero b
    intro c
    rw [norm_identity_map_defect]
    exact sub_eq_zero.mpr (norm_identity_ground_tensor τ hτ _)
  let φ : P →ₐ[K] R := FiniteAlgebraUnits.coefficientMap b x
  have hg : Algebra.TensorProduct.map φ (AlgHom.id K D) g = x :=
    FiniteAlgebraUnits.evaluatedElement_coefficientMap b x
  have h := congrArg (Algebra.TensorProduct.map φ (AlgHom.id K D)) hgen
  rw [norm_identity_map_defect, _root_.map_zero, hg] at h
  exact sub_eq_zero.mp h

/-- The constructed quaternion conjugation has the actual reduced norm on every coefficient
algebra over the infinite ground field. -/
theorem quaternionConjugation_norm_baseChange
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
    (R : Type u) [CommRing R] [Algebra K R] (x : R ⊗[K] D) :
    x * (σ.quaternionConjugation hdim hsym).baseChange R x =
      algebraMap R (R ⊗[K] D) (Langlands.CentralSimple.reducedNorm K D R x) :=
  conjugation_norm_baseChange (σ.quaternionConjugation hdim hsym)
    (σ.quaternionConjugation_norm hdim hsym) R x

end PolynomialExtension

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
