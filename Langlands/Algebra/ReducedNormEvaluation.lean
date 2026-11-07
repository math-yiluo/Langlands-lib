import Langlands.Algebra.ReducedNormDescent
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-! Evaluation of a descended determinant polynomial on all commutative scalar algebras. -/

noncomputable section

namespace Langlands.ReducedNorm

universe uK uL uA uI uJ uR uS

open scoped TensorProduct
open MvPolynomial

variable {K : Type uK} [Field K] {A : Type uA} [Ring A] [Algebra K A]
  {J : Type uJ} [Fintype J]

/-- Evaluate a coordinate polynomial using the base-changed basis. -/
def polynomialValue (b : Module.Basis J K A) (P : MvPolynomial J K)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) : R :=
  eval₂ (algebraMap K R) ((b.baseChange R).repr x) P

/-- Every tensor has its finite basis-coordinate expansion. -/
theorem sum_coordinates_tmul (b : Module.Basis J K A)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    ∑ j, (b.baseChange R).repr x j ⊗ₜ[K] b j = x := by
  simpa only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    using (b.baseChange R).sum_repr x

omit [Fintype J] in
/-- Base-changed coordinates commute with any scalar-algebra map. -/
theorem coordinates_naturality (b : Module.Basis J K A)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : R ⊗[K] A) (j : J) :
    (b.baseChange S).repr (Algebra.TensorProduct.map f (AlgHom.id K A) x) j =
      f ((b.baseChange R).repr x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

omit [Fintype J] in
/-- Polynomial evaluation on coordinates is natural on every commutative test algebra. -/
theorem polynomialValue_naturality (b : Module.Basis J K A) (P : MvPolynomial J K)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    polynomialValue b P S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      f (polynomialValue b P R x) := by
  unfold polynomialValue
  change _ = f.toRingHom (eval₂ (algebraMap K R) ((b.baseChange R).repr x) P)
  rw [MvPolynomial.hom_eval₂]
  have hf : f.toRingHom.comp (algebraMap K R) = algebraMap K S := f.comp_algebraMap
  rw [hf]
  congr 1
  funext j
  exact coordinates_naturality b f x j

section Splitting

variable {L : Type uL} [Field L] [Algebra K L]
  {I : Type uI} [Fintype I] [DecidableEq I]

/-- Extend a splitting chart to a test algebra over its coefficient field. -/
def splittingMap (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] :
    R ⊗[K] A →ₐ[R] Matrix I I R :=
  AlgHom.liftEquiv K R A (Matrix I I R)
    ((((Algebra.ofId L R).mapMatrix).restrictScalars K).comp
      ((e.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight))

@[simp] theorem splittingMap_tmul (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (r : R) (a : A) :
    splittingMap e R (r ⊗ₜ[K] a) = r • (e (1 ⊗ₜ[K] a)).map (algebraMap L R) := rfl

variable [Nonempty I] [FiniteDimensional K L] [IsGalois K L]

/-- The descended coordinate polynomial evaluates to determinant over every splitting-field algebra. -/
theorem descendedPolynomial_eval_det (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (x : R ⊗[K] A) :
    polynomialValue b (descendedPolynomial e b) R x = (splittingMap e R x).det := by
  unfold polynomialValue
  rw [IsScalarTower.algebraMap_eq K L R, ← MvPolynomial.eval₂_map,
    descendedPolynomial_map, chartPolynomial, detPolynomial_eval]
  congr 1
  calc
    _ = splittingMap e R (∑ j, (b.baseChange R).repr x j ⊗ₜ[K] b j) := by
      rw [map_sum]
      rfl
    _ = splittingMap e R x := congrArg (splittingMap e R) (sum_coordinates_tmul b R x)

/-- A multiplicative map with zero obtained by actual polynomial evaluation and faithful comparison. -/
def normFromGalois (b : Module.Basis J K A) (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] : R ⊗[K] A →*₀ R where
  toFun := polynomialValue b (descendedPolynomial e b) R
  map_zero' := by
    apply Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective K L)
    rw [← polynomialValue_naturality b _ (Algebra.TensorProduct.includeRight (A := L)),
      map_zero, descendedPolynomial_eval_det]
    simp
  map_one' := by
    apply Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective K L)
    rw [← polynomialValue_naturality b _ (Algebra.TensorProduct.includeRight (A := L)),
      map_one, descendedPolynomial_eval_det]
    simp only [map_one, Matrix.det_one]
  map_mul' x y := by
    apply Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective K L)
    simp only [map_mul]
    rw [← polynomialValue_naturality b _ (Algebra.TensorProduct.includeRight (A := L)),
      ← polynomialValue_naturality b _ (Algebra.TensorProduct.includeRight (A := L)),
      ← polynomialValue_naturality b _ (Algebra.TensorProduct.includeRight (A := L))]
    rw [map_mul, descendedPolynomial_eval_det, descendedPolynomial_eval_det,
      descendedPolynomial_eval_det, map_mul, Matrix.det_mul]

@[simp] theorem normFromGalois_apply (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    normFromGalois b e R x = polynomialValue b (descendedPolynomial e b) R x := rfl

/-- Naturality of the constructed norm for arbitrary algebra maps. -/
theorem normFromGalois_naturality (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    normFromGalois b e S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      f (normFromGalois b e R x) :=
  polynomialValue_naturality b _ f x

/-- On any algebra over the splitting field, the constructed norm is determinant. -/
theorem normFromGalois_eq_det (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (x : R ⊗[K] A) : normFromGalois b e R x = (splittingMap e R x).det :=
  descendedPolynomial_eval_det b e R x

/-- The scalar formula over every commutative scalar algebra. -/
theorem normFromGalois_scalar (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] (r : R) :
    normFromGalois b e R (r ⊗ₜ[K] (1 : A)) = r ^ Fintype.card I := by
  apply Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective K L)
  rw [← normFromGalois_naturality b e (Algebra.TensorProduct.includeRight (A := L))]
  rw [normFromGalois_eq_det]
  have he : e (1 ⊗ₜ[K] (1 : A)) = 1 := map_one e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, splittingMap_tmul, he,
    Matrix.map_one _ (map_zero _) (map_one _)]
  simp

/-- Changing the coordinate basis leaves the norm unchanged on all test algebras. -/
theorem normFromGalois_basis_independent {J' : Type*} [Fintype J']
    (b : Module.Basis J K A) (b' : Module.Basis J' K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    normFromGalois b' e R x = normFromGalois b e R x := by
  apply Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective K L)
  rw [← normFromGalois_naturality b' e (Algebra.TensorProduct.includeRight (A := L)),
    ← normFromGalois_naturality b e (Algebra.TensorProduct.includeRight (A := L)),
    normFromGalois_eq_det, normFromGalois_eq_det]

/-- The coordinate polynomial is nonzero because the norm sends one to one. -/
theorem descendedPolynomial_basis_ne_zero (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) : descendedPolynomial e b ≠ 0 := by
  intro hP
  have h := map_one (normFromGalois b e K)
  change polynomialValue b (descendedPolynomial e b) K 1 = 1 at h
  simp only [polynomialValue, hP, eval₂_zero, zero_ne_one] at h

/-- The nonzero homogeneous coordinate polynomial has exact total degree equal to matrix size. -/
theorem descendedPolynomial_basis_totalDegree (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    (descendedPolynomial e b).totalDegree = Fintype.card I :=
  (descendedPolynomial_isHomogeneous e b).totalDegree (descendedPolynomial_basis_ne_zero b e)

/-- The induced group homomorphism on actual units. -/
def normFromGaloisUnits (b : Module.Basis J K A) (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] : (R ⊗[K] A)ˣ →* Rˣ :=
  Units.map (normFromGalois b e R).toMonoidHom

/-- The actual kernel of the constructed homomorphism on units. -/
def normFromGaloisOne (b : Module.Basis J K A) (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] : Subgroup (R ⊗[K] A)ˣ :=
  (normFromGaloisUnits b e R).ker

@[simp] theorem mem_normFromGaloisOne (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (R : Type uR) [CommRing R] [Algebra K R] (x : (R ⊗[K] A)ˣ) :
    x ∈ normFromGaloisOne b e R ↔ normFromGalois b e R (x : R ⊗[K] A) = 1 := by
  change normFromGaloisUnits b e R x = 1 ↔ _
  exact Units.ext_iff

/-- The group homomorphisms are natural for arbitrary scalar-algebra maps. -/
theorem normFromGaloisUnits_naturality (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : (R ⊗[K] A)ˣ) :
    normFromGaloisUnits b e S (Units.map
        (Algebra.TensorProduct.map f (AlgHom.id K A)).toMonoidHom x) =
      Units.map f.toMonoidHom (normFromGaloisUnits b e R x) := by
  apply Units.ext
  exact normFromGalois_naturality b e f (x : R ⊗[K] A)

end Splitting

end Langlands.ReducedNorm
