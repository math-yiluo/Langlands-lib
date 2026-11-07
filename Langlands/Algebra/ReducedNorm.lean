import Langlands.Algebra.ReducedNormComparison
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting

/-! The actual reduced norm of every finite-dimensional central simple algebra. -/

noncomputable section

namespace Langlands.CentralSimple

universe u uJ uL uR uS

open scoped TensorProduct
open Langlands.ReducedNorm

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- The reduced norm coordinate polynomial in any finite basis. -/
def reducedNormPolynomial {J : Type uJ} [Fintype J] (b : Module.Basis J K A) :
    MvPolynomial J K :=
  descendedPolynomial (finiteGaloisSplittingChart K A) b

/-- The actual reduced norm on every commutative scalar algebra. -/
def reducedNorm (R : Type uR) [CommRing R] [Algebra K R] : R ⊗[K] A →*₀ R :=
  normFromGalois (Module.finBasis K A) (finiteGaloisSplittingChart K A) R

/-- Reduced degree is positive and its square is the original dimension. -/
theorem reducedNorm_degree_spec :
    0 < reducedDegree K A ∧ Module.finrank K A = reducedDegree K A * reducedDegree K A :=
  finiteGaloisSplittingChart_spec K A

/-- The reduced norm is evaluation of its actual coordinate polynomial in every finite basis. -/
theorem reducedNorm_eq_polynomialValue {J : Type uJ} [Fintype J] (b : Module.Basis J K A)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    reducedNorm K A R x = polynomialValue b (reducedNormPolynomial K A b) R x := by
  exact (normFromGalois_basis_independent (Module.finBasis K A) b
    (finiteGaloisSplittingChart K A) R x).symm

/-- Every monomial of the reduced norm polynomial has the reduced degree. -/
theorem reducedNormPolynomial_isHomogeneous {J : Type uJ} [Fintype J]
    (b : Module.Basis J K A) :
    (reducedNormPolynomial K A b).IsHomogeneous (reducedDegree K A) := by
  simpa only [reducedNormPolynomial, Fintype.card_fin] using
    descendedPolynomial_isHomogeneous (finiteGaloisSplittingChart K A) b

/-- The coordinate polynomial is nonzero. -/
theorem reducedNormPolynomial_ne_zero {J : Type uJ} [Fintype J]
    (b : Module.Basis J K A) : reducedNormPolynomial K A b ≠ 0 :=
  descendedPolynomial_basis_ne_zero b (finiteGaloisSplittingChart K A)

/-- The coordinate polynomial has exact total degree equal to reduced degree. -/
theorem reducedNormPolynomial_totalDegree {J : Type uJ} [Fintype J]
    (b : Module.Basis J K A) :
    (reducedNormPolynomial K A b).totalDegree = reducedDegree K A := by
  simpa only [reducedNormPolynomial, Fintype.card_fin] using
    descendedPolynomial_basis_totalDegree b (finiteGaloisSplittingChart K A)

/-- Evaluating in different coordinate bases gives the same law on every test algebra. -/
theorem reducedNormPolynomial_basis_independent {J : Type uJ} [Fintype J]
    {J' : Type*} [Fintype J'] (b : Module.Basis J K A) (b' : Module.Basis J' K A)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    polynomialValue b (reducedNormPolynomial K A b) R x =
      polynomialValue b' (reducedNormPolynomial K A b') R x := by
  rw [← reducedNorm_eq_polynomialValue, ← reducedNorm_eq_polynomialValue]

/-- Naturality for every scalar-algebra map, including noninjective maps. -/
theorem reducedNorm_naturality
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    reducedNorm K A S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      f (reducedNorm K A R x) :=
  normFromGalois_naturality (Module.finBasis K A) (finiteGaloisSplittingChart K A) f x

/-- Scalars have reduced norm equal to their power by the reduced degree. -/
theorem reducedNorm_scalar (R : Type uR) [CommRing R] [Algebra K R] (r : R) :
    reducedNorm K A R (r ⊗ₜ[K] (1 : A)) = r ^ reducedDegree K A := by
  simpa only [reducedNorm, Fintype.card_fin] using
    normFromGalois_scalar (Module.finBasis K A) (finiteGaloisSplittingChart K A) R r

/-- Coefficient extension identifies the coordinate polynomial with determinant in every chart. -/
theorem reducedNormPolynomial_map_chart {J : Type uJ} [Fintype J]
    (b : Module.Basis J K A) {L : Type uL} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) :
    MvPolynomial.map (algebraMap K L) (reducedNormPolynomial K A b) =
      chartPolynomial e (fun j => 1 ⊗ₜ[K] b j) :=
  descendedPolynomial_map_chart (finiteGaloisSplittingChart K A) e b

/-- The reduced norm is determinant under every splitting chart on every further test algebra. -/
theorem reducedNorm_eq_det {L : Type uL} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (x : R ⊗[K] A) : reducedNorm K A R x = (splittingMap e R x).det :=
  normFromGalois_eq_det_of_chart (Module.finBasis K A) (finiteGaloisSplittingChart K A) e R x

/-- In particular, over the splitting field the reduced norm is the chart determinant itself. -/
theorem reducedNorm_eq_chart_det {L : Type uL} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)
    (x : L ⊗[K] A) : reducedNorm K A L x = (e x).det := by
  rw [reducedNorm_eq_det K A e L]
  congr 1
  induction x using TensorProduct.inductionOn with
  | tmul l a =>
    rw [splittingMap_tmul]
    change l • e (1 ⊗ₜ[K] a) = e (l ⊗ₜ[K] a)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Any finite Galois splitting choice and any finite basis give the constructed norm. -/
theorem reducedNorm_splitting_independent {J : Type uJ} [Fintype J]
    (b : Module.Basis J K A) {L : Type uL} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    normFromGalois b e R x = reducedNorm K A R x :=
  normFromGalois_splitting_independent (Module.finBasis K A) b
    (finiteGaloisSplittingChart K A) e R x

/-- The natural group homomorphism induced by reduced norm on actual units. -/
def reducedNormUnits (R : Type uR) [CommRing R] [Algebra K R] : (R ⊗[K] A)ˣ →* Rˣ :=
  Units.map (reducedNorm K A R).toMonoidHom

@[simp] theorem reducedNormUnits_val (R : Type uR) [CommRing R] [Algebra K R]
    (x : (R ⊗[K] A)ˣ) :
    (reducedNormUnits K A R x : R) = reducedNorm K A R (x : R ⊗[K] A) := rfl

/-- The actual norm-one subgroup of units is the kernel of reduced norm on units. -/
def reducedNormOne (R : Type uR) [CommRing R] [Algebra K R] : Subgroup (R ⊗[K] A)ˣ :=
  (reducedNormUnits K A R).ker

@[simp] theorem mem_reducedNormOne (R : Type uR) [CommRing R] [Algebra K R]
    (x : (R ⊗[K] A)ˣ) :
    x ∈ reducedNormOne K A R ↔ reducedNorm K A R (x : R ⊗[K] A) = 1 := by
  change reducedNormUnits K A R x = 1 ↔ _
  exact Units.ext_iff

/-- The group homomorphism on units is natural for every scalar-algebra map. -/
theorem reducedNormUnits_naturality
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : (R ⊗[K] A)ˣ) :
    reducedNormUnits K A S (Units.map
        (Algebra.TensorProduct.map f (AlgHom.id K A)).toMonoidHom x) =
      Units.map f.toMonoidHom (reducedNormUnits K A R x) := by
  apply Units.ext
  exact reducedNorm_naturality K A f (x : R ⊗[K] A)

end Langlands.CentralSimple
