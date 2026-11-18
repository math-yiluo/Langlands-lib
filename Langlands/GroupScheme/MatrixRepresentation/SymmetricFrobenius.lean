import Langlands.GroupScheme.MatrixRepresentation.SymmetricPower
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Langlands.GroupScheme.MatrixRepresentation.StableProjection
import Langlands.GroupScheme.MatrixRepresentation.StableComplements

/-! # The actual stable Frobenius subspace of a symmetric power -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.Algebra.SymmetricMatrix

namespace SymmetricFrobenius

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The coefficients of a pure `p`th-power monomial. -/
def powerVector (R : Type u) [CommRing R] (p : ℕ) (j : n) : Index n p → R :=
  fun a => (MvPolynomial.X j ^ p : MvPolynomial n R).coeff a.val

/-- Inclusion of the span of pure `p`th-power monomials into symmetric
coordinates. -/
def inclusion (R : Type u) [CommRing R] (p : ℕ) : Matrix (Index n p) n R :=
  fun a j => powerVector R p j a

omit [Fintype n] in
@[simp]
theorem powerVector_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (p : ℕ) (j : n) (a : Index n p) :
    g (powerVector R p j a) = powerVector S p j a := by
  classical
  simp [powerVector, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]

omit [Fintype n] in
@[simp]
theorem inclusion_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (p : ℕ) :
    (inclusion R p : Matrix (Index n p) n R).map g = inclusion S p := by
  ext a j
  exact powerVector_map g p j a

/-- The index of a pure-power monomial. -/
def pureIndex (p : ℕ) (j : n) : Index n p :=
  ⟨Finsupp.single j p, by simp⟩

/-- Positive pure powers give independent monomial coordinates. -/
theorem inclusion_mulVec_pureIndex (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
    (v : n → R) (j : n) :
    ((inclusion R p : Matrix (Index n p) n R) *ᵥ v) (pureIndex p j) = v j := by
  classical
  simp [Matrix.mulVec, dotProduct, inclusion, powerVector, pureIndex,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial,
    Finsupp.single_left_inj hp.ne', eq_comm]

/-- The pure-power inclusion is injective in every positive degree. -/
theorem inclusion_injective (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) :
    Function.Injective (inclusion R p : Matrix (Index n p) n R).mulVecLin := by
  intro v w h
  funext j
  have hj := congrFun h (pureIndex p j)
  exact (inclusion_mulVec_pureIndex R p hp v j).symm.trans
    (hj.trans (inclusion_mulVec_pureIndex R p hp w j))

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

omit [DecidableEq n] in
/-- The Frobenius formula for the actual linear substitution on pure powers,
valid also over the zero algebra and algebras with nilpotents. -/
theorem substitute_power {A : Type u} [CommRing A] [Algebra k A]
    (M : Matrix n n A) (j : n) :
    substitute M (MvPolynomial.X j ^ p) =
      ∑ i, MvPolynomial.C ((M i j) ^ p) * MvPolynomial.X i ^ p := by
  rw [map_pow, substitute_X]
  let F := characteristicPowerMap k p (MvPolynomial n A) 1
  have h := map_sum F (fun i => MvPolynomial.C (M i j) * MvPolynomial.X i) Finset.univ
  simpa only [F, characteristicPowerMap_apply, pow_one, mul_pow, ← map_pow] using h

omit [DecidableEq n] in
/-- The pure-power inclusion intertwines symmetric substitution with the
entrywise Frobenius matrix. -/
theorem matrix_mul_inclusion {A : Type u} [CommRing A] [Algebra k A]
    (M : Matrix n n A) :
    matrix M p * inclusion A p = inclusion A p * M.map (fun a => a ^ p) := by
  ext a j
  let P : MvPolynomial.homogeneousSubmodule n A p :=
    ⟨MvPolynomial.X j ^ p, MvPolynomial.isHomogeneous_X_pow (R := A) j p⟩
  have h := congrFun (matrix_mulVec M P) a
  change (matrix M p *ᵥ powerVector A p j) a =
    (substitute M (MvPolynomial.X j ^ p)).coeff a.val at h
  rw [substitute_power k p] at h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] at h
  change (∑ b, matrix M p a b * powerVector A p j b) =
    ∑ i, powerVector A p i a * (M i j) ^ p
  simpa only [Matrix.mulVec, dotProduct, powerVector, mul_comm] using h

end SymmetricFrobenius

open SymmetricFrobenius

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual Frobenius-power representation maps into the actual symmetric
power by the pure-power inclusion on every affine test. -/
theorem frobeniusPower_intertwines_symmetricPower (ρ : MatrixRepresentation G n)
    (p : ℕ) [ExpChar k p] :
    Intertwines (ρ.frobeniusPower p 1) (ρ.symmetricPower p) (inclusion k p) := by
  intro A x
  rw [symmetricPower_affineMatrix, glHom_val, inclusion_map,
    frobeniusPower_affineMatrix]
  change inclusion A p * (ρ.affineMatrix A x : Matrix n n A).map
    (fun a => a ^ p ^ 1) = _
  simp only [pow_one]
  exact (matrix_mul_inclusion k p (ρ.affineMatrix A x : Matrix n n A)).symm

/-- The Frobenius subspace in the finite symmetric coordinates. -/
def symmetricFrobeniusSubspace (k : Type u) [Field k]
    (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) :
    Submodule k (Index n p → k) :=
  LinearMap.range (inclusion k p : Matrix (Index n p) n k).mulVecLin

/-- The pure-power span is stable for the exact all-affine-test predicate. -/
theorem isStableSubspace_symmetricFrobeniusSubspace (ρ : MatrixRepresentation G n)
    (p : ℕ) [ExpChar k p] :
    (ρ.symmetricPower p).IsStableSubspace (symmetricFrobeniusSubspace k n p) :=
  (frobeniusPower_intertwines_symmetricPower ρ p).isStableSubspace_range

/-- Semisimplicity supplies a genuine all-test equivariant projection onto the
Frobenius subspace. -/
theorem exists_equivariantProjection_symmetricFrobeniusSubspace
    (ρ : MatrixRepresentation G n) (p : ℕ) [ExpChar k p]
    (hs : (ρ.symmetricPower p).IsSemisimple) :
    ∃ P : Module.End k (Index n p → k),
      (ρ.symmetricPower p).IsEquivariantProjection
        (symmetricFrobeniusSubspace k n p) P := by
  have hV := isStableSubspace_symmetricFrobeniusSubspace ρ p
  apply (exists_stable_complement_iff_exists_equivariantProjection hV).mp
  exact (isSemisimple_iff_exists_stable_complement _).mp hs _ hV

end Langlands.GroupScheme.MatrixRepresentation
