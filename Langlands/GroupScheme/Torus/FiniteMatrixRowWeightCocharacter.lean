import Langlands.GroupScheme.Torus.FiniteMatrixRowWeightAction
import Langlands.GroupScheme.MultiplicativePointTopology

/-! # Restricting matrix row weights to a cocharacter -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj LaurentPolynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Lie

variable {K : Type u} [Field K]

/-- A character restricted to a cocharacter is the power given by their lattice pairing. -/
theorem characterValue_cocharacter
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    (χ : characterLattice T) (ν : cocharacterLattice T)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R) :
    characterValue χ (t ≫ (CommGroupScheme.groupHom ν).hom.hom) =
      Gm.affineUnitsEquiv (CommRingCat.of K) R t ^ latticePairing T χ ν := by
  rw [← characterValue_comp]
  unfold characterValue
  rw [eq_gmEndEquiv_zsmul K (ν ≫ χ), Gm.comp_zsmul_id, map_zpow]
  rfl

end Lie

namespace splitTorus

variable {K : Type u} [Field K] {I : Type u} [Fintype I]

/-- An exponent monomial on a cocharacter evaluates by the lattice pairing. -/
theorem exponentValue_cocharacter (m : I → ℤ)
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of K)) I))
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R) :
    exponentValue I
        (algebraPointsEquiv I R (t ≫ (CommGroupScheme.groupHom ν).hom.hom))
        (Multiplicative.ofAdd m) =
      Gm.affineUnitsEquiv (CommRingCat.of K) R t ^
        latticePairing (commGroupScheme (Spec (CommRingCat.of K)) I)
          ((characterLatticeEquiv K I).symm m) ν := by
  rw [← characterValue_characterLatticeEquiv_symm, Lie.characterValue_cocharacter]

end splitTorus

namespace FiniteMatrixAlgebraTorusWeights

open FiniteAlgebraUnits FiniteAlgebraTorusWeights SplitTorusRepresentationWeights
open MatrixNormOneSplitRank (coeffTensor coeffTensor_tmul)

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {n : Type} [Fintype n] [DecidableEq n]
  {d : ℕ} {b : Module.Basis (Fin d) K (Matrix n n D)}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- The finite set of occurring full-torus weights with a specified pairing. -/
def cocharacterWeightSupport
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (c : ℤ) : Finset (I → ℤ) :=
  (weightSupport (rightRegularRepresentation b) I i).filter
    (fun m => latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
      ((splitTorus.characterLatticeEquiv K I).symm m) ν = c)

theorem mem_cocharacterWeightSupport
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (c : ℤ) (m : I → ℤ) :
    m ∈ cocharacterWeightSupport i ν c ↔
      m ∈ weightSupport (rightRegularRepresentation b) I i ∧
        latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
          ((splitTorus.characterLatticeEquiv K I).symm m) ν = c :=
  Finset.mem_filter

/-- Restriction of the row action groups its terms by their pairing with a cocharacter. -/
theorem rowActionOver_cocharacter_eq_sum
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R)
    (v : n → D) :
    rowActionOver i R (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
        (fun a => (1 : R) ⊗ₜ[K] v a) =
      ∑ m ∈ weightSupport (rightRegularRepresentation b) I i,
        fun a => ((Gm.affineUnitsEquiv (CommRingCat.of K) R t ^
          latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
            ((splitTorus.characterLatticeEquiv K I).symm m) ν : Rˣ) : R) ⊗ₜ[K]
              rowWeightProjection i m v a := by
  rw [rowActionOver_eq_sum]
  simp_rw [splitTorus.exponentValue_cocharacter]

/-- Each full-torus row weight restricts to the corresponding integer weight. -/
theorem rowActionOver_cocharacter_of_mem (m : I → ℤ) {v : n → D}
    (hv : v ∈ rowWeightSpace i m)
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R) :
    rowActionOver i R (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
        (fun a => (1 : R) ⊗ₜ[K] v a) =
      fun a => ((Gm.affineUnitsEquiv (CommRingCat.of K) R t ^
        latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
          ((splitTorus.characterLatticeEquiv K I).symm m) ν : Rˣ) : R) ⊗ₜ[K] v a := by
  rw [rowActionOver_of_mem i m hv, splitTorus.exponentValue_cocharacter]

/-- An all-test integer eigenvector is the sum of exactly the full-torus pieces
with that pairing. Coefficients at the universal Laurent unit detect this sum. -/
theorem sum_rowWeightProjection_of_cocharacter
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (c : ℤ) (v : n → D)
    (hv : ∀ (R : CommAlgCat.{u} (CommRingCat.of K))
      (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R),
      rowActionOver i R (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
          (fun a => (1 : R) ⊗ₜ[K] v a) =
        fun a => ((Gm.affineUnitsEquiv (CommRingCat.of K) R t ^ c : Rˣ) : R) ⊗ₜ[K] v a) :
    (∑ m ∈ cocharacterWeightSupport i ν c, rowWeightProjection i m v) = v := by
  classical
  let R := CommAlgCat.of (CommRingCat.of K) K[T;T⁻¹]
  let t := (Gm.affineUnitsEquiv (CommRingCat.of K) R).symm (Gm.relativeCoordUnit K)
  have ht : Gm.affineUnitsEquiv (CommRingCat.of K) R t = Gm.relativeCoordUnit K :=
    MulEquiv.apply_symm_apply _ _
  have h := hv R t
  rw [rowActionOver_cocharacter_eq_sum] at h
  funext a
  have hc := congrArg (fun w => coeffTensor D c (w a)) h
  simp only [Finset.sum_apply, map_sum, ht] at hc
  dsimp only [R] at hc
  simp only [Gm.relativeCoordUnit_zpow_val, coeffTensor_tmul, LaurentPolynomial.T_apply,
    ite_smul, one_smul, zero_smul, ite_true] at hc
  simpa only [cocharacterWeightSupport, Finset.sum_apply, Finset.sum_filter] using hc

/-- The full-torus pieces with the specified pairing contain every all-test
cocharacter eigenvector. -/
theorem mem_iSup_rowWeightSpace_of_cocharacter
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (c : ℤ) (v : n → D)
    (hv : ∀ (R : CommAlgCat.{u} (CommRingCat.of K))
      (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R),
      rowActionOver i R (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
          (fun a => (1 : R) ⊗ₜ[K] v a) =
        fun a => ((Gm.affineUnitsEquiv (CommRingCat.of K) R t ^ c : Rˣ) : R) ⊗ₜ[K] v a) :
    v ∈ ⨆ m ∈ cocharacterWeightSupport i ν c, rowWeightSpace i m := by
  rw [← sum_rowWeightProjection_of_cocharacter i ν c v hv]
  exact Submodule.sum_mem _ (fun m hm =>
    Submodule.mem_iSup_of_mem m
      (Submodule.mem_iSup_of_mem hm (rowWeightProjection_mem i m v)))

end FiniteMatrixAlgebraTorusWeights

end Langlands.GroupScheme
