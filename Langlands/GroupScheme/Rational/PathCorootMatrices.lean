import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.PathMergedReflectionMatrices
import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.Rational.TorusFormalCharacter

/-! # Coroot points on normalized path lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k]

/-- The diagonal matrix on the `L + 1` lines `0, ..., L` with entry `t` at line `i`, entry `t⁻¹`
at line `i + 2`, and entry `1` at every other line. It is the matrix of the merged coroot point in
the normalized path basis (`normalizedPathMatrix_corootRationalPoint_adjacent`). -/
def adjacentCorootMatrix (L i : ℕ) (t : kˣ) : Matrix (Fin (L + 1)) (Fin (L + 1)) k :=
  Matrix.diagonal fun j : Fin (L + 1) =>
    if (j : ℕ) = i then (t : k) else if (j : ℕ) = i + 2 then ((t⁻¹ : kˣ) : k) else 1

/-- Unfolding `adjacentCorootMatrix` as an explicit diagonal matrix. -/
theorem adjacentCorootMatrix_eq (L i : ℕ) (t : kˣ) :
    adjacentCorootMatrix L i t = Matrix.diagonal fun j : Fin (L + 1) =>
      if (j : ℕ) = i then (t : k) else if (j : ℕ) = i + 2 then ((t⁻¹ : kˣ) : k) else 1 :=
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}

/-- A rational point of the split maximal torus acts on a weight space by the value of the
weight at that point. -/
theorem rationalMatrix_torusPoint_mulVec_of_mem {w : characterLattice p.torus} {v : d → k}
    (hv : v ∈ p.representationWeightSpace ρ w) (s : rationalPoints p.torus.toGrp) :
    (ρ.rationalMatrix (s ≫ p.inclusion.hom.hom) : Matrix d d k) *ᵥ v =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm w) s :
        k) • v := by
  let _ := p.isSplitTorus.isAffineHom
  have h := characterSpace_affine hv (CommAlgCat.of (CommRingCat.of k) k) (rationalAffinePoint s)
  rw [affineMatrix_restrict, affineUnitsEquiv_rationalAffinePoint] at h
  rw [rationalMatrix_eq_affineMatrix, rationalAffinePoint_comp]
  exact h

/-- The coroot point `r^∨(t)` acts on the weight space of `w` by `t ^ ⟨w, r^∨⟩`. -/
theorem rationalMatrix_corootRationalPoint_mulVec_of_mem (r : p.rootIndex) (t : kˣ)
    {w : characterLattice p.torus} {v : d → k} (hv : v ∈ p.representationWeightSpace ρ w) :
    (ρ.rationalMatrix (corootRationalPoint p r t) : Matrix d d k) *ᵥ v =
      ((t ^ p.rootDatum.toLinearMap w (p.rootDatum.coroot r) : kˣ) : k) • v := by
  have h := rationalMatrix_torusPoint_mulVec_of_mem hv
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
      (CommGroupScheme.groupHom (p.rootDatum.coroot r)).hom.hom)
  have heval := CocharacterUniformizer.rationalCharacterEval_cocharacterPoints
    k p.torus w (p.rootDatum.coroot r) t
  change rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm w)
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
      (CommGroupScheme.groupHom (p.rootDatum.coroot r)).hom.hom) =
      t ^ latticePairing p.torus w (p.rootDatum.coroot r) at heval
  rw [heval, ← p.isRootDatum.1] at h
  rw [← h]
  rfl

variable {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- A rational point for which every normalized path vector is an eigenvector has the diagonal
matrix of the eigenvalues in the normalized path basis. -/
theorem normalizedPathMatrix_eq_diagonal {g : rationalPoints G} (c : Fin (L + 1) → k)
    (hg : ∀ j : Fin (L + 1), (ρ.rationalMatrix g : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ j : d → k) =
      c j • (normalizedPathVector hρ hβ hlam x v₀ j : d → k)) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ g = Matrix.diagonal c := by
  ext i j
  rw [normalizedPathMatrix_apply, hg j, ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ j,
    map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- **The coroot point on the normalized path lines.** The matrix of `r^∨(t)` in the
normalized path basis is diagonal, with entry `t ^ ⟨ω_j, r^∨⟩` at the line of the path weight
`ω_j`. -/
theorem normalizedPathMatrix_corootRationalPoint (r : p.rootIndex) (t : kˣ) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ (corootRationalPoint p r t) =
      Matrix.diagonal fun j : Fin (L + 1) =>
        ((t ^ p.rootDatum.toLinearMap (pathWeight β lam j) (p.rootDatum.coroot r) : kˣ) : k) :=
  normalizedPathMatrix_eq_diagonal hρ hβ hlam x v₀ hv₀ _ fun j =>
    rationalMatrix_corootRationalPoint_mulVec_of_mem r t (normalizedPathVector hρ hβ hlam x v₀ j).2

include hβ in
/-- The coroot of the sum of two adjacent path roots is the sum of their coroots. -/
theorem adjacentRoot_coroot {i : ℕ} (hi : i + 2 ≤ L) {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) :
    p.rootDatum.coroot r = p.rootDatum.coroot (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.coroot (β ⟨i + 1, by omega⟩ : p.rootIndex) := by
  rw [adjacentRoot_eq_reflectionPerm hβ hi hr, RootPairing.coroot_reflectionPerm,
    RootPairing.coreflection_apply_coroot, hβ.pairing_succ_right (by omega : i + 1 < L),
    neg_one_smul, sub_neg_eq_add, add_comm]

include hβ in
/-- **The merged coroot on the normalized path lines.** Let `r` be the root `α_(β i) + α_(β (i+1))`
of two adjacent path vertices. Then `r^∨(t)` acts in the normalized path basis by `t` on the line
`i`, by `t⁻¹` on the line `i + 2`, and trivially on every other line: its matrix is
`adjacentCorootMatrix L i t`. -/
theorem normalizedPathMatrix_corootRationalPoint_adjacent {i : ℕ} (hi : i + 2 ≤ L)
    {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) (t : kˣ) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ (corootRationalPoint p r t) =
      adjacentCorootMatrix L i t := by
  rw [normalizedPathMatrix_corootRationalPoint, adjacentCorootMatrix_eq]
  congr 1
  funext j
  rw [adjacentRoot_coroot hβ hi hr, map_add,
    pairing_pathWeight_mk hβ hlam (by omega : (j : ℕ) ≤ L) (by omega : i < L),
    pairing_pathWeight_mk hβ hlam (by omega : (j : ℕ) ≤ L) (by omega : i + 1 < L)]
  split_ifs <;> first | omega | simp

end Langlands.GroupScheme.SplitPinning
