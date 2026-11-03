import Langlands.GroupScheme.Rational.GeneralLinearLatticeCentralizer
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit

/-! # Generic cocharacters of the diagonal torus and their centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]
variable (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

/-- Pairing the root of `(i, j)` with a cocharacter subtracts its two weights. -/
theorem latticePairing_rootDatum_root_fintype (ν : cocharacterLattice 𝔻)
    (p : {p : n × n // p.1 ≠ p.2}) :
    latticePairing 𝔻 ((rootDatum n k).root p) ν =
      cocharacterCoordEquiv n k ν p.1.1 - cocharacterCoordEquiv n k ν p.1.2 := by
  rw [latticePairing_coord, characterCoordEquiv_rootDatum_root, sum_rootCoord_mul]

/-- A cocharacter of the diagonal torus is generic exactly when its weights
are pairwise distinct. -/
theorem isGenericCocharacter_diagonalTorus_iff (ν : cocharacterLattice 𝔻) :
    IsGenericCocharacter (diagonalTorus n (CommRingCat.of k)) ν ↔
      Function.Injective (cocharacterCoordEquiv n k ν) := by
  constructor
  · intro hν i j hij
    by_contra hne
    let p : {p : n × n // p.1 ≠ p.2} := ⟨(i, j), hne⟩
    have hp : (rootDatum n k).root p ∈ relativeRoots (diagonalTorus n (CommRingCat.of k)) := by
      change (rootDatum n k).root p ∈ roots (diagonalTorus n (CommRingCat.of k))
      rw [roots_diagonalTorus]
      exact ⟨i, j, hne, characterLatticeEquiv_rootDatum_root p⟩
    apply hν _ hp
    rw [latticePairing_rootDatum_root_fintype]
    exact sub_eq_zero.mpr hij
  · intro hν χ hχ
    change χ ∈ roots (diagonalTorus n (CommRingCat.of k)) at hχ
    rw [roots_diagonalTorus] at hχ
    obtain ⟨i, j, hij, hχ⟩ := hχ
    let p : {p : n × n // p.1 ≠ p.2} := ⟨(i, j), hij⟩
    have hχp : χ = (rootDatum n k).root p := by
      apply (splitTorus.characterLatticeEquiv k (ULift.{u} n)).injective
      exact hχ.trans (characterLatticeEquiv_rootDatum_root p).symm
    rw [hχp, latticePairing_rootDatum_root_fintype]
    exact sub_ne_zero.mpr (fun h => hij (hν h))

/-- The dynamic Levi of a generic cocharacter of the diagonal torus equals
the centralizer of the whole torus on every test scheme. -/
theorem dynamicCentralizer_diagonalTorus_of_isGeneric
    (ν : cocharacterLattice 𝔻)
    (hν : IsGenericCocharacter (diagonalTorus n (CommRingCat.of k)) ν) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ diagonalTorus n (CommRingCat.of k)) =
      torusCentralizer
        (T := 𝔻) (diagonalTorus n (CommRingCat.of k)) := by
  apply dynamicCentralizer_eq_torusCentralizer_of_injective_weights
    (diagonalTorus n (CommRingCat.of k)) (CommGroupScheme.groupHom ν)
    ((isGenericCocharacter_diagonalTorus_iff k ν).1 hν)
  · intro U t
    rw [pointsEquiv_diagonalTorus_val]
    exact Matrix.isDiag_diagonal _
  · exact cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points k
      (diagonalTorus n (CommRingCat.of k))
      (fun _ t => pointsEquiv_diagonalTorus_val t) ν
  · exact centralizer_diagonalCocharacter n (CommRingCat.of k) _

end Langlands.GroupScheme.GeneralLinear
