import Langlands.GroupScheme.Rational.RelativeRank
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Rational.SplitRankReduction
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Rational character coordinates and intrinsic ranks of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Integral character coordinates associated with an actual splitting of a torus. -/
def splitTorusCharacterCoordinates {I : Type u} [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) :
    characterLattice T ≃+ (I → ℤ) :=
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  (characterLattice.congr eC).trans (splitTorus.characterLatticeEquiv k I)

/-- Rational character coordinates associated with an actual splitting of a torus. -/
def splitTorusRationalCharacterCoordinates {I : Type u} [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) :
    (ℚ ⊗[ℤ] characterLattice T) ≃ₗ[ℚ] (I → ℚ) :=
  tensorEquivPi (splitTorusCharacterCoordinates e)

@[simp] theorem splitTorusRationalCharacterCoordinates_tmul {I : Type u} [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (q : ℚ) (χ : characterLattice T) :
    splitTorusRationalCharacterCoordinates e (q ⊗ₜ[ℤ] χ) =
      fun j => (splitTorusCharacterCoordinates e χ j : ℚ) * q :=
  tensorEquivPi_tmul _ q χ

/-- The rationalized full character lattice of any split torus is finite dimensional. -/
theorem IsSplitTorus.finite_characterLatticeRat (hT : IsSplitTorus T.toGrp) :
    Module.Finite ℚ (ℚ ⊗[ℤ] characterLattice T) := by
  have := hT.finite_characterLattice
  infer_instance

/-- Every actual relative root span in a split torus is finite dimensional. -/
theorem IsSplitTorus.finite_relativeRootSpan (hT : IsSplitTorus T.toGrp)
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) :
    Module.Finite ℚ (relativeRootSpan i) := by
  have := hT.finite_characterLatticeRat
  infer_instance

/-- The rationalized rational-character module of a connected reductive group is
finite dimensional. -/
theorem IsConnectedReductive.finite_rationalCharactersRat (hG : IsConnectedReductive G) :
    Module.Finite ℚ (ℚ ⊗[ℤ] rationalCharacters G) := by
  have := (rationalCharacterLattice k G hG).2
  infer_instance

/-- The intrinsic lattice rank is the cardinality of any finite splitting index. -/
theorem splitTorusRank_eq_card_of_splitting {I : Type u} [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) :
    splitTorusRank T = Nat.card I := by
  let := Fintype.ofFinite I
  rw [splitTorusRank, (splitTorusRationalCharacterCoordinates e).finrank_eq]
  simp [Nat.card_eq_fintype_card]

/-- The intrinsic lattice rank equals the splitting-independent rank of a split torus. -/
theorem IsSplitTorus.rank_eq_splitTorusRank (hT : IsSplitTorus T.toGrp) :
    hT.rank = splitTorusRank T := by
  obtain ⟨hI, ⟨e⟩⟩ := hT.choose_spec
  have := hI
  exact (hT.rank_eq_card hT.choose e).trans (splitTorusRank_eq_card_of_splitting e).symm

/-- The lattice rank of a split torus agrees with its own split rank. -/
theorem IsSplitTorus.splitRank_eq_splitTorusRank (hT : IsSplitTorus T.toGrp) :
    splitRank T.toGrp = (splitTorusRank T : ℕ∞) := by
  rw [← hT.rank_eq_splitTorusRank]
  exact hT.rank_eq_splitRank.symm

/-- Every closed split subtorus gives a lower bound for the ambient split rank. -/
theorem IsSplitSubtorus.splitTorusRank_le_splitRank {i : T.toGrp ⟶ G}
    (hi : IsSplitSubtorus i) : (splitTorusRank T : ℕ∞) ≤ splitRank G := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.1
  have := hI
  rw [splitTorusRank_eq_card_of_splitting e]
  exact hi.card_le_splitRank I e

end Langlands.GroupScheme
