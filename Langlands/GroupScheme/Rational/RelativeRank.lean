import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.StandardParabolic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Actual relative root ranks and rational character restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Rank of the full character lattice after rationalization. For a split torus
this is its split rank; no root-span quotient is taken. -/
def splitTorusRank (T : CommGroupScheme (Spec (CommRingCat.of k))) : ℕ :=
  Module.finrank ℚ (ℚ ⊗[ℤ] characterLattice T)

/-- Rank of the actual rational character module of a group scheme. -/
def rationalCharacterRank (G : GroupScheme (Spec (CommRingCat.of k))) : ℕ :=
  Module.finrank ℚ (ℚ ⊗[ℤ] rationalCharacters G)

variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational scalar extension of restriction of the actual group-scheme characters. -/
def rationalCharacterRestrictRat (f : H ⟶ G) :
    (ℚ ⊗[ℤ] rationalCharacters G) →ₗ[ℚ] (ℚ ⊗[ℤ] rationalCharacters H) :=
  (characterRestrict f).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalCharacterRestrictRat_tmul (f : H ⟶ G) (q : ℚ)
    (χ : rationalCharacters G) :
    rationalCharacterRestrictRat f (q ⊗ₜ[ℤ] χ) = q ⊗ₜ[ℤ] characterRestrict f χ := rfl

@[simp] theorem rationalCharacterRestrictRat_toRat (f : H ⟶ G) (χ : rationalCharacters G) :
    rationalCharacterRestrictRat f (toRat χ) = toRat (characterRestrict f χ) := rfl

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Relative semisimple rank, measured on the published span of all actual
relative roots, including nonreduced roots. -/
def relativeRootRank (i : T.toGrp ⟶ G) : ℕ :=
  Module.finrank ℚ (relativeRootSpan i)

/-- The actual vector in the relative root span corresponding to a simple root
for the chosen cocharacter. -/
def simpleRelativeRootVector (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (α : simpleRelativeRoots i ν) : relativeRootSpan i :=
  ⟨toRat α.1, toRat_mem_ratSpan α.2.1.1⟩

@[simp] theorem coe_simpleRelativeRootVector (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (α : simpleRelativeRoots i ν) :
    (simpleRelativeRootVector i ν α : ℚ ⊗[ℤ] characterLattice T) = toRat α.1 := rfl

/-- The full rationalized character rank of the actual split torus has the
expected value, also for the empty index type. -/
theorem splitTorusRank_splitTorus (I : Type u) [Finite I] :
    splitTorusRank (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) = Nat.card I := by
  let := Fintype.ofFinite I
  rw [splitTorusRank, (tensorEquivPi (splitTorus.characterLatticeEquiv k I)).finrank_eq]
  simp [Nat.card_eq_fintype_card]

end Langlands.GroupScheme
