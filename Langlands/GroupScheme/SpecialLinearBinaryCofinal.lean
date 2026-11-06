import Langlands.GroupScheme.SpecialLinearBinaryRegularAction

/-! # Cofinal irreducibility for the actual binary covariant spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

variable {k : Type u} [Field k]

local instance : IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

local instance : IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  SpecialLinear.isAffineHom_groupScheme _ _

local instance : IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance : IsAffineHom (groupScheme (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme _

/-- The entire actual covariant space at the cofinal Steinberg degree has its monomial basis. -/
def cofinalCovariantBasis (p e : ℕ) :
    Module.Basis (Fin (p ^ e - 1 + 1)) k
      (AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ (p ^ e - 1))) :=
  covariantBasis (p ^ e - 1)

/-- The exact cofinal irreducibility clause of the big-cell statement holds for binary SL. -/
theorem cofinal_covariantRegularRepresentation_isIrreducible
    (p : ℕ) [Fact p.Prime] [CharP k p] [Infinite k] :
    ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
          (characterCoordinate k ^ e'))),
      (Chevalley.affineRegularRepresentation
        (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace
          (inclusion (CommRingCat.of k)) (characterCoordinate k ^ e') f
          hv)).rationalRepresentation.IsIrreducible := by
  intro e
  refine ⟨p ^ e - 1, ?_, p ^ e - 1 + 1, cofinalCovariantBasis p e, ?_⟩
  · have h : e < p ^ e := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    omega
  · exact covariantRegularRepresentation_isIrreducible (k := k) p e

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
