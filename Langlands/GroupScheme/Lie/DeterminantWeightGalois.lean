import Langlands.GroupScheme.Lie.ActionBaseChange
import Langlands.GroupScheme.Lie.DeterminantWeightCharacter

/-! # The rational determinant restriction and Galois-fixed actual Lie weight sum -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Restriction

variable {k : Type u} [CommRing k]
    {H U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffine H.X.left]
    (a : AutomorphicAction H U) {d : ℕ} (c : Lie.FiniteCoordinates U d)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ H)

/-- The actual Lie determinant restricted to a possibly nonsplit commutative group. -/
def lieDeterminantCharacter : characterLattice T :=
  torusCharacterRestrict j (a.determinantCharacter c)

end Restriction

section SplitRestriction

variable {k : Type u} [Field k]
    {H U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffine H.X.left]
    (a : AutomorphicAction H U) {d : ℕ} (c : Lie.FiniteCoordinates U d)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ H)

/-- Over a field, splitness identifies the restricted determinant with the actual
dimension-weighted sum of Lie weights. -/
theorem lieDeterminantCharacter_eq_lieWeightCharacter
    (hT : IsSplitTorus T.toGrp) :
    a.lieDeterminantCharacter c j = a.lieWeightCharacter c hT j :=
  a.torusCharacterRestrict_determinantCharacter c hT j

end SplitRestriction

section BaseChange

variable (k K : Type u) [CommRing k] [Field K] [Algebra k K]
    {H U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffine H.X.left]
    (a : AutomorphicAction H U) {d : ℕ} (c : Lie.FiniteCoordinates U d)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ H)

local notation "b" => algebraBaseMap k K
local notation "H_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) H
local notation "U_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) U
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "j_K" =>
  CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) j

local instance : IsAffineHom (U_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd U.X.hom b)
  infer_instance

local instance : IsAffine (H_K).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback H.X.hom b)
  infer_instance

/-- Actual restricted determinant characters commute with scheme base change,
independently of the coordinate choices and their ranks. -/
theorem lieDeterminantCharacter_baseChange {e : ℕ}
    (cK : Lie.FiniteCoordinates U_K e) :
    characterLattice.baseChange b T (a.lieDeterminantCharacter c j) =
      (a.baseChange b).lieDeterminantCharacter (T := T_K) cK j_K := by
  unfold lieDeterminantCharacter
  rw [characterLattice.baseChange_torusCharacterRestrict,
    a.determinantCharacter_baseChange k K c cK]

/-- The actual dimension-weighted Lie character over a splitting extension is
the base change of the original restricted rational determinant character. -/
theorem lieWeightCharacter_eq_baseChange_lieDeterminantCharacter {e : ℕ}
    (cK : Lie.FiniteCoordinates U_K e) (hT : IsSplitTorus (T_K).toGrp) :
    (a.baseChange b).lieWeightCharacter (k := K) (T := T_K) cK hT j_K =
      characterLattice.baseChange b T (a.lieDeterminantCharacter c j) := by
  have h := torusCharacterRestrict_determinantCharacter
    (k := K) (H := H_K) (U := U_K) (T := T_K) (a.baseChange b) cK hT j_K
  change (a.baseChange b).lieWeightCharacter (k := K) (T := T_K) cK hT j_K = _
  rw [← h]
  exact (a.lieDeterminantCharacter_baseChange k K c j cK).symm

include c in
/-- Every endomorphism of the extension base over the original base fixes the
actual dimension-weighted Lie character by canonical transport. -/
theorem transport_lieWeightCharacter {e : ℕ}
    (cK : Lie.FiniteCoordinates U_K e) (hT : IsSplitTorus (T_K).toGrp)
    (τ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (hτ : τ ≫ b = b) :
    characterLattice.transport b τ hτ T
        ((a.baseChange b).lieWeightCharacter (k := K) (T := T_K) cK hT j_K) =
      (a.baseChange b).lieWeightCharacter (k := K) (T := T_K) cK hT j_K := by
  rw [a.lieWeightCharacter_eq_baseChange_lieDeterminantCharacter k K c j cK hT]
  exact characterLattice.transport_baseChange b τ hτ _

include c in
/-- Every algebra automorphism fixes the actual weighted Lie character under the
published Galois representation. No finiteness or Galois-extension hypothesis is needed. -/
theorem galoisRepresentation_lieWeightCharacter {e : ℕ}
    (cK : Lie.FiniteCoordinates U_K e) (hT : IsSplitTorus (T_K).toGrp)
    (σ : K ≃ₐ[k] K) :
    characterLattice.galoisRepresentation k K T σ
        ((a.baseChange b).lieWeightCharacter (k := K) (T := T_K) cK hT j_K) =
      (a.baseChange b).lieWeightCharacter (k := K) (T := T_K) cK hT j_K := by
  rw [a.lieWeightCharacter_eq_baseChange_lieDeterminantCharacter k K c j cK hT]
  exact characterLattice.galoisRepresentation_baseChange k K T σ _

/-- Positive actual weights on a nonzero extended Lie module force the original
restricted determinant character to be nonzero. -/
theorem lieDeterminantCharacter_ne_zero_of_baseChange_pos {e : ℕ}
    (cK : Lie.FiniteCoordinates U_K e) (hT : IsSplitTorus (T_K).toGrp)
    [Nontrivial (Additive (lieKernel U_K K))] (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      (a.baseChange b).lieWeightSpace (R := CommRingCat.of K) (T := T_K) j_K χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    a.lieDeterminantCharacter c j ≠ 0 := by
  intro hz
  have hn := lieWeightCharacter_ne_zero_of_pos
    (k := K) (H := H_K) (U := U_K) (T := T_K)
    (a.baseChange b) cK hT j_K ν hpos
  apply hn
  rw [a.lieWeightCharacter_eq_baseChange_lieDeterminantCharacter k K c j cK hT,
    hz, map_zero]

end BaseChange

end Langlands.GroupScheme.AutomorphicAction
