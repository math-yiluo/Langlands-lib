import Langlands.GroupScheme.Lie.TorusDeterminant
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The determinant as the dimension-weighted sum of actual Lie weights -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.AutomorphicAction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] {H U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (a : AutomorphicAction H U) {d : ℕ}
    (c : Lie.FiniteCoordinates U d) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ H)

/-- A finite enumeration of the dimension-weighted actual Lie weight indices. -/
@[instance_reducible]
def lieWeightBasisFintype : Fintype (a.lieWeightBasisIndex j) :=
  letI := a.finite_lieWeightBasisIndex c hT j
  Fintype.ofFinite _

/-- The integral sum of actual Lie weights, repeated by their weight-space dimensions. -/
def lieWeightCharacter : characterLattice T :=
  letI := a.lieWeightBasisFintype c hT j
  ∑ i : a.lieWeightBasisIndex j, i.1.val

/-- Evaluation of the dimension-weighted sum is the product of its character values. -/
theorem lieWeightCharacter_affinePoints (A : CommAlgCat.{u} (CommRingCat.of k))
    (t : Lie.AffinePoints T.toGrp A) :
    Lie.characterValue (a.lieWeightCharacter c hT j) t =
      letI := a.lieWeightBasisFintype c hT j
      ∏ i : a.lieWeightBasisIndex j, Lie.characterValue i.1.val t := by
  classical
  let := a.lieWeightBasisFintype c hT j
  change Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
    (t ≫ (CommGroupScheme.groupHom
      (∑ i : a.lieWeightBasisIndex j, i.1.val)).hom.hom) = _
  rw [comp_groupHom_sum, map_prod]
  rfl

/-- Integral cocharacter pairing distributes over the dimension-weighted sum. -/
theorem latticePairing_lieWeightCharacter (ν : cocharacterLattice T) :
    latticePairing T (a.lieWeightCharacter c hT j) ν =
      letI := a.lieWeightBasisFintype c hT j
      ∑ i : a.lieWeightBasisIndex j, latticePairing T i.1.val ν := by
  classical
  let := a.lieWeightBasisFintype c hT j
  exact map_sum ((latticePairing T).flip ν) _ _

/-- A nonzero Lie module with strictly positive actual weights has a positive weight sum. -/
theorem latticePairing_lieWeightCharacter_pos
    [Nontrivial (Additive (lieKernel U k))] (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice T, a.lieWeightSpace j χ ≠ ⊥ →
      0 < latticePairing T χ ν) :
    0 < latticePairing T (a.lieWeightCharacter c hT j) ν := by
  classical
  let := a.lieWeightBasisFintype c hT j
  rw [a.latticePairing_lieWeightCharacter c hT j]
  apply Finset.sum_pos
  · intro i _
    exact hpos i.1.val i.1.property
  · obtain ⟨i⟩ := (a.lieWeightBasis c hT j).index_nonempty
    exact ⟨i, Finset.mem_univ _⟩

/-- Strict positivity on a nonzero Lie module forces the weight character to be nonzero. -/
theorem lieWeightCharacter_ne_zero_of_pos
    [Nontrivial (Additive (lieKernel U k))] (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice T, a.lieWeightSpace j χ ≠ ⊥ →
      0 < latticePairing T χ ν) :
    a.lieWeightCharacter c hT j ≠ 0 := by
  intro hzero
  have h := a.latticePairing_lieWeightCharacter_pos c hT j ν hpos
  simp only [hzero, map_zero, LinearMap.zero_apply, lt_self_iff_false] at h

variable [IsAffine H.X.left]

/-- The actual algebraic Lie determinant restricts to the dimension-weighted character sum. -/
theorem torusCharacterRestrict_determinantCharacter :
    torusCharacterRestrict j (a.determinantCharacter c) =
      a.lieWeightCharacter c hT j := by
  classical
  let := a.lieWeightBasisFintype c hT j
  have hv (A : CommAlgCat.{u} (CommRingCat.of k))
      (t : Lie.AffinePoints T.toGrp A) :
      Lie.characterValue (torusCharacterRestrict j (a.determinantCharacter c)) t =
        Lie.characterValue (a.lieWeightCharacter c hT j) t := by
    rw [a.lieWeightCharacter_affinePoints c hT j,
      ← a.differential_det_lieWeightBasis c hT j A t]
    change Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
      (t ≫ (CommGroupScheme.groupHom
        (torusCharacterRestrict j (a.determinantCharacter c))).hom.hom) = _
    rw [groupHom_torusCharacterRestrict, Grp.comp_hom_hom, ← Category.assoc,
      a.determinantCharacter_affinePoints c A]
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  let e := AffineCoordinates.groupSchemeIso T.toGrp
  have hx :
      e.hom.hom.hom ≫
          (CommGroupScheme.groupHom
            (torusCharacterRestrict j (a.determinantCharacter c))).hom.hom =
        e.hom.hom.hom ≫
          (CommGroupScheme.groupHom (a.lieWeightCharacter c hT j)).hom.hom :=
    (Gm.affinePointsEquiv _).injective (hv _ e.hom.hom.hom)
  have key : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 T.toGrp.X := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  apply CommGroupScheme.hom_ext_points
  intro V x
  have kx : (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x := by
    rw [Category.assoc, key, Category.comp_id]
  calc
    x ≫ (CommGroupScheme.groupHom
        (torusCharacterRestrict j (a.determinantCharacter c))).hom.hom =
      (x ≫ e.inv.hom.hom) ≫
        (e.hom.hom.hom ≫ (CommGroupScheme.groupHom
          (torusCharacterRestrict j (a.determinantCharacter c))).hom.hom) := by
            rw [← Category.assoc, kx]
    _ = (x ≫ e.inv.hom.hom) ≫
        (e.hom.hom.hom ≫
          (CommGroupScheme.groupHom (a.lieWeightCharacter c hT j)).hom.hom) := by rw [hx]
    _ = x ≫ (CommGroupScheme.groupHom (a.lieWeightCharacter c hT j)).hom.hom := by
      rw [← Category.assoc, kx]

include hT in
/-- Positive actual weights on a nonzero Lie module give a nonzero restricted determinant. -/
theorem torusCharacterRestrict_determinantCharacter_ne_zero_of_pos
    [Nontrivial (Additive (lieKernel U k))] (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice T, a.lieWeightSpace j χ ≠ ⊥ →
      0 < latticePairing T χ ν) :
    torusCharacterRestrict j (a.determinantCharacter c) ≠ 0 := by
  rw [a.torusCharacterRestrict_determinantCharacter c hT j]
  exact a.lieWeightCharacter_ne_zero_of_pos c hT j ν hpos

/-- Normalizing rational points fix the dimension-weighted sum because it is a character
restriction. No finiteness of the normalizer quotient is needed. -/
theorem weylAction_lieWeightCharacter [Mono j.hom.hom.left] (n : normalizerPoints j) :
    weylAction j n (a.lieWeightCharacter c hT j) = a.lieWeightCharacter c hT j := by
  rw [← a.torusCharacterRestrict_determinantCharacter c hT j]
  exact weylAction_torusCharacterRestrict j n (a.determinantCharacter c)

end Langlands.GroupScheme.AutomorphicAction
