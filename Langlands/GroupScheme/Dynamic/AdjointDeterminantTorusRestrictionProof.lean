import Langlands.GroupScheme.Dynamic.AdjointDeterminantTorusRestrictionStatement
import Langlands.GroupScheme.Lie.TorusDeterminant
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # The actual adjoint determinant restricted to a split torus -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AutomorphicAction

variable {k : Type u} [Field k] {H U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (a : AutomorphicAction H U) {d : ℕ}
    (c : Lie.FiniteCoordinates U d) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ H)

/-- Algebraic characters agree if their values agree on every affine test. -/
private theorem character_ext_affine [IsAffine T.X.left]
    {χ ψ : rationalCharacters T.toGrp}
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (t : Lie.AffinePoints T.toGrp A),
      Lie.characterValue ((rationalCharacters.equivCharacterLattice T) χ) t =
      Lie.characterValue ((rationalCharacters.equivCharacterLattice T) ψ) t) : χ = ψ := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  let e := (Grp.forget _).mapIso (AffineCoordinates.coordinateCogroupIso T.toGrp)
  apply (cancel_epi e.hom).mp
  exact (Gm.affinePointsEquiv _).injective (h (AffineCoordinates.algebra T.toGrp) e.hom)

include hT in
/-- The algebraic determinant restriction is the sum of the collected basis weights. -/
theorem determinantCharacter_restrict_eq_basisSum [IsAffine H.X.left]
    [Fintype (a.lieWeightBasisIndex j)] [DecidableEq (a.lieWeightBasisIndex j)] :
    characterRestrict j (a.determinantCharacter c) =
      ∑ i : a.lieWeightBasisIndex j,
        (rationalCharacters.equivCharacterLattice T).symm i.1.val := by
  classical
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  apply character_ext_affine
  intro A t
  change Gm.affinePointsEquiv _
    (t ≫ (characterRestrict j (a.determinantCharacter c)).toMul.hom.hom) = _
  rw [characterRestrict_apply, Grp.comp_hom_hom, ← Category.assoc]
  have hd := a.determinantCharacter_affinePoints c
    (CommAlgCat.of (CommRingCat.of k) A) (t ≫ j.hom.hom)
  refine hd.trans ?_
  rw [a.differential_det_lieWeightBasis c hT j A t]
  change _ = Lie.characterValue (∑ i : a.lieWeightBasisIndex j, i.1.val) t
  rw [Lie.characterValue, comp_groupHom_sum, map_prod]
  rfl

local instance instAdjointDeterminantTorusRestrictionProof1 [Fintype {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥}] :
    Fintype (a.lieWeightBasisIndex j) := by
  unfold lieWeightBasisIndex
  infer_instance

include c hT in
/-- Collecting equal basis weights gives the finite root sum, with zero weight omitted. -/
theorem basisSum_eq_rootSum
    [Fintype {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥}] :
    (∑ i : a.lieWeightBasisIndex j,
      (rationalCharacters.equivCharacterLattice T).symm i.1.val) =
      ∑ᶠ α ∈ a.lieRoots j, Module.finrank k (a.lieWeightSpace j α) •
        (rationalCharacters.equivCharacterLattice T).symm α := by
  classical
  let S : Set (characterLattice T) := {α | a.lieWeightSpace j α ≠ ⊥}
  have hs : S.Finite := a.finite_lieWeightSupport_of_finiteCoordinates c hT j
  rw [finsum_mem_eq_sum_of_inter_support_eq
    (f := fun α => Module.finrank k (a.lieWeightSpace j α) •
      (rationalCharacters.equivCharacterLattice T).symm α)
    (t := hs.toFinset) (by
      ext α
      by_cases hα : α = 0
      · subst α
        simp
      · simp [lieRoots, hα, S])]
  rw [Finset.sum_subtype (p := fun α => a.lieWeightSpace j α ≠ ⊥)
    (F := (inferInstance : Fintype {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥}))
    hs.toFinset (fun α => hs.mem_toFinset)]
  change (∑ i : (Σ α : {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥},
    Fin (Module.finrank k (a.lieWeightSpace j α.val))),
    (rationalCharacters.equivCharacterLattice T).symm i.1.val) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rfl

include c hT in
/-- The determinant of an actual action restricts to the sum of its roots with multiplicities. -/
theorem determinantCharacter_restrict_eq_rootSum [IsAffine H.X.left] :
    characterRestrict j (a.determinantCharacter c) =
      ∑ᶠ α ∈ a.lieRoots j, Module.finrank k (a.lieWeightSpace j α) •
        (rationalCharacters.equivCharacterLattice T).symm α := by
  classical
  let := (a.finite_lieWeightSupport_of_finiteCoordinates c hT j).fintype
  exact (a.determinantCharacter_restrict_eq_basisSum c hT j).trans
    (a.basisSum_eq_rootSum c hT j)

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.Dynamic

/-- The root-multiplicity formula for the actual adjoint determinant character. -/
theorem adjointDeterminantTorusRestriction :
    AdjointDeterminantTorusRestrictionStatement.{u} := by
  intro k _ G χ P U iP iU hP hU _ _ d c T hT j
  exact ⟨(parabolicAdjointAction hP hU).finite_lieRoots_of_finiteCoordinates c hT j,
    (parabolicAdjointAction hP hU).determinantCharacter_restrict_eq_rootSum c hT j⟩

end Langlands.GroupScheme.Dynamic
