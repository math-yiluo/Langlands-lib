import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Reductive.DominantMultipleAssembly
import Langlands.GroupScheme.Reductive.SplitBorelCellPower
import Langlands.GroupScheme.Reductive.CovariantRegularHighestWeight

/-! # Existence of dominant highest-weight representations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance dominantHighestWeightProofIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Every dominant character has a positive multiple realized by a coordinate. -/
theorem exists_pos_nsmul_isRealizedWeight (lam : characterLattice p.torus)
    (hlam : p.IsDominantWeight lam) : ∃ n : ℕ, 0 < n ∧ p.IsRealizedWeight (n • lam) := by
  obtain ⟨n, hn, χ, f, hχ, hf⟩ := DominantMultiple.exists_pos_nsmul_mem_realizedSet p
    p.positiveCocharacter
    (fun a ha => (p.latticePairing_root_positiveCocharacter_pos_iff a).mpr
      (by rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_one_of_mem_support ha];
          exact one_pos))
    p.negativeBorelHom p.isRepresentedBy_negativeBorelHom p.torusToNegativeBorel
    p.torusToNegativeBorel_comp p.positiveUnipotentHom
    p.isRepresentedBy_positiveUnipotentHom.2.le p.isUnipotent_positiveUnipotent lam
    (fun a ha => by rw [← DominantMultiple.pairing_eq]; exact hlam ⟨a, ha⟩)
  refine ⟨n, hn, f, ?_⟩
  have hb := p.eq_borelCharacter χ
  rw [hχ] at hb
  rw [IsRealizedBy, borelCharacterCoordinate, ← hb]
  exact hf

/-- Over an algebraically closed field, every dominant character is realized. -/
theorem isRealizedWeight_of_isDominantWeight [IsAlgClosed k] (lam : characterLattice p.torus)
    (hlam : p.IsDominantWeight lam) : p.IsRealizedWeight lam := by
  obtain ⟨n, hn, h⟩ := p.exists_pos_nsmul_isRealizedWeight lam hlam
  exact h.of_nsmul hn

/-- The covariant socle of a coordinate realizing `lam` has highest weight `lam`. -/
theorem IsRealizedBy.isHighestWeight_affineCovariantSocleRepresentation
    {p : SplitPinning G} {lam : characterLattice p.torus}
    {f : AffineCoordinates.algebra G} (hf : p.IsRealizedBy lam f) :
    p.IsHighestWeight (Chevalley.affineCovariantSocleRepresentation G f) lam :=
  ⟨hf.isIrreducible, p.iSup_representationWeightSpace_eq_top _,
    (p.affineCovariantSocleRepresentation_weights hf).1,
    (p.affineCovariantSocleRepresentation_weights hf).2⟩

end SplitPinning

/-- Every dominant character of a split pinning of an actual group over an
algebraically closed field is the highest weight of an actual representation. -/
theorem splitDominantHighestWeightRepresentationsExist :
    SplitDominantHighestWeightRepresentationsExistStatement.{u} := by
  intro k _ _ G _ p lam hlam
  let := isAffine_of_isAffineHom G.X.hom
  obtain ⟨f, hf⟩ := p.isRealizedWeight_of_isDominantWeight lam hlam
  exact ⟨_, _, hf.isHighestWeight_affineCovariantSocleRepresentation⟩

end Langlands.GroupScheme
