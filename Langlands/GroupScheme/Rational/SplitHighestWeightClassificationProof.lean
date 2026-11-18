import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationStatement
import Langlands.GroupScheme.Rational.DominantHighestWeightProof
import Langlands.GroupScheme.Rational.HighestWeightIntertwiners
import Langlands.GroupScheme.Reductive.SplitBorelCellSaturation
import Langlands.GroupScheme.Reductive.IrreducibleCovariantSocle

/-! # Proof of the classification of simple representations by highest weight -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

namespace SplitPinning

open MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]

local instance splitHighestWeightClassificationProofInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Over an arbitrary field, every dominant character is realized by a coordinate. -/
theorem isRealizedWeight_of_isDominantWeight' (lam : characterLattice p.torus)
    (hlam : p.IsDominantWeight lam) : p.IsRealizedWeight lam := by
  obtain ⟨m, hm, h⟩ := p.exists_pos_nsmul_isRealizedWeight lam hlam
  exact h.of_nsmul' hm

/-- Every irreducible actual representation has a highest weight, and it is
isomorphic to the covariant socle representation of a coordinate realizing that
weight. -/
theorem exists_isHighestWeight_isRealizedBy_intertwines (ρ : MatrixRepresentation G n)
    (hρ : ρ.IsIrreducible) :
    ∃ (lam : characterLattice p.torus) (f : AffineCoordinates.algebra G),
      p.IsHighestWeight ρ lam ∧ p.IsRealizedBy lam f ∧
        ∃ C : Matrix n (Fin (Module.finrank k (Chevalley.affineCovariantSocle G f))) k,
          (Chevalley.affineCovariantSocleRepresentation G f).Intertwines ρ C ∧
            Function.Bijective C.mulVecLin := by
  obtain ⟨lam, f, hf, C, hC, hCb⟩ :=
    p.exists_isRealizedBy_intertwines_affineCovariantSocleRepresentation ρ hρ
  obtain ⟨N, hN, hNb⟩ := hC.exists_inverse hCb
  exact ⟨lam, f, hf.isHighestWeight_affineCovariantSocleRepresentation.of_intertwines hN hNb,
    hf, N, hN, hNb⟩

/-- Two coordinates realizing the same character are equal. -/
theorem IsRealizedBy.eq {lam : characterLattice p.torus} {f f' : AffineCoordinates.algebra G}
    (hf : p.IsRealizedBy lam f) (hf' : p.IsRealizedBy lam f') : f = f' := by
  have h := AffineCoordinates.eq_counit_smul_of_covariant_rightInvariant
    p.negativeBorelHom p.positiveUnipotentHom _ p.cellCoordinate_mem_nonZeroDivisors
    p.exists_factors_of_isUnit_cellCoordinate hf.1 hf.2.1 hf.2.2 hf'.1 hf'.2.1
  rw [hf'.2.2, one_smul] at h
  exact h.symm

end SplitPinning

/-- The fundamental theorem of highest weight for a split pinning over an
arbitrary field. -/
theorem splitHighestWeightClassification :
    SplitHighestWeightClassificationStatement.{u} := by
  intro k _ G _ p
  let := isAffine_of_isAffineHom G.X.hom
  refine ⟨?_, ?_, ?_⟩
  · intro lam hlam
    obtain ⟨f, hf⟩ := p.isRealizedWeight_of_isDominantWeight' lam hlam
    exact ⟨_, _, hf.isHighestWeight_affineCovariantSocleRepresentation⟩
  · intro n m ρ σ lam mu hl hm
    constructor
    · rintro ⟨C, hC, hCb⟩
      exact (hl.of_intertwines hC hCb).eq hm
    · rintro rfl
      obtain ⟨lam₁, f₁, hf₁, D₁, hD₁, hD₁b⟩ :=
        p.exists_isRealizedBy_intertwines_affineCovariantSocleRepresentation ρ hl.1
      obtain ⟨lam₂, f₂, hl₂, hf₂, C₂, hC₂, hC₂b⟩ :=
        p.exists_isHighestWeight_isRealizedBy_intertwines σ hm.1
      obtain ⟨N₁, hN₁, hN₁b⟩ := hD₁.exists_inverse hD₁b
      have e₁ : lam₁ = lam :=
        (hf₁.isHighestWeight_affineCovariantSocleRepresentation.of_intertwines hN₁ hN₁b).eq hl
      have e₂ : lam₂ = lam := hl₂.eq hm
      subst e₁ e₂
      have hff : f₁ = f₂ := hf₁.eq p hf₂
      subst hff
      exact ⟨C₂ * D₁, hD₁.comp hC₂, by
        rw [Matrix.mulVecLin_mul, LinearMap.coe_comp]
        exact hC₂b.comp hD₁b⟩
  · intro n ρ hρ
    obtain ⟨lam, f, hl, -⟩ := p.exists_isHighestWeight_isRealizedBy_intertwines ρ hρ
    exact ⟨lam, ⟨hl.isDominantWeight, hl⟩, fun mu hmu => hmu.2.eq hl⟩

end Langlands.GroupScheme
