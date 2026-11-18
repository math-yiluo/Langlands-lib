import Langlands.GroupScheme.Reductive.NegativeBorelEigenCovector
import Langlands.GroupScheme.Reductive.CovectorRegularEmbedding
import Langlands.GroupScheme.Reductive.CovariantTensorEmbedding
import Langlands.GroupScheme.Reductive.CovariantUnipotentFixedLine
import Langlands.GroupScheme.Rational.HighestWeightIntertwiners

/-! # Every irreducible representation is a covariant socle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace SplitPinning

open MatrixRepresentation AffineCoordinates Chevalley

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]

local instance irreducibleCovariantSocleInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Every irreducible actual representation of a group with a split pinning is
isomorphic, by a bijective actual intertwiner, to the covariant socle
representation of a coordinate realizing some torus character. -/
theorem exists_isRealizedBy_intertwines_affineCovariantSocleRepresentation
    (ρ : MatrixRepresentation G n) (hρ : ρ.IsIrreducible) :
    ∃ (lam : characterLattice p.torus) (f : AffineCoordinates.algebra G),
      p.IsRealizedBy lam f ∧
        ∃ C : Matrix (Fin (Module.finrank k (affineCovariantSocle G f))) n k,
          ρ.Intertwines (affineCovariantSocleRepresentation G f) C ∧
            Function.Bijective C.mulVecLin := by
  classical
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    obtain ⟨x, y, hxy⟩ := (hρ.1 : Nontrivial (n → k))
    exact hxy (funext fun i => isEmptyElim i)
  obtain ⟨ξ, lam, hξ0, hξ⟩ := p.exists_negativeBorel_eigenCovector ρ
  obtain ⟨V, d, b, hV, C, hC, hCb, hF⟩ :=
    exists_affineRegular_bijective_matrixCoefficient G ρ hρ hξ0
  -- The finite regular subspace is left covariant for the negative Borel subgroup.
  have hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam) := by
    intro w hw
    obtain ⟨v, hv⟩ := hCb.2 (b.equivFun ⟨w, hw⟩)
    have hw' : w = affineRegularCoordinateMap G V b (C *ᵥ v) := by
      rw [← Matrix.mulVecLin_apply, hv]
      change w = ((b.equivFun.symm (b.equivFun ⟨w, hw⟩) : V) : algebra G)
      rw [LinearEquiv.symm_apply_apply]
    rw [hw', hF v]
    exact matrixCoefficient_mem_leftCovariantSubspace ρ ξ v p.negativeBorelHom _ hξ
  -- It is nonzero, since the source representation is nonzero.
  have hV0 : V ≠ ⊥ := by
    intro hbot
    have hd : IsEmpty (Fin d) := by
      refine ⟨fun i => b.ne_zero i ?_⟩
      exact Subtype.ext ((Submodule.eq_bot_iff V).mp hbot _ (b i).2)
    obtain ⟨j⟩ := hne
    have h1 := hCb.1 (a₁ := (Pi.single j (1 : k) : n → k)) (a₂ := 0)
      (funext fun i => isEmptyElim i)
    have h2 := congrFun h1 j
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    exact one_ne_zero h2
  -- A normalized positive-unipotent fixed vector gives a realizing coordinate.
  obtain ⟨v₀, hv₀fix, hv₀1, -⟩ :=
    affineRegularRepresentation_exists_normalized_fixedVector G V b hV p.negativeBorelHom
      p.positiveUnipotentHom p.isUnipotent_positiveUnipotent _ hcov hV0
      p.cellCoordinate_mem_nonZeroDivisors p.exists_factors_of_isUnit_cellCoordinate
  set f := affineRegularCoordinateMap G V b v₀ with hf_def
  have hf : p.IsRealizedBy lam f :=
    ⟨hcov (affineRegularCoordinateMap_mem G V b v₀),
      affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector G V b hV
        p.positiveUnipotentHom hv₀fix, hv₀1⟩
  refine ⟨lam, f, hf, ?_⟩
  -- The covariant socle of `f` sits inside `V`, and the inclusion is bijective.
  have hSV : affineCovariantSocle G f ≤ V :=
    affineCovariantSocle_le_of_nonzero_rightAct_mem G p.negativeBorelHom
      p.positiveUnipotentHom p.isUnipotent_positiveUnipotent _ V hV hcov hV0
      p.cellCoordinate_mem_nonZeroDivisors p.exists_factors_of_isUnit_cellCoordinate
      hf.1 hf.2.1 hf.2.2
  let := (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  let bS := Module.finBasis k (affineCovariantSocle G f)
  have hD := intertwines_affine_coactionCoordinates G (affineCovariantSocle G f) V bS b
    (rightAct_mem_affineCovariantSocle G f) hV hSV
  let D := coactionCoordinates V b fun j => (bS j : AffineCoordinates.algebra G)
  have hDinj : Function.Injective D.mulVecLin :=
    coactionCoordinates_mulVecLin_injective (affineCovariantSocle G f) V bS b hSV
  have hirr : (affineRegularRepresentation G V b hV).IsIrreducible :=
    hC.isIrreducible_of_bijective hρ hCb
  have hDsurj : Function.Surjective D.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    rcases hirr.2 _ hD.isStableSubspace_range with h | h
    · exfalso
      have hS0 := affineCovariantSocle_ne_bot G hf.2.2
      have : Nontrivial (affineCovariantSocle G f) := Submodule.nontrivial_iff_ne_bot.mpr hS0
      have : Nonempty (Fin (Module.finrank k (affineCovariantSocle G f))) := bS.index_nonempty
      obtain ⟨i⟩ := this
      have h1 : D.mulVecLin (Pi.single i 1) = D.mulVecLin 0 := by
        rw [map_zero]
        have hm : D.mulVecLin (Pi.single i 1) ∈ LinearMap.range D.mulVecLin :=
          LinearMap.mem_range_self _ _
        rw [h, Submodule.mem_bot] at hm
        exact hm
      have h2 := congrFun (hDinj h1) i
      rw [Pi.single_eq_same, Pi.zero_apply] at h2
      exact one_ne_zero h2
    · exact h
  obtain ⟨E, hE, hEb⟩ := hD.exists_inverse ⟨hDinj, hDsurj⟩
  refine ⟨E * C, hC.comp hE, ?_⟩
  rw [Matrix.mulVecLin_mul, LinearMap.coe_comp]
  exact hEb.comp hCb

end SplitPinning

end Langlands.GroupScheme
