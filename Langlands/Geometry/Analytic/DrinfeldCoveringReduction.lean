import Langlands.Geometry.Analytic.DrinfeldFacetBarycenter
import Langlands.Geometry.Analytic.DrinfeldCoveringStatement
import Langlands.Geometry.Analytic.DrinfeldFacetDistinguishedStatement
import Langlands.Geometry.Analytic.DrinfeldReductionSurjectiveStatement

/-! # The covering and nerve, and the remaining inputs to the distinguished covering -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set
open scoped ENNReal

namespace NormClass

variable {F : Type v} [NontriviallyNormedField F]
  {V : Type w} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]

/-- A strict upper bound for the radii used in the nerve computation, in additive distance. -/
def nerveRadius (ϖ : F) (N : ℕ) : ℝ := Real.log (gapConst ϖ N)

variable {ϖ : F} (hϖ : VectorNorm.IsMaxBelowOne ϖ)
include hϖ

/-- The nerve radius is positive in positive dimension. -/
theorem nerveRadius_pos {N : ℕ} (hN : 0 < N) : 0 < nerveRadius ϖ N :=
  Real.log_pos (one_lt_gapConst hϖ hN)

/-- The open thickening of a vertex star, below the nerve radius, lies strictly within
multiplicative distance `q` of the vertex. -/
theorem distRatio_lt_of_mem_vertexNbhd {e x : NormClass F V} {ε : ℝ}
    (hε : ε < nerveRadius ϖ (Module.finrank F V)) (hx : x ∈ vertexNbhd e ε) :
    distRatio x e < ENNReal.ofReal ‖ϖ‖⁻¹ := by
  obtain ⟨y, hy, hxy⟩ := hx
  have hq : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  set lam := gapConst ϖ (Module.finrank F V) with hlam
  have hlam0 : 0 < lam := zero_lt_one.trans (one_lt_gapConst hϖ Module.finrank_pos)
  have hexp : Real.exp ε < lam := (Real.lt_log_iff_exp_lt hlam0).1 hε
  have hprod : Real.exp ε * (‖ϖ‖⁻¹ / lam) < ‖ϖ‖⁻¹ := calc
    _ < lam * (‖ϖ‖⁻¹ / lam) := mul_lt_mul_of_pos_right hexp (div_pos hq hlam0)
    _ = _ := mul_div_cancel₀ _ hlam0.ne'
  calc distRatio x e ≤ distRatio x y * distRatio y e := distRatio_le_mul x y e
    _ ≤ ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (‖ϖ‖⁻¹ / lam) :=
      mul_le_mul' hxy.le (distRatio_le_of_mem_vertexStar hϖ hy)
    _ < ENNReal.ofReal ‖ϖ‖⁻¹ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_lt_ofReal_iff hq |>.2 hprod

/-- A nonempty finite family of vertices has intersecting open star neighborhoods, at these
radii, exactly when it is a facet. -/
theorem facetNbhd_nonempty_iff_isFacet {ε : ℝ}
    (hε₀ : 0 < ε) (hε : ε < nerveRadius ϖ (Module.finrank F V))
    (S : Finset (NormClass F V)) (hS : S.Nonempty) (hver : ∀ e ∈ S, IsVertex e) :
    (facetNbhd (S : Set (NormClass F V)) ε).Nonempty ↔ IsFacet (S : Set (NormClass F V)) := by
  constructor
  · rintro ⟨x, hx⟩
    refine isFacet_of_distRatio_lt hϖ x S hS fun e he => ⟨hver e he, ?_⟩
    exact distRatio_lt_of_mem_vertexNbhd hϖ hε (mem_iInter₂.1 hx e he)
  · intro hf
    obtain ⟨x, hx⟩ := exists_mem_vertexStar_of_isFacet hϖ hf
    exact ⟨x, mem_iInter₂.2 fun e he => vertexStar_subset_vertexNbhd e hε₀ (hx e he)⟩

end NormClass

namespace DrinfeldUpperHalfSpace

open NormClass

/-- The vertex domains cover Drinfeld's upper half space for every positive radius. -/
theorem iUnion_facetDomain_singleton {F : Type v} [NontriviallyNormedField F] [IsUltrametricDist F]
    [ProperSpace F] (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra F K] {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (⋃ (e : NormClass F (Fin (d + 1) → F)) (_ : IsVertex e), facetDomain K {e} ε) = univ := by
  obtain ⟨ϖ, hϖ⟩ := VectorNorm.exists_isMaxBelowOne (F := F)
  apply eq_univ_of_forall
  intro z
  obtain ⟨e, he, hx⟩ := exists_mem_vertexStar hϖ (reduction K z)
  refine mem_iUnion₂.2 ⟨e, he, ?_⟩
  change reduction K z ∈ facetNbhd {e} ε
  apply mem_iInter₂.2
  intro e' he'
  rw [mem_singleton_iff.1 he']
  exact vertexStar_subset_vertexNbhd e hε hx

/-- The full distinguished-covering statement follows from surjectivity of the reduction map
and the compact-difference assertion for individual facets. -/
theorem distinguishedCovering_of_surjective_of_distinguished
    (hsurj : ReductionSurjectiveStatement.{u, v}) (hdis : FacetDomainDistinguishedStatement.{u, v}) :
    DistinguishedCoveringStatement.{u, v} := by
  intro F _ _ _ K _ _ _ _ d _
  obtain ⟨ϖ, hϖ⟩ := VectorNorm.exists_isMaxBelowOne (F := F)
  obtain ⟨εd, hεd, hd⟩ := hdis F K d
  let N := Module.finrank F (Fin (d + 1) → F)
  have hN : 0 < N := Module.finrank_pos
  refine ⟨min εd (nerveRadius ϖ N), lt_min hεd (nerveRadius_pos hϖ hN), fun ε hε hbound => ?_⟩
  have hεd' : ε < εd := hbound.trans_le (min_le_left _ _)
  have hεr' : ε < nerveRadius ϖ N := hbound.trans_le (min_le_right _ _)
  refine ⟨iUnion_facetDomain_singleton K hε, hd ε hε hεd', fun S hS hver => ?_⟩
  rw [facetDomain, (hsurj F K d).nonempty_preimage]
  exact facetNbhd_nonempty_iff_isFacet hϖ hε hεr' S hS hver

end DrinfeldUpperHalfSpace

end Langlands.Analytic
