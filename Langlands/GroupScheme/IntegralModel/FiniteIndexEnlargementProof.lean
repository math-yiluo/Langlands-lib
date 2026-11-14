import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.Core
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.Bridge
import Langlands.GroupScheme.RelativeIdentityComponent.OpenSubgroup

/-! # Finite-index enlargement of smooth integral group models: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open FiniteIndexEnlargement

/-- **KP Proposition A.7.1, finite-index part.** Over a Henselian discrete valuation ring with
algebraically closed residue field, a smooth affine model `M` of a smooth affine generic group and
a subgroup `V` of generic points containing the integral points of `M` as a normal subgroup of
finite index admit a smooth model `N` with integral points `V`, together with an open inclusion of
`M` into `N` extending the identity of the generic group that preserves relative identity
components. -/
theorem finiteIndexEnlargement : FiniteIndexEnlargementStatement.{u} := by
  intro R _ _ _ _ _ K _ _ _ G _ _ M hM V hMV hnorm hfin
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let A := AffineCoordinates.hopfAlgebra M.group
  let e := AffineCoordinates.hopfSpecIso M.group
  have : Algebra.Smooth R A := coordinate_smooth M hM
  let ev : rationalPoints G →* WithConv (A →ₐ[R] K) := (evaluationEquiv M A e).toMonoidHom
  have hU : ∀ x, x ∈ M.integralPoints ↔ ∀ a, ev x a ∈ (algebraMap R K).range :=
    fun x => mem_integralPoints_iff M A e x
  have hsurj : ∀ σ : A →ₐ[R] R, ∃ u, (ev u).ofConv = (Algebra.ofId R K).comp σ := by
    intro σ
    refine ⟨M.integralPointMap ((sectionEquiv M.group A e).symm (toConv σ)), ?_⟩
    change (evaluationEquiv M A e _).ofConv = _
    rw [evaluationEquiv_integralPointMap, MulEquiv.apply_symm_apply]
  obtain ⟨B, iB, hBsm, hbij, hopen, hpts⟩ :=
    exists_hopf_enlargement ev M.integralPoints hU hsurj V hMV
  let N := reconstructedModel M A e B iB hbij hBsm
  let j := reconstructedHom M A e B iB hbij hBsm
  have hN : N.IsSmooth := reconstructedModel_isSmooth M A e B iB hbij hBsm
  have hj : IsOpenImmersion j.hom.hom.hom.left :=
    reconstructedHom_isOpenImmersion M A e B iB hbij hBsm hopen
  refine ⟨N, j, hN, ?_, hj, ?_⟩
  · ext g
    rw [reconstructedModel_mem_integralPoints_iff]
    exact hpts g
  · intro C i hi
    have : Smooth N.group.X.hom := hN
    exact RelativeIdentityComponent.comp_open j.hom i hi

end Langlands.GroupScheme.IntegralModel
