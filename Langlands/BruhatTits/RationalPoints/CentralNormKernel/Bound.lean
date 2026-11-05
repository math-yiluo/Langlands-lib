import Langlands.BruhatTits.RationalPoints.CentralNormKernel.CentralUnipotent
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.CentralJordan
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.BaseChange
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.Norm
import Langlands.GroupScheme.Reductive.FiniteCenterReflection

/-! # Bounded matrix entries of central norm-kernel points

Let `F` be a nonarchimedean local field and `ρ` a closed linear embedding of an affine group
scheme `M` of finite type over `F` whose base change to the algebraic closure `K` has trivial
unipotent radical. The matrix entries of the central points of the rational common norm kernel
are bounded.

For such a point `z`, its base change `z_K` is central, and `ρ_K(z_K) = s ρ_K(u)` with
`s = ∑ λ i E i` the block-scalar matrix of its eigenvalues and `u` a central point with unipotent
matrix. The points `u` range over a finite set. The eigenvalues `λ i` are eigenvalues of `ρ(z)`,
so they have spectral norm one. Each entry of `ρ(z)` is `∑ λ i (E i ρ_K(u))_{kl}`, whose spectral
norm is at most `∑ i ‖(E i ρ_K(u))_{kl}‖`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open Langlands.GroupScheme Langlands.GroupScheme.CentralIntersection

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

theorem spectralNorm_sum_le {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] {J : Type*} (s : Finset J) (g : J → L) :
    spectralNorm K L (∑ i ∈ s, g i) ≤ ∑ i ∈ s, spectralNorm K L (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spectralNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg).trans (add_le_add le_rfl ih)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

set_option maxHeartbeats 800000 in
/-- **Entry bound.** The matrix entries of the central points of the rational common norm kernel
are bounded. -/
theorem exists_entry_bound {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]
    [LocallyOfFiniteType M.X.hom] (hU : HasTrivialUnipotentRadical (closureGroup M))
    {N : Type} [Fintype N] [DecidableEq N] (ρ : MatrixRepresentation M N)
    [IsClosedImmersion ρ.hom.hom.left] :
    ∃ C : ℝ, letI := LocalGalois.localNormedField F
      ∀ z ∈ GroupScheme.schemeCenterPoints M ⊓ Plancherel.rationalCommonNormKernel M,
        ∀ k l, ‖(ρ.rationalMatrix z : Matrix N N F) k l‖ ≤ C := by
  let := LocalGalois.localNormedField F
  have : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  have : CompleteSpace F := LocalGalois.localNormedField_complete F
  have : IsAffine (closureGroup M).X.left := by
    change IsAffine (pullback M.X.hom (closureBase F))
    exact isAffine_of_isAffineHom (pullback.snd M.X.hom (closureBase F))
  have : LocallyOfFiniteType (closureGroup M).X.hom := by
    change LocallyOfFiniteType (pullback.snd M.X.hom (closureBase F))
    infer_instance
  have hMKaff : IsAffineHom (closureGroup M).X.hom := by
    change IsAffineHom (pullback.snd M.X.hom (closureBase F))
    infer_instance
  have := isClosedImmersion_closureRep ρ
  obtain ⟨Z, z₀, hz₀⟩ := schemeTheoreticCenterExistence_of_isAffineHom hMKaff
  have hfin := finite_centralUnipotent hU z₀ hz₀ (closureRep ρ)
  obtain ⟨D⟩ := nonempty_spectralData (AlgebraicClosure F) (CentralAlgebra (closureRep ρ))
  let f : rationalPoints (closureGroup M) → N → N → Fin D.r → ℝ := fun u k l i =>
    spectralNorm F (AlgebraicClosure F)
      ((blockIdem D i * ((closureRep ρ).rationalMatrix u : Matrix N N (AlgebraicClosure F))) k l)
  have hf0 : ∀ u k l i, 0 ≤ f u k l i := fun _ _ _ _ => spectralNorm_nonneg _
  refine ⟨∑ u ∈ hfin.toFinset, ∑ k, ∑ l, ∑ i, f u k l i, ?_⟩
  intro z hz k l
  obtain ⟨hzc, hzK⟩ := Subgroup.mem_inf.1 hz
  have hzc' := closurePoint_mem_center hzc
  obtain ⟨u, huc, hun, hdec⟩ := exists_central_unipotent_decomposition D hzc'
  have hu : u ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨huc, hun⟩
  have hρK : ((closureRep ρ).rationalMatrix (closurePoint z) : Matrix N N (AlgebraicClosure F)) =
      (ρ.rationalMatrix z : Matrix N N F).map (algebraMap F (AlgebraicClosure F)) := by
    rw [closureRep_rationalMatrix]
    rfl
  have hentry : algebraMap F (AlgebraicClosure F) ((ρ.rationalMatrix z : Matrix N N F) k l) =
      ∑ i, (blockEigenvalues D hzc' i : AlgebraicClosure F) *
        (blockIdem D i * ((closureRep ρ).rationalMatrix u :
          Matrix N N (AlgebraicClosure F))) k l := by
    have h1 := congrArg (fun M' : Matrix N N (AlgebraicClosure F) => M' k l) hρK
    simp only [Matrix.map_apply] at h1
    rw [← h1, hdec, semisimpleMatrix_mul_apply]
  have hlam : ∀ i, spectralNorm F (AlgebraicClosure F)
      (blockEigenvalues D hzc' i : AlgebraicClosure F) = 1 := by
    intro i
    refine spectralNorm_eq_one_of_mem_normKernel ρ hzc hzK ?_
    have h := D.isRoot_charpoly_χ (centralVal (closureRep ρ))
      (centralVal_injective (closureRep ρ)) (centralElement (closureRep ρ) hzc') i
    rw [centralVal_centralElement, hρK, Matrix.charpoly_map] at h
    exact h
  rw [← spectralNorm_extends (L := AlgebraicClosure F), hentry]
  calc spectralNorm F (AlgebraicClosure F) (∑ i, (blockEigenvalues D hzc' i : AlgebraicClosure F) *
        (blockIdem D i * ((closureRep ρ).rationalMatrix u :
          Matrix N N (AlgebraicClosure F))) k l)
      ≤ ∑ i, spectralNorm F (AlgebraicClosure F)
          ((blockEigenvalues D hzc' i : AlgebraicClosure F) *
            (blockIdem D i * ((closureRep ρ).rationalMatrix u :
              Matrix N N (AlgebraicClosure F))) k l) := spectralNorm_sum_le _ _
    _ ≤ ∑ i, f u k l i := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _)
          (Algebra.IsAlgebraic.isAlgebraic _)).trans ?_
        rw [hlam i, one_mul]
    _ ≤ ∑ l', ∑ i, f u k l' i :=
        Finset.single_le_sum (f := fun l' => ∑ i, f u k l' i)
          (fun _ _ => Finset.sum_nonneg fun _ _ => hf0 _ _ _ _) (Finset.mem_univ l)
    _ ≤ ∑ k', ∑ l', ∑ i, f u k' l' i :=
        Finset.single_le_sum (f := fun k' => ∑ l', ∑ i, f u k' l' i)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf0 _ _ _ _)
          (Finset.mem_univ k)
    _ ≤ ∑ u' ∈ hfin.toFinset, ∑ k', ∑ l', ∑ i, f u' k' l' i :=
        Finset.single_le_sum (f := fun u' => ∑ k', ∑ l', ∑ i, f u' k' l' i)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => hf0 _ _ _ _) hu

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
