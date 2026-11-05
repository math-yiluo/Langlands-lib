import Langlands.GroupScheme.PseudoParabolicQuotientSplitRadicalReduction
import Langlands.GroupScheme.PseudoParabolicQuotientReductionStatement
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.Dynamic.ParabolicQuotient
import Langlands.GroupScheme.HomogeneousQuotientFactorization
import Langlands.GroupScheme.SubgroupFunctor.FppfProductKernel
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Pseudo-parabolic quotients as dynamic-parabolic quotients of pseudo-reductive groups

The proof of CGP Proposition 2.2.10 in the Library's homogeneous-quotient interface: a
supplied quotient of `G` by a pseudo-parabolic `P_G(λ) R_{u,k}(G)` descends to the
pseudo-reductive quotient `G' = G/R_{u,k}(G)`, where its fibers are the cosets of
`P_{G'}(π ∘ λ)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- CGP Proposition 2.2.10 with Corollary 2.1.9: every supplied homogeneous quotient of a
smooth connected affine group by a pseudo-parabolic subgroup is a homogeneous quotient of a
pseudo-reductive group by an actual dynamic parabolic. -/
theorem pseudoParabolicQuotientPseudoReductiveReduction :
    PseudoParabolicQuotientPseudoReductiveReductionStatement.{u} := by
  intro k _ G P i hP Q q hqs hqsurj hqqc hfib
  have : Smooth G.X.hom := hP.smooth
  have : ConnectedSpace G.X.left := hP.connectedSpace
  have : IsAffineHom G.X.hom := hP.isAffineHom
  obtain ⟨U, j, χ, hj, hprod⟩ := hP.presentation
  obtain ⟨G', π, hπ, hG'⟩ := unipotentRadicalQuotient k G U j hj
  have : Smooth G'.X.hom := hG'.smooth
  have : IsAffineHom G'.X.hom := hG'.isAffineHom
  have : ConnectedSpace G'.X.left := hG'.connectedSpace
  have : Flat π.hom.hom.left := hπ.1
  have : Surjective π.hom.hom.left := hπ.2.1
  have : LocallyOfFinitePresentation π.hom.hom.left := hπ.2.2.1
  have : Smooth U.X.hom := hj.smooth
  have : ConnectedSpace U.X.left := hj.connectedSpace
  have hπs : Smooth π.hom.hom.left :=
    (HasSmoothConnectedUnipotentKernel.of_representative j hj.isClosedSubgroup
      hj.isUnipotent hπ).smooth
  have : QuasiCompact π.hom.hom.left := by
    have : QuasiCompact (π.hom.hom.left ≫ G'.X.hom) := by
      rw [Over.w π.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp π.hom.hom.left G'.X.hom
  -- Corollary 2.1.9: `π` maps `P_G(χ)` onto `P_{G'}(χ ≫ π)` fppf-locally.
  have hPar := Dynamic.parabolic_isFppfImage χ π hπs hπ.2.1
  -- Hence `P = P_G(χ) R_{u,k}(G)` is the full preimage of `P_{G'}(χ ≫ π)`.
  have hpre : SubgroupFunctor.range i = (Dynamic.parabolic (χ ≫ π)).comap π := by
    have key : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range i).carrier T ↔
          x ∈ ((Dynamic.parabolic (χ ≫ π)).comap π).carrier T := by
      intro T x
      rw [hprod.mem_range_iff T x, ← hπ.2.2.2, SubgroupFunctor.mem_comap]
      exact hPar.fppfLocallyInProduct_kernel_iff x
    apply le_antisymm
    · intro T x hx
      exact (key T x).mp hx
    · intro T x hx
      exact (key T x).mpr hx
  obtain ⟨H₁, K₁, i₁, j₁, p₁, -, hj₁, -, -, -, -⟩ := hPar
  have : Mono j₁.hom.hom := hj₁.1
  have hpre' : SubgroupFunctor.range i = (SubgroupFunctor.range j₁).comap π := by
    rw [hj₁.2]
    exact hpre
  have hker : SubgroupFunctor.range (kernelι π) ≤ SubgroupFunctor.range i :=
    HomogeneousQuotientFactorization.kernel_le_of_comap π (SubgroupFunctor.range i) j₁ hpre'
  let q' : G'.X ⟶ Q :=
    HomogeneousQuotientFactorization.desc π (SubgroupFunctor.range i) q hfib hker
  have hfac : π.hom.hom ≫ q' = q :=
    HomogeneousQuotientFactorization.fac_desc π (SubgroupFunctor.range i) q hfib hker
  have he : π.hom.hom.left ≫ q'.left = q.left := congrArg (fun a => a.left) hfac
  refine ⟨G', χ ≫ π, q', hG', ?_, ?_, ?_, ?_⟩
  · have : Smooth (π.hom.hom.left ≫ q'.left) := by
      rw [he]
      exact hqs
    exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      π.hom.hom.left q'.left
  · have : Surjective (π.hom.hom.left ≫ q'.left) := by
      rw [he]
      exact hqsurj
    exact Surjective.of_comp π.hom.hom.left q'.left
  · have : QuasiCompact (π.hom.hom.left ≫ q'.left) := by
      rw [he]
      exact hqqc
    exact PseudoParabolicQuotientSplitRadicalReduction.quasiCompact_of_surjective_comp π.hom.hom.left q'.left
  · intro T g h
    rw [← hj₁.2]
    exact HomogeneousQuotientFactorization.desc_fibers π (SubgroupFunctor.range i) q hfib hker
      j₁ hpre' T g h

end Langlands.GroupScheme
