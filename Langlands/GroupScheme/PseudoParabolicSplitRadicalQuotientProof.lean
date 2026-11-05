import Langlands.GroupScheme.PseudoParabolicSplitRadicalQuotientStatement
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.Dynamic.ParabolicQuotient
import Langlands.GroupScheme.SubgroupFunctor.FppfProductImage

/-! # Pseudo-parabolic descent under split-radical quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every supplied split-radical quotient carries the original pseudo-parabolic
subgroup to a pseudo-parabolic subgroup with exactly that full inverse image. -/
theorem pseudoParabolicSplitRadicalQuotient :
    PseudoParabolicSplitRadicalQuotientStatement.{u} := by
  intro k _ G H _ _ _ _ _ _ N n hn f hf P i hi
  have : Flat f.hom.hom.left := hf.1
  have : Surjective f.hom.hom.left := hf.2.1
  have : LocallyOfFinitePresentation f.hom.hom.left := hf.2.2.1
  have : Smooth N.X.hom := hn.smooth
  have : ConnectedSpace N.X.left := hn.connectedSpace
  have hker : HasSmoothConnectedUnipotentKernel f :=
    HasSmoothConnectedUnipotentKernel.of_representative n hn.isClosedSubgroup
      hn.isUnipotent hf
  have hfs : Smooth f.hom.hom.left := hker.smooth
  have : Smooth P.X.hom := hi.source_smooth
  have : ConnectedSpace P.X.left := hi.source_connectedSpace
  have : IsAffineHom P.X.hom := hi.source_isAffineHom
  obtain ⟨K, j, p, hj, hp, hpf, hps, _, hpl, _, _, _⟩ :=
    HomImage.exists_image (i ≫ f)
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj
  have hImage : SubgroupFunctor.IsFppfImage
      (SubgroupFunctor.range i) (SubgroupFunctor.range j) f :=
    ⟨P, K, i, j, p, ⟨Over.mono_of_mono_left _, rfl⟩,
      ⟨Over.mono_of_mono_left _, rfl⟩, hp.symm, hpf, hps, hpl⟩
  obtain ⟨U, r, χ, hr, hprod⟩ := hi.presentation
  obtain ⟨V, s, hs⟩ := unipotentRadicalExistence k H
  have hPar := Dynamic.parabolic_isFppfImage χ f hfs hf.2.1
  have hRad := hker.radical_isFppfImage hr hs
  have hjPseudo : IsPseudoParabolicSubgroup j :=
    ⟨inferInstance, inferInstance, inferInstance,
      V, s, χ ≫ f, hs, hprod.of_fppfImages hPar hRad hImage hj⟩
  have hker_le : SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range i := by
    rw [hf.2.2.2]
    exact (hn.range_le_unipotentRadical hr).trans hprod.right_le
  exact ⟨K, j, hjPseudo, (hImage.comap_eq_of_kernel_le hker_le).symm⟩

end Langlands.GroupScheme
