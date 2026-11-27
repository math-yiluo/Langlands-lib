import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Rational.LeviCocharacterLieWeightsStatement
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityReduction
import Langlands.GroupScheme.Dynamic.RingLieProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # The Lie algebras of a parabolic, its Levi subgroup and its unipotent radical as weight spaces:
proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

theorem leviCocharacterLieWeights : LeviCocharacterLieWeightsStatement.{u} := by
  intro k _ G Q M' V _ _ _ _ q iV l' hG hq hV hl
  have : Smooth G.X.hom := hG.smooth
  have : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
  have : Mono q.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG Q q hq.isClosedSubgroup).mp hq
  obtain ⟨ψ, hψ, hP⟩ := hl.exists_centralCocharacter_of_dynamicParabolic hG χ ⟨inferInstance, hχ⟩
  have hZ := hl.centralizer_eq_of_dynamicParabolic hG ψ hP
  have hU := Dynamic.range_comp_radical_eq_unipotent_of_reductive hG (ψ ≫ l' ≫ q) q hP iV hV.1
  have hM'mono : Mono (l' ≫ q).hom.hom := by
    have : IsClosedImmersion l'.hom.hom.left := hl.isClosedSubgroup
    have : Mono l'.hom.hom := Over.mono_of_mono_left _
    rw [Grp.comp_hom_hom]
    infer_instance
  have hVmono : Mono (iV ≫ q).hom.hom := by
    have : IsClosedImmersion iV.hom.hom.left := hV.1.isClosedSubgroup
    have : Mono iV.hom.hom := Over.mono_of_mono_left _
    rw [Grp.comp_hom_hom]
    infer_instance
  have hZrep : (Dynamic.centralizer (ψ ≫ l' ≫ q)).IsRepresentedBy (l' ≫ q) := ⟨hM'mono, hZ.symm⟩
  have hUrep : (Dynamic.unipotent (ψ ≫ l' ≫ q)).IsRepresentedBy (iV ≫ q) := ⟨hVmono, hU⟩
  refine ⟨ψ, hψ, hP, ?_, ?_, ?_⟩
  · ext X
    rw [SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear hZrep]
    exact ((dynamicRingLie k G (ψ ≫ l' ≫ q) X.toMul).1).symm
  · ext X
    rw [SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear hUrep]
    exact ((dynamicRingLie k G (ψ ≫ l' ≫ q) X.toMul).2.2).symm
  · ext X
    rw [SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear hP]
    exact ((dynamicRingLie k G (ψ ≫ l' ≫ q) X.toMul).2.1).symm

end Langlands.GroupScheme
