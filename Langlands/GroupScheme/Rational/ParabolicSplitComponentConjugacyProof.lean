import Langlands.GroupScheme.Rational.ParabolicSplitComponentStatements
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusInitialCentralizerLeviProof
import Langlands.GroupScheme.Rational.ReductiveParabolicContraction
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Rational.TorusUnipotentLiftConjugacy
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.Rational.CentralTorusFixedness

/-! # Unipotent conjugacy of parabolic split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The specified unipotent radical acts transitively on the maximal split
tori of the specified solvable radical of a rational parabolic. -/
theorem parabolicSplitComponentConjugacy :
    ParabolicSplitComponentConjugacyStatement.{u} := by
  intro k _ G hG P j hj R r hr U u hu A A' a a' ha ha'
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom P.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth R.X.hom := hr.1.smooth
  let : ConnectedSpace R.X.left := hr.1.connectedSpace
  let : IsClosedImmersion u.hom.hom.left := hu.1.isClosedSubgroup
  let : Mono u.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom U.X.hom := by
    rw [← Over.w u.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hu.1.smooth
  let : ConnectedSpace U.X.left := hu.1.connectedSpace
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hj.isClosedSubgroup).mp hj
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨inferInstance, hχ⟩
  have hU : (Dynamic.unipotent χ).IsRepresentedBy (u ≫ j) := by
    refine ⟨?_, Dynamic.range_comp_radical_eq_unipotent_of_reductive hG χ j hP u hu.1⟩
    change Mono (u.hom.hom ≫ j.hom.hom)
    infer_instance
  have hsplit : RelativeRoot.IsSplitUnipotent U :=
    Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χ hU
      (hu.1.isClosedSubgroup.comp hj.isClosedSubgroup)
  obtain ⟨S, s, hs, L, l, hl, hcent⟩ :=
    parabolicRadicalTorusInitialCentralizerLevi k G hG P j hj R r hr
  obtain ⟨U₀, u₀, q, hu₀, hmul, hlq, hker⟩ :=
    hl.exists_unipotentRadical_retraction
  have hcentral : IsCentral (r ≫ q) :=
    hr.1.isSolvableGroupScheme.isCentral_comp_split
      hl.isConnectedReductive l q r hlq hr.1.isNormal
  have hkernel : SubgroupFunctor.range u = SubgroupFunctor.range (kernelι q) := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [mem_range_kernelι_iff, hker, hu₀.1.range_eq hu.1]
  have hconj : SubgroupConjugate a a' :=
    smoothMaximalSplitTorusConjugacy k R A A' a a' ha ha'
  obtain ⟨g, e, he⟩ := hconj.postcomp r
  have heq : (a ≫ r) ≫ q = (e.hom ≫ (a' ≫ r)) ≫ q := by
    have h := congrArg (fun f : A.toGrp ⟶ P => f ≫ q) he
    rw [Category.assoc, innerIso_hom_comp, ← Category.assoc,
      (show IsCentral ((a ≫ r) ≫ q) from
        by simpa only [Category.assoc] using hcentral.comp a).comp_innerIso_hom] at h
    exact h
  refine ⟨QuotientHomCocycle.splitUnipotentTorusConjugator
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
    u q hkernel hu.1.isUnipotent hsplit (a ≫ r) (e.hom ≫ (a' ≫ r)) heq
    ha.1.1.isTorus, e, ?_⟩
  simpa only [Category.assoc] using
    QuotientHomCocycle.splitUnipotentTorusConjugator_conjugates
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
      u q hkernel hu.1.isUnipotent hsplit (a ≫ r) (e.hom ≫ (a' ≫ r)) heq
      ha.1.1.isTorus

end Langlands.GroupScheme
