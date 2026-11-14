import Langlands.GroupScheme.Rational.ParabolicSplitComponentStatements
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Rational.LeviRadicalCentrality
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # A rational Levi split component is maximal split in the parabolic radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The split component of a rational Levi factors through the specified
parabolic radical as a maximal split torus (Renard V.3.1). -/
theorem leviSplitComponentRadical : LeviSplitComponentRadicalStatement.{u} := by
  intro k _ G hG P j hj R r hr L l hl A aL hA
  have hjc : IsClosedSubgroup j := hj.isClosedSubgroup
  let : IsClosedImmersion j.hom.hom.left := hjc
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hjc).mp hj
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨hjrep.1, hχ⟩
  obtain ⟨_, _, _, hcent⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP hA
  have hlj : IsClosedSubgroup (l ≫ j) := hl.isClosedSubgroup.comp hjc
  let : IsClosedImmersion (l ≫ j).hom.hom.left := hlj
  have hljrep : (SubgroupFunctor.range (l ≫ j)).IsRepresentedBy (l ≫ j) :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let a := hl.centralTorusRadicalFactor aL hr.1 hA.1.1.1.isTorus hA.1.1.2 hA.1.2
  have ha : a ≫ r = aL ≫ l :=
    hl.centralTorusRadicalFactor_comp aL hr.1 hA.1.1.1.isTorus hA.1.1.2 hA.1.2
  refine ⟨a, ha, ⟨hA.1.1.1,
    hl.isClosedSubgroup_centralTorusRadicalFactor aL hr.1
      hA.1.1.1.isTorus hA.1.1.2 hA.1.2⟩, ?_⟩
  intro B b hb f hf
  have hbG : IsSplitSubtorus (b ≫ r ≫ j) :=
    hb.comp (hr.1.isClosedSubgroup.comp hjc)
  have hfG : f ≫ (b ≫ r ≫ j) = aL ≫ l ≫ j := by
    rw [← Category.assoc f b, hf, ← Category.assoc a r, ha, Category.assoc]
  have hcontained : SubgroupFunctor.range (b ≫ r ≫ j) ≤
      SubgroupFunctor.range (l ≫ j) := by
    rw [← hcent]
    exact range_le_torusCentralizer_of_factor _ _ f hfG
  let bL := (hbG.factorInClosedSubgroup hlj hcontained).val
  have hbL : bL ≫ (l ≫ j) = b ≫ r ≫ j :=
    hbG.factorInClosedSubgroup_comp hlj hcontained
  have hbLP : bL ≫ l = b ≫ r := by
    apply hjrep.hom_ext
    simpa only [Category.assoc] using hbL
  have hbLc : IsCentral bL :=
    hl.isCentral_of_factor_solvableRadical hr.1 b bL hbLP
  apply hA.2 B bL
    ⟨hbG.isSplitSubtorus_factorInClosedSubgroup hlj hcontained, hbLc⟩ f
  apply hljrep.hom_ext
  rw [Category.assoc, hbL, hfG]

end Langlands.GroupScheme
