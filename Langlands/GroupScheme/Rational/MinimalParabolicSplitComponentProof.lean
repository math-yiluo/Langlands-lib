import Langlands.GroupScheme.Rational.ParabolicSplitComponentStatements
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusCentralizerLeviProof
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.LeviRadicalCentrality
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Rational.MinimalParabolicCompatibleRefinement
import Langlands.GroupScheme.Rational.RationalCocharacterRealization
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof

/-! # Minimal parabolics and their specified split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Renard V.3.2: a rational parabolic is minimal exactly when its specified
split component, viewed in the ambient group, is a maximal split torus. -/
theorem minimalParabolicSplitComponent :
    MinimalParabolicSplitComponentStatement.{u} := by
  intro k _ G hG P j hj R r hR A a ha
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : IsClosedImmersion r.hom.hom.left := hR.1.isClosedSubgroup
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth R.X.hom := hR.1.smooth
  let hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let hrrep : (SubgroupFunctor.range r).IsRepresentedBy r :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  obtain ⟨S, s, hs, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType R a ha.1.1.isTorus ha.1.2
  obtain ⟨L, l, hl, hZ⟩ :=
    parabolicRadicalTorusCentralizerLevi k G hG P j hj R r hR S s hs
  let sL : S.toGrp ⟶ L := torusCentralizerFactor (s ≫ r ≫ j) hZ
  let aL : A.toGrp ⟶ L := f ≫ sL
  have hfac : aL ≫ l = a ≫ r := by
    apply hjrep.hom_ext
    change (f ≫ torusCentralizerFactor (s ≫ r ≫ j) hZ) ≫ l ≫ j =
      (a ≫ r) ≫ j
    rw [Category.assoc, Category.assoc, torusCentralizerFactor_comp,
      ← Category.assoc f s, hf]
  have hAL : IsSplitComponent aL := by
    refine ⟨⟨⟨ha.1.1, ?_⟩, hl.isCentral_of_factor_solvableRadical hR.1 a aL hfac⟩, ?_⟩
    · apply IsClosedSubgroup.of_comp hl.isClosedSubgroup
      rw [hfac]
      exact ha.1.2.comp hR.1.isClosedSubgroup
    · intro B b hb g hg
      let bR : B.toGrp ⟶ R :=
        hl.centralTorusRadicalFactor b hR.1 hb.1.1.isTorus hb.1.2 hb.2
      have hbR : bR ≫ r = b ≫ l :=
        hl.centralTorusRadicalFactor_comp b hR.1 hb.1.1.isTorus hb.1.2 hb.2
      have hbRclosed : IsClosedSubgroup bR :=
        hl.isClosedSubgroup_centralTorusRadicalFactor b hR.1 hb.1.1.isTorus hb.1.2 hb.2
      apply ha.2 B bR ⟨hb.1.1, hbRclosed⟩ g
      apply hrrep.hom_ext
      rw [Category.assoc, hbR, ← Category.assoc, hg, hfac]
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hj.isClosedSubgroup).mp hj
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨hjrep.1, hχ⟩
  have hamb : aL ≫ l ≫ j = a ≫ r ≫ j := by
    rw [← Category.assoc, hfac, Category.assoc]
  constructor
  · intro hmin
    rw [← hamb]
    exact hl.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic hG hmin χ hP hAL
  · intro hmax
    obtain ⟨ν, hνP, hνZ, hcent⟩ :=
      hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP hAL
    have hgeneric : IsGenericCocharacter (aL ≫ l ≫ j) ν :=
      RationalCocharacter.isGenericCocharacter_of_centralizer_eq_torusCentralizer
        ha.1.1 (aL ≫ l ≫ j) ν (hνZ.trans hcent.symm)
    have hmax' : IsMaximalSplitTorus (aL ≫ l ≫ j) := by
      rwa [hamb]
    have hmin := genericMinimalParabolic k G hG A (aL ≫ l ≫ j) hmax' ν hgeneric
    rw [← hνP.2] at hmin
    exact ⟨hj, fun Q q hq hle => hmin.2 (SubgroupFunctor.range q) ⟨Q, q, hq, rfl⟩ hle⟩

end Langlands.GroupScheme
