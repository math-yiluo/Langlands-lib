import Langlands.GroupScheme.Rational.MinimalParabolicTorusSplitPartStatement
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusLeviStatement
import Langlands.GroupScheme.Rational.MinimalParabolicLeviCentralizerStatement
import Langlands.GroupScheme.Rational.CentralTorusSplitTransfer

/-! # Reduction of the minimal-parabolic split-part theorem to rational Levi geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The two explicit rational-Levi geometry statements imply the unchanged
minimal-parabolic torus split-part statement. -/
theorem minimalParabolicTorusSplitPartStatement_of_radical_torus_levi
    (hRadical : ParabolicRadicalTorusLeviStatement.{u})
    (hLevi : MinimalParabolicLeviCentralizerStatement.{u}) :
    MinimalParabolicTorusSplitPartStatement.{u} := by
  intro k _ G hG P j hj T t ht f hf A a ha
  obtain ⟨R, r, hR, S, sT, sR, hsT, hsR, hdiagram, hintersection,
    L, l, sL, hl, hcentralizer, hsL, hz⟩ :=
    hRadical k G hG P j hj.1 T t ht f hf
  obtain ⟨B, bR, hB, hC⟩ := hLevi k G hG P j hj L l hl R r hR
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hjc : IsClosedSubgroup (l ≫ j) :=
    hl.isClosedSubgroup.comp hj.1.isClosedSubgroup
  have : IsClosedImmersion (l ≫ j).hom.hom.left := hjc
  have hrep : (torusCentralizer (bR ≫ r ≫ j)).IsRepresentedBy (l ≫ j) :=
    ⟨Over.mono_of_mono_left _, hC.symm⟩
  have hcomm : sT ≫ t = sL ≫ (l ≫ j) := by
    simpa only [Category.assoc, hf] using
      (congrArg (fun q => q ≫ j) hsL).symm
  have hle : SubgroupFunctor.range (l ≫ j) ≤ SubgroupFunctor.range j := by
    intro U g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨x ≫ l.hom.hom, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc]
  exact ha.ambient_transfer_of_centralizer_center t ht.2.1 sT sL
    hz.isClosedSubgroup hz.greatest (l ≫ j) hjc hcomm
    (bR ≫ r ≫ j) hB hrep hle

/-- The explicit conditional reduction, without asserting either geometric
premise. -/
def MinimalParabolicTorusSplitPartReductionStatement : Prop :=
  ParabolicRadicalTorusLeviStatement.{u} →
    MinimalParabolicLeviCentralizerStatement.{u} →
      MinimalParabolicTorusSplitPartStatement.{u}

/-- The uniform conditional reduction to the two rational-Levi inputs. -/
theorem minimalParabolicTorusSplitPartReduction :
    MinimalParabolicTorusSplitPartReductionStatement.{u} :=
  minimalParabolicTorusSplitPartStatement_of_radical_torus_levi

end Langlands.GroupScheme
