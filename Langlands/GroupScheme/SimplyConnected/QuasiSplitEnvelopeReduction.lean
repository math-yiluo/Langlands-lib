import Langlands.GroupScheme.SimplyConnected.QuasiSplitEnvelopeStatement
import Langlands.GroupScheme.Rational.MaximalSplitSubgroupStatement
import Langlands.GroupScheme.SimplyConnected.NonmultipliableCorootSpanStatement
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.TorusCentralizerQuasiSplit
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.DynamicReflectionCell

/-! # The quasi-split envelope from Borel–Tits 7.2 and the nonmultipliable coroot span -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The split subgroup of Borel–Tits 7.2 of a simply connected group is simply connected and
quasi-split once the nonmultipliable relative coroots span the cocharacter lattice. -/
theorem simplyConnectedQuasiSplitEnvelope_of_maximalSplitSubgroup
    (hBT : MaximalSplitSubgroupStatement.{u})
    (hHL : NonmultipliableCorootSpanStatement.{u}) :
    SimplyConnectedQuasiSplitEnvelopeStatement.{u} := by
  intro k _ G hG S i hi
  have hGr := hG.isSemisimple.isConnectedReductive
  obtain ⟨F, hF, j, f, hj, hfj, hf, hroots⟩ := hBT k G hGr S i hi
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have := hF.isAffineHom
  have := hGr.isAffineHom
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k F hF S hS f hf
  have hcoroot : P.corootSpan ℤ = ⊤ := by
    refine hHL k G hG S i hi J P hP.1 ?_ ?_
    · rw [hP.2.1]
      exact hroots
    · intro α
      obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
      refine ⟨n ≫ j.hom.hom, σ, ?_, hσ⟩
      have h := hn.comp_hom j
      rwa [hfj] at h
  have hFss : IsSemisimple F := by
    refine (splitSemisimpleRootDatum k F hF S hS f hf J P hP).2.mpr ?_
    rw [hcoroot]
    infer_instance
  have hFsc : IsSimplyConnected F :=
    splitCorootSpanSimplyConnected k F hFss S hS f hf J P hP hcoroot
  have hFqs : IsQuasiSplit F := by
    have : IsClosedImmersion f.hom.hom.left := hf.2.1
    have hrep : (torusCentralizer f).IsRepresentedBy f :=
      ⟨Over.mono_of_mono_left _, (maximalTorusCentralizer k F hF S f hf).symm⟩
    exact hS.isQuasiSplit_of_torusCentralizer hF f f hrep hf.1
  refine ⟨F, j, f, hFsc, hFqs, hj, ?_, hfj⟩
  apply IsMaximalSplitTorus.of_comp hj
  rw [hfj]
  exact hi

end Langlands.GroupScheme
