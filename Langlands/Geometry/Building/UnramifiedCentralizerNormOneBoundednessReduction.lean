import Langlands.Geometry.Building.UnramifiedTorusNormOneBoundedness
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof

/-! # Reducing norm-one centralizer boundedness to Henselian quasi-splitness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme

/-- Any supplied representative of the centralizer of a maximal split torus
in a quasi-split group is a torus. -/
theorem IsQuasiSplit.isTorus_of_represents_maximalSplitTorusCentralizer
    {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsQuasiSplit G) {a : A.toGrp ⟶ G}
    (ha : IsMaximalSplitTorus a) {j : Z ⟶ G}
    (hj : (torusCentralizer a).IsRepresentedBy j) :
    IsTorus Z := by
  obtain ⟨A₀, a₀, C, c, ha₀, hc, _, hC⟩ :=
    quasiSplitTorusCentralizerExistence k G hG
  obtain ⟨g, e, he⟩ :=
    (maximalSplitTorusConjugacy k G hG.isConnectedReductive).1 A₀ A a₀ a ha₀ ha
  have hc' := hc.torusCentralizer_of_iso_square e (G.innerIso g) he
  exact IsTorus.of_iso (hj.isoOfIsRepresentedBy hc') hC

end Langlands.GroupScheme

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The generic Henselian discrete quasi-splitness theorem suffices for the
exact norm-one centralizer boundedness target. -/
def CentralizerNormOneBoundedHenselianReductionStatement : Prop :=
  HenselianDiscreteQuasiSplitStatement.{u} → CentralizerNormOneBoundedStatement.{u}

/-- Unramified quasi-splitness identifies the supplied centralizer as a torus,
so the proved torus bound applies with the exact target data. -/
theorem centralizerNormOneBounded_of_unramifiedQuasiSplit
    (h : UnramifiedQuasiSplitStatement.{u}) :
    CentralizerNormOneBoundedStatement.{u} := by
  intro F _ _ _ _ G _ C
  apply centralizerNormOneBounded_of_isTorus F G C
  exact (h F G C.isConnectedReductive).isTorus_of_represents_maximalSplitTorusCentralizer
    C.isMaximalSplitTorus C.centralizer.isRepresentedBy

/-- The structural reduction uses the published Henselian specialization and
the proved norm-one torus bound, with no completeness assumption on the fixed field. -/
theorem centralizerNormOneBounded_of_henselianDiscreteQuasiSplit :
    CentralizerNormOneBoundedHenselianReductionStatement.{u} := by
  intro h
  exact centralizerNormOneBounded_of_unramifiedQuasiSplit
    (unramifiedQuasiSplit_of_henselianDiscrete h)

end Langlands.Geometry.Building.MaximalUnramified
