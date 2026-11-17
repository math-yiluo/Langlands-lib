import Langlands.GroupScheme.Absolute.NoUnipotentSubgroupTorusStatement
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerProof
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison
import Langlands.GroupScheme.Dynamic.TrivialUnipotentCentralizer
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Groups without nontrivial connected unipotent subgroups are tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.25, first sentence, proved through the contracting
subgroups and centralizer of a generic cocharacter of a maximal torus. -/
theorem noUnipotentSubgroupTorus : NoUnipotentSubgroupTorusStatement.{u} := by
  intro k _ _ G _ _ _ hno
  have hpre : IsPseudoReductive G :=
    ⟨inferInstance, inferInstance, inferInstance,
      fun U i hi hs hc hu _ => hno U i hi hs hc hu⟩
  have hG : IsConnectedReductive G := hpre.isConnectedReductive_of_isAlgClosed
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hvan : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.unipotent χ = ⊥ := by
    intro χ
    let U := Dynamic.Affine.unipotentScheme χ
    let i : U ⟶ G := Dynamic.Affine.unipotentHom χ
    have hi : (Dynamic.unipotent χ).IsRepresentedBy i :=
      Dynamic.Affine.isRepresentedBy_unipotentHom χ
    rw [← hi.2]
    exact hno U i (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)
      ((dynamicSmooth k G χ U i).2.2 hi)
      (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hi)
      (dynamicUnipotentUnipotence k G χ U i hi)
  obtain ⟨T, j, hj⟩ := maximalTorusExistence k G
  have hT : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hT.exists_genericCocharacter j
  have hC : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j) = ⊤ :=
    (Dynamic.centralizer_groupHom_neg j ν).symm.trans
      ((Dynamic.centralizer_eq_parabolic_of_unipotent_eq_bot
        (CommGroupScheme.groupHom (-ν) ≫ j) (hvan _)).trans
          (Dynamic.parabolic_neg_eq_top_of_unipotent_eq_bot hT j ν (hvan _)))
  have hrange : SubgroupFunctor.range j = ⊤ := by
    rw [← algClosedMaximalTorusCentralizer k G hG T j hj,
      ← genericCentralizer k G hG T j (hj.isMaximalSplitTorus hT) ν hν]
    exact hC
  have : Mono j.hom.hom := hj.2.1.mono_overHom
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy j := ⟨inferInstance, hrange⟩
  exact hj.1.of_iso hrep.topIso.symm

end Langlands.GroupScheme
