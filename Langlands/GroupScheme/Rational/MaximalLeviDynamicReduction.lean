import Langlands.GroupScheme.Rational.MaximalLeviContainmentStatement
import Langlands.GroupScheme.Rational.MaximalLeviFiniteWeights
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Dynamic.CommutingRefinements
import Langlands.GroupScheme.Dynamic.ImproperParabolic

/-! # Maximal-Levi containment reduced to dynamic presentations of parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

theorem isIso_of_full_range {S : Scheme.{u}} {H G : GroupScheme S}
    (f : H ⟶ G) (hm : Mono f.hom.hom)
    (hf : SubgroupFunctor.range f = ⊤) : IsIso f := by
  have hfrep : (⊤ : SubgroupFunctor G).IsRepresentedBy f := ⟨hm, hf⟩
  have hidrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) :=
    ⟨inferInstance, SubgroupFunctor.range_id G⟩
  let e : H ≅ G := hfrep.isoOfIsRepresentedBy hidrep
  have he : e.hom = f := by
    simpa only [Category.comp_id] using hfrep.isoOfIsRepresentedBy_hom_comp hidrep
  rw [← he]
  infer_instance

theorem full_range_of_isIso {S : Scheme.{u}} {H G : GroupScheme S}
    (f : H ⟶ G) [IsIso f] : SubgroupFunctor.range f = ⊤ := by
  have h := SubgroupFunctor.range_iso_comp (asIso f) (𝟙 G)
  simpa only [asIso_hom, Category.comp_id, SubgroupFunctor.range_id] using h

section CommonComponent

variable {k : Type u} [Field k]
    {G P M Q L : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {lQ : L ⟶ Q}

/-- Presenting cocharacters for nested original Levis can both be placed in
the split component of the smaller Levi. The original parabolic maps remain
the representatives of their dynamic parabolics. -/
theorem exists_commonSplitComponentCocharacters_of_levi_le
    (hG : IsConnectedReductive G)
    (hl : IsRationalLeviSubgroup l) (hlQ : IsRationalLeviSubgroup lQ)
    (chi tau : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic chi).IsRepresentedBy p)
    (hQ : (Dynamic.parabolic tau).IsRepresentedBy q)
    (hle : SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (lQ ≫ q)) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
      (zeta eta : cocharacterLattice A), IsSplitComponent a ∧
      (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ a ≫ l ≫ p)).IsRepresentedBy p ∧
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ a ≫ l ≫ p) =
        SubgroupFunctor.range (l ≫ p) ∧
      (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ a ≫ l ≫ p)).IsRepresentedBy q ∧
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ a ≫ l ≫ p) =
        SubgroupFunctor.range (lQ ≫ q) := by
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  let : Mono p.hom.hom := hP.1
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  have hm : Mono (l ≫ p).hom.hom := by
    change Mono (l.hom.hom ≫ p.hom.hom)
    infer_instance
  have hMrep : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) := ⟨hm, rfl⟩
  obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement k M hl.isConnectedReductive
  obtain ⟨zeta, hzP, hzZ, -⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG chi hP ha
  obtain ⟨tauL, -, htQ⟩ := hlQ.exists_centralCocharacter_of_dynamicParabolic hG tau hQ
  have htZ := hlQ.centralizer_eq_of_dynamicParabolic hG tauL htQ
  let chi' := CommGroupScheme.groupHom zeta ≫ a ≫ l ≫ p
  let tau' := tauL ≫ lQ ≫ q
  have hchi : SubgroupFunctor.range chi' ≤ Dynamic.centralizer tau' := by
    have hchiM : SubgroupFunctor.range chi' ≤ SubgroupFunctor.range (l ≫ p) := by
      simpa only [chi', Category.assoc] using
        SubgroupFunctor.range_comp_le (CommGroupScheme.groupHom zeta ≫ a) (l ≫ p)
    exact hchiM.trans (hle.trans htZ.ge)
  have htM : SubgroupFunctor.range tau' ≤ SubgroupFunctor.range (l ≫ p) :=
    (Dynamic.range_le_centralizer_symm tau' chi' hchi).trans hzZ.le
  let tauM := hMrep.factorHom tau' htM
  have htMcomp : tauM ≫ (l ≫ p) = tau' := hMrep.factorHom_comp tau' htM
  have htMcentral : IsCentral tauM := by
    apply isCentral_of_range_le_torusCentralizer hm
    rw [htMcomp, torusCentralizer_gm_eq_dynamicCentralizer]
    exact hle.trans htZ.ge
  obtain ⟨eta, heta⟩ := ha.exists_factor isSplitTorus_gm htMcentral
  have hetaG : eta ≫ a ≫ l ≫ p = tau' := by
    rw [← Category.assoc eta a, heta]
    exact htMcomp
  refine ⟨A, a, zeta, Additive.ofMul eta, ha, hzP, hzZ, ?_, ?_⟩
  · change (Dynamic.parabolic (eta ≫ a ≫ l ≫ p)).IsRepresentedBy q
    rw [hetaG]
    exact htQ
  · change Dynamic.centralizer (eta ≫ a ≫ l ≫ p) = SubgroupFunctor.range (lQ ≫ q)
    rw [hetaG]
    exact htZ

end CommonComponent

/-- The remaining parabolic-presentation theorem suffices for the exact
maximal-Levi containment statement. This proposition retains that input. -/
def MaximalLeviContainmentFromParabolicDynamic : Prop :=
  ParabolicDynamicStatement.{u} → MaximalLeviContainmentStatement.{u}

/-- The finite-weight intermediate-parabolic argument proves the reduction,
without a root-system classification, a rank assertion, or an additional
geometric unipotent-radical hypothesis. -/
theorem maximalLeviContainment_of_parabolicDynamic :
    MaximalLeviContainmentFromParabolicDynamic.{u} := by
  intro hPD k _ G hG P M Q L p l q lQ hp hl _ hmax hq hlQ hqproper hle
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let : Mono q.hom.hom := Over.mono_of_mono_left _
  obtain ⟨chi, hchi⟩ := (hPD k G hG P p hp.isClosedSubgroup).mp hp
  obtain ⟨tau, htau⟩ := (hPD k G hG Q q hq.isClosedSubgroup).mp hq
  obtain ⟨A, a, zeta, eta, ha, hzP, hzZ, htQ, htZ⟩ :=
    exists_commonSplitComponentCocharacters_of_levi_le hG hl hlQ chi tau
      ⟨inferInstance, hchi⟩ ⟨inferInstance, htau⟩ hle
  let i := a ≫ l ≫ p
  have hproper : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ≠ ⊤ := by
    intro htop
    apply hqproper
    apply isIso_of_full_range q htQ.1
    exact htQ.2.trans (Dynamic.parabolic_eq_top_of_centralizer _ htop)
  by_contra hne
  have hlt : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) <
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) := by
    refine lt_of_le_not_ge ?_ ?_
    · simpa only [i, hzZ, htZ] using hle
    · intro hback
      apply hne
      exact le_antisymm hle (by simpa only [i, hzZ, htZ] using hback)
  obtain ⟨mu, hmuP, hmuZ, hmuproper⟩ :=
    exists_properCentralizerCoarsening ha.1.1.1 i zeta eta hlt hproper
  let Q' := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom mu ≫ i)
  let q' : Q' ⟶ G := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom mu ≫ i)
  have hq'rep : (Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i)).IsRepresentedBy q' :=
    Dynamic.Affine.isRepresentedBy_parabolicHom _
  have hq'par : IsParabolicSubgroup q' :=
    (hPD k G hG Q' q' (Dynamic.Affine.isClosedSubgroup_parabolicHom _)).mpr
      ⟨_, hq'rep.2⟩
  have hPmu : SubgroupFunctor.range p ≤
      Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) := hzP.2.le.trans hmuP
  let j : P ⟶ Q' := hq'rep.factorHom p hPmu
  have hj : j ≫ q' = p := hq'rep.factorHom_comp p hPmu
  rcases hmax Q' q' j hq'par hj with hjiso | hq'iso
  · let : IsIso j := hjiso
    have hPmu' : (Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i)).IsRepresentedBy p :=
      ⟨hzP.1, by
        rw [← hj]
        have hr : SubgroupFunctor.range (j ≫ q') = SubgroupFunctor.range q' := by
          simpa only [asIso_hom] using SubgroupFunctor.range_iso_comp (asIso j) q'
        exact hr.trans hq'rep.2⟩
    have hZmu := hl.centralizer_eq_of_dynamicParabolic hG
      (CommGroupScheme.groupHom mu ≫ a) (by
        simpa only [i, Category.assoc] using hPmu')
    have heq : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
        Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) := by
      simpa only [i, Category.assoc] using hzZ.trans hZmu.symm
    exact hmuZ.ne heq
  · let : IsIso q' := hq'iso
    have htop : Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) = ⊤ :=
      hq'rep.2.symm.trans (full_range_of_isIso q')
    exact hmuproper
      ((Dynamic.parabolic_eq_top_iff_centralizer_eq_top hG.hasTrivialUnipotentRadical _).mp htop)

end Langlands.GroupScheme
