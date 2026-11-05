import Langlands.GroupScheme.SubgroupFunctor.FppfProductKernel
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionReduction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.AffineLineRigidity
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.SemigroupQuotientTransport
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof
import Langlands.GroupScheme.Rational.DynamicSemigroupProof

/-! # Local products from affine-line rigidity of the radical quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Inclusion

variable {k : Type u} [Field k]
    {G U V : GroupScheme (Spec (CommRingCat.of k))}
    {j : U ⟶ G} {n : V ⟶ G}

/-- The canonical homomorphism from a represented split radical into a
represented ordinary radical, obtained from their all-test containment. -/
def IsSplitUnipotentRadical.inclusionInRadical
    (hn : IsSplitUnipotentRadical n) (hj : IsUnipotentRadical j) : V ⟶ U := by
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  exact (show (SubgroupFunctor.range j).IsRepresentedBy j from
    ⟨Over.mono_of_mono_left _, rfl⟩).factorHom n (hn.range_le_unipotentRadical hj)

/-- The canonical inclusion recovers the specified split radical inclusion. -/
theorem IsSplitUnipotentRadical.inclusionInRadical_comp
    (hn : IsSplitUnipotentRadical n) (hj : IsUnipotentRadical j) :
    hn.inclusionInRadical hj ≫ j = n := by
  unfold inclusionInRadical
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The canonical inclusion of the split radical into the ordinary radical is closed. -/
theorem IsSplitUnipotentRadical.isClosedSubgroup_inclusionInRadical
    (hn : IsSplitUnipotentRadical n) (hj : IsUnipotentRadical j) :
    IsClosedSubgroup (hn.inclusionInRadical hj) :=
  IsClosedSubgroup.of_comp hj.isClosedSubgroup (by
    rw [hn.inclusionInRadical_comp hj]
    exact hn.isClosedSubgroup)

/-- The canonical inclusion has normal full all-test image in the ordinary radical. -/
theorem IsSplitUnipotentRadical.isNormal_inclusionInRadical
    (hn : IsSplitUnipotentRadical n) (hj : IsUnipotentRadical j) :
    (SubgroupFunctor.range (hn.inclusionInRadical hj)).IsNormal := by
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  rw [← range_comp_comap_of_mono (hn.inclusionInRadical hj) j, hn.inclusionInRadical_comp hj]
  exact hn.isNormal.comap j

/-- An actual smooth connected affine quotient of the ordinary radical by the
canonical split radical inclusion exists over every field. -/
theorem IsSplitUnipotentRadical.exists_quotient_inRadical [IsAffineHom G.X.hom]
    (hn : IsSplitUnipotentRadical n) (hj : IsUnipotentRadical j) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : U ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧ ConnectedSpace Q.X.left ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (hn.inclusionInRadical hj)) q := by
  let : Smooth U.X.hom := hj.smooth
  let : ConnectedSpace U.X.left := hj.connectedSpace
  let : IsAffineHom U.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G U j hj.isClosedSubgroup
  obtain ⟨Q, q, hsm, ha, hq⟩ := normalSubgroupQuotient k U V (hn.inclusionInRadical hj)
    (hn.isClosedSubgroup_inclusionInRadical hj) (hn.isNormal_inclusionInRadical hj)
  exact ⟨Q, q, hsm, ha, hq.connectedSpace, hq⟩

end Inclusion

section LocalProduct

variable {k : Type u} [Field k]
    {G U V Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth U.X.hom] [Smooth V.X.hom]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]

/-- Two nested ambient normal closed subgroups give local parabolic-kernel
factorizations when their specified quotient has only constant affine-line maps.
This does not assert that any radical quotient has that rigidity property. -/
theorem fppfLocallyInProduct_parabolic_of_wound_quotient
    (j : U ⟶ G) (n : V ⟶ G) (m : V ⟶ U)
    (hj : IsClosedSubgroup j) (hjn : (SubgroupFunctor.range j).IsNormal)
    (hn : IsClosedSubgroup n) (hnn : (SubgroupFunctor.range n).IsNormal)
    (hm : m ≫ j = n) (q : U ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range m) q)
    (hQ : HasConstantAffineLineMaps Q)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (hx : x ∈ (SubgroupFunctor.range j).carrier T) :
    SubgroupFunctor.FppfLocallyInProduct (Dynamic.parabolic χ) (SubgroupFunctor.range n) x := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom U.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G U j hj
  have hmr : (SubgroupFunctor.range m).IsRepresentedBy m := by
    let : IsClosedImmersion m.hom.hom.left := IsClosedSubgroup.of_comp hj (by rw [hm]; exact hn)
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  have hcomap : (SubgroupFunctor.range n).comap j = SubgroupFunctor.range m := by
    rw [← hm]
    exact range_comp_comap_of_mono m j
  let aG := AutomorphicAction.conjugation χ
  have hJ : aG.IsStable (SubgroupFunctor.range j) := by
    intro W s g hg
    rw [AutomorphicAction.conjugation_act]
    exact hjn W _ g (Subgroup.mem_top _) hg
  have hjr : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  let a := aG.onRepresentedSubgroup j hjr hJ
  have heqj : a.IsEquivariant aG j := by
    intro W s g
    exact aG.onRepresentedSubgroup_act_comp j hjr hJ s g
  have hM : a.IsStable (SubgroupFunctor.range m) := by
    intro W s g hg
    rw [← hcomap, SubgroupFunctor.mem_comap, heqj]
    rw [AutomorphicAction.conjugation_act]
    apply hnn W _ _ (Subgroup.mem_top _)
    exact SubgroupFunctor.mem_comap.mp (hcomap.symm ▸ hg)
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  let c := hq.action a hM
  have heqq : a.IsEquivariant c q := hq.action_isEquivariant a hM
  have hc : c = AutomorphicAction.trivial _ Q :=
    hQ.splitTorus_action_eq_trivial c isSplitTorus_gm
  let ν : cocharacterLattice (Gm (Spec (CommRingCat.of k))) := 𝟙 _
  let A := RelativeRoot.nonnegativeSemigroup ν
  have hzero : 0 ∈ A := by simp [A, RelativeRoot.nonnegativeSemigroup]
  have hctop : RelativeRoot.semigroupSubgroup c A = ⊤ := by
    apply RelativeRoot.semigroupSubgroup_eq_top_of_act_eq c _ isSplitTorus_gm
      inferInstance inferInstance A hzero
    intro W s g
    rw [hc, AutomorphicAction.trivial_act]
  have hqs : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hmr inferInstance
  have hImage := RelativeRoot.isFppfImage_semigroupSubgroup a c q (fun _ s g => heqq s g)
    RelativeRoot.semigroupRealization RelativeRoot.semigroupSmoothQuotient
    isSplitTorus_gm hqs hq.2.1 A
  have hpar : Dynamic.parabolic χ = RelativeRoot.semigroupSubgroup aG A := by
    have hid : CommGroupScheme.groupHom ν ≫ χ = χ := by
      change (𝟙 _ ≫ χ) = χ
      exact Category.id_comp χ
    simpa only [hid] using
      (RelativeRoot.dynamicSemigroupComparison k G inferInstance inferInstance inferInstance
        (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm χ ν).1
  have hmap := RelativeRoot.semigroupFunctoriality k U G inferInstance inferInstance
    inferInstance inferInstance (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm
    a aG j (fun _ s g => heqj s g) A
  obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hu : u ≫ q.hom.hom ∈ (RelativeRoot.semigroupSubgroup c A).carrier T := by
    rw [hctop]
    exact Subgroup.mem_top _
  obtain ⟨W, w, hf, hs, hl, f, r, hF, hr, he⟩ :=
    (hImage.fppfLocallyInProduct_kernel_iff u).mpr hu
  refine ⟨W, w, hf, hs, hl, f ≫ j.hom.hom, r ≫ j.hom.hom, ?_, ?_, ?_⟩
  · rw [hpar]
    exact hmap W ⟨f, hF, rfl⟩
  · rw [hq.2.2.2] at hr
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hr
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨v, ?_⟩
    rw [← hm, Grp.comp_hom_hom, ← Category.assoc, hv]
  · rw [← Category.assoc, he, MonObj.mul_comp]

end LocalProduct

end Langlands.GroupScheme
