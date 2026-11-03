import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Cartan subgroups as closed representatives of maximal-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H H' : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed subgroup is a Cartan subgroup when its all-test subgroup functor is the
centralizer of some maximal torus. This predicate makes sense for any ambient group scheme;
the classical structural results impose further hypotheses on that ambient group. -/
def IsCartanSubgroup (i : H ⟶ G) : Prop :=
  IsClosedSubgroup i ∧
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j ∧ SubgroupFunctor.range i = torusCentralizer j

theorem IsCartanSubgroup.isClosedSubgroup {i : H ⟶ G} (hi : IsCartanSubgroup i) :
    IsClosedSubgroup i :=
  hi.1

/-- A closed representative of a maximal-torus centralizer is a Cartan subgroup. -/
theorem isCartanSubgroup_of_representsCentralizer
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    (hj : IsMaximalTorus j) {i : H ⟶ G} (hi : IsClosedSubgroup i)
    (hrep : (torusCentralizer j).IsRepresentedBy i) : IsCartanSubgroup i :=
  ⟨hi, T, j, hj, hrep.2⟩

/-- A Cartan embedding represents the centralizer of one of its witnessing maximal tori. -/
theorem IsCartanSubgroup.exists_centralizer_representation {i : H ⟶ G}
    (hi : IsCartanSubgroup i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j ∧ (torusCentralizer j).IsRepresentedBy i := by
  obtain ⟨hclosed, T, j, hj, heq⟩ := hi
  let : IsClosedImmersion i.hom.hom.left := hclosed
  exact ⟨T, j, hj, Over.mono_of_mono_left _, heq⟩

/-- For an affine group over a field, every maximal torus has an actual closed Cartan
representative of its all-test centralizer. This does not assert existence of a maximal torus. -/
theorem exists_isCartanSubgroup_of_isMaximalTorus [IsAffine G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    (hj : IsMaximalTorus j) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsCartanSubgroup i ∧ (torusCentralizer j).IsRepresentedBy i := by
  have hrep := (hasClosedRepresentative_normalizer_centralizer_range j hj.2.1).2
  rw [← torusCentralizer_eq_centralizer_range] at hrep
  obtain ⟨H, i, hi, hrep⟩ := hrep
  exact ⟨H, i, isCartanSubgroup_of_representsCentralizer hj hi hrep, hrep⟩

/-- Cartan embeddings with the same all-test image have a unique isomorphism over the ambient
group. Cartan subgroups with different images are not compared by this result. -/
theorem IsCartanSubgroup.existsUnique_iso_of_range_eq {i : H ⟶ G} {i' : H' ⟶ G}
    (hi : IsCartanSubgroup i) (hi' : IsCartanSubgroup i')
    (heq : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    ∃! e : H ≅ H', e.hom ≫ i' = i := by
  let : IsClosedImmersion i.hom.hom.left := hi.1
  let : IsClosedImmersion i'.hom.hom.left := hi'.1
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hrep' : (SubgroupFunctor.range i).IsRepresentedBy i' :=
    ⟨Over.mono_of_mono_left _, heq.symm⟩
  refine ⟨hrep.isoOfIsRepresentedBy hrep', hrep.isoOfIsRepresentedBy_hom_comp hrep', ?_⟩
  intro e he
  apply Iso.ext
  exact hrep'.hom_ext (he.trans (hrep.isoOfIsRepresentedBy_hom_comp hrep').symm)

/-- Conditional on the published maximal-torus centralizer statement, a maximal torus of a
connected reductive group is itself a Cartan subgroup. -/
theorem IsMaximalTorus.isCartanSubgroup_of_centralizerStatement
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    (hj : IsMaximalTorus j) (hcentralizer : MaximalTorusCentralizerStatement.{u})
    (hG : IsConnectedReductive G) : IsCartanSubgroup j :=
  ⟨hj.2.1, T, j, hj, (hcentralizer k G hG T j hj).symm⟩

/-- Conditional on the maximal-torus centralizer statement, a Cartan subgroup of a connected
reductive group is isomorphic over the group to its witnessing maximal torus. -/
theorem IsCartanSubgroup.exists_iso_maximalTorus_of_centralizerStatement
    {i : H ⟶ G} (hi : IsCartanSubgroup i)
    (hcentralizer : MaximalTorusCentralizerStatement.{u}) (hG : IsConnectedReductive G) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j ∧ ∃ e : H ≅ T.toGrp, e.hom ≫ j = i := by
  obtain ⟨T, j, hj, hrep⟩ := hi.exists_centralizer_representation
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  have hrepj : (torusCentralizer j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, (hcentralizer k G hG T j hj).symm⟩
  exact ⟨T, j, hj, hrep.isoOfIsRepresentedBy hrepj,
    hrep.isoOfIsRepresentedBy_hom_comp hrepj⟩

/-- Conditional on the maximal-torus centralizer statement, Cartan subgroups of connected
reductive groups are tori. -/
theorem IsCartanSubgroup.isTorus_of_centralizerStatement {i : H ⟶ G}
    (hi : IsCartanSubgroup i) (hcentralizer : MaximalTorusCentralizerStatement.{u})
    (hG : IsConnectedReductive G) : IsTorus H := by
  obtain ⟨T, j, hj, e, _⟩ :=
    hi.exists_iso_maximalTorus_of_centralizerStatement hcentralizer hG
  exact IsTorus.of_iso e hj.1

end Langlands.GroupScheme
