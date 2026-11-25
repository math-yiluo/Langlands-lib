import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.IdentityJetParameterOfSubgroup
import Langlands.GroupScheme.Lie.SmoothOpenSubgroup
import Langlands.GroupScheme.OpenImmersionBaseLocus
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.RelativeIdentityComponent.OpenSubgroup

/-! # The base open where a subgroup is open in its jet stabilizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IdentityJet

open SubgroupFunctor Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter TorusSubgroupModuli

variable {S T : Scheme.{u}} {G H N : GroupScheme S}

/-- The closed stabilizer of the given jet admits the subgroup as an open subgroup. -/
def OpenInStabilizer (i : H ⟶ G) (n : ℕ) : Prop :=
  ∃ (N : GroupScheme S) (j : N ⟶ G), IsClosedSubgroup j ∧ (stabilizer i n).IsRepresentedBy j ∧
    ∃ a : H ⟶ N, a ≫ j = i ∧ IsOpenImmersion a.hom.hom.left

/-- The canonical factorization into a represented jet stabilizer. -/
def stabilizerFactor [IsSeparated G.X.hom] {i : H ⟶ G} (hi : IsClosedSubgroup i)
    {n : ℕ} {j : N ⟶ G} (hj : (stabilizer i n).IsRepresentedBy j) : H ⟶ N :=
  hj.liftOfLE i ((range i).le_normalizer.trans (normalizer_le_stabilizer i hi n))

@[reassoc (attr := simp)]
theorem stabilizerFactor_comp [IsSeparated G.X.hom] {i : H ⟶ G} (hi : IsClosedSubgroup i)
    {n : ℕ} {j : N ⟶ G} (hj : (stabilizer i n).IsRepresentedBy j) :
    stabilizerFactor hi hj ≫ j = i :=
  hj.liftOfLE_comp i _

/-- The open-subgroup condition is independent of the chosen closed stabilizer. -/
theorem openInStabilizer_iff {i : H ⟶ G} {n : ℕ} {j : N ⟶ G} (hj : IsClosedSubgroup j)
    (hrep : (stabilizer i n).IsRepresentedBy j) (a : H ⟶ N) (ha : a ≫ j = i) :
    OpenInStabilizer i n ↔ IsOpenImmersion a.hom.hom.left := by
  refine ⟨?_, fun h => ⟨N, j, hj, hrep, a, ha, h⟩⟩
  rintro ⟨K, k, _, hk, b, hb, hbopen⟩
  let e := hk.isoOfIsRepresentedBy hrep
  have he : b ≫ e.hom = a := hrep.hom_ext (by
    rw [Category.assoc, hk.isoOfIsRepresentedBy_hom_comp hrep, hb, ha])
  have : IsOpenImmersion b.hom.hom.left := hbopen
  rw [← he]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  exact inferInstanceAs (IsOpenImmersion (b.hom.hom.left ≫ e.hom.hom.hom.left))

/-- Every test of a finite-flat jet parameter with closed universal stabilizer
has an actual closed stabilizer for the jet of a smooth closed subgroup. -/
theorem stabilizer_isClosedRepresentable_of_parameter {G : GroupScheme S} [IsSeparated G.X.hom]
    (n : ℕ) (D : Parameter (overScheme G n))
    (hD : (conjugationStabilizer (subschemeToGroup G n D.base D.ideal)).IsClosedRepresentable)
    {U : Over S} {H : GroupScheme U.left} [Smooth H.X.hom]
    (i : H ⟶ (baseChange U.hom).obj G) (hi : IsClosedSubgroup i) : (stabilizer i n).IsClosedRepresentable := by
  obtain ⟨g, hg, _⟩ := existsUnique_subgroupJetPoint G n D i hi
  obtain ⟨N, j, hrep, hj⟩ := hD
  exact ⟨_, familyHom j g, isRepresentedBy_subgroupJetStabilizer G n D j hj hrep g i hi hg,
    isClosedSubgroup_familyHom j hj g⟩

/-- The condition of being open in a represented jet stabilizer has an
actual open locus, with the asserted factorization test after every base change. -/
theorem exists_open_of_openInStabilizer [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth H.X.hom] {i : H ⟶ G} (hi : IsClosedSubgroup i) {n : ℕ}
    (hN : (stabilizer i n).IsClosedRepresentable) :
    ∃ W : S.Opens, ∀ (T : Scheme.{u}) (b : T ⟶ S),
      Set.range b ⊆ W ↔ OpenInStabilizer ((baseChange b).map i) n := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated H.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  obtain ⟨N, j, hrep, hj⟩ := hN
  have : IsClosedImmersion j.hom.hom.left := hj
  have : LocallyOfFiniteType N.X.hom := by rw [← Over.w j.hom.hom]; infer_instance
  let a := stabilizerFactor hi hrep
  have ha : a ≫ j = i := stabilizerFactor_comp hi hrep
  have : Mono a.hom.hom.left := by
    have h : Mono (a.hom.hom.left ≫ j.hom.hom.left) := by
      change Mono (a ≫ j).hom.hom.left
      rw [ha]
      infer_instance
    exact mono_of_mono _ j.hom.hom.left
  refine ⟨SmoothMonoLocalIso.unitEtaleOpen a,
    fun T b => (range_subset_unitEtaleOpen_iff a b).trans ?_⟩
  have hrep' := hrep.baseChange b
  rw [stabilizer_baseChange b] at hrep'
  exact (openInStabilizer_iff (hj.baseChange b) hrep' ((baseChange b).map a)
    (by rw [← Functor.map_comp, ha])).symm

/-- The same open condition for direct evaluation of an actual subgroup family. -/
theorem exists_open_of_openInStabilizer_familyHom {G : GroupScheme S} [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] (n : ℕ) (D : Parameter (overScheme G n))
    (hD : (conjugationStabilizer (subschemeToGroup G n D.base D.ideal)).IsClosedRepresentable)
    {U : Over S} {K : GroupScheme U.left} [Smooth K.X.hom]
    (i : K ⟶ (baseChange U.hom).obj G) (hi : IsClosedSubgroup i) :
    ∃ W : U.left.Opens, ∀ (V : Over S) (b : V ⟶ U),
      (Set.range b.left ⊆ W ↔ OpenInStabilizer ((baseChange b.left).map i) n) ∧
        (Set.range b.left ⊆ W ↔ OpenInStabilizer (familyHom i b) n) := by
  obtain ⟨g, hg, _⟩ := existsUnique_subgroupJetPoint G n D i hi
  obtain ⟨N, j, hrep, hj⟩ := hD
  let j' := familyHom j g
  have hj' : IsClosedSubgroup j' := isClosedSubgroup_familyHom j hj g
  have : IsClosedImmersion j'.hom.hom.left := hj'
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated ((baseChange U.hom).obj G).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom U.hom))
  have : IsSeparated K.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  have : LocallyOfFiniteType ((baseChange U.hom).obj G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom U.hom))
  have : LocallyOfFiniteType ((baseChange g.left).obj N).X.hom := by
    rw [← Over.w j'.hom.hom]
    infer_instance
  let hrep' := isRepresentedBy_subgroupJetStabilizer G n D j hj hrep g i hi hg
  let a := stabilizerFactor hi hrep'
  have ha : a ≫ j' = i := stabilizerFactor_comp hi hrep'
  have : Mono a.hom.hom.left := by
    have hm : Mono (a.hom.hom.left ≫ j'.hom.hom.left) := by
      change Mono (a ≫ j').hom.hom.left
      rw [ha]
      infer_instance
    exact mono_of_mono _ j'.hom.hom.left
  refine ⟨SmoothMonoLocalIso.unitEtaleOpen a, fun V b => ?_⟩
  have hopen' := range_subset_unitEtaleOpen_iff a b.left
  refine ⟨hopen'.trans ?_, hopen'.trans ?_⟩
  · have hr := hrep'.baseChange b.left
    rw [stabilizer_baseChange b.left] at hr
    exact (openInStabilizer_iff (hj'.baseChange b.left) hr ((baseChange b.left).map a)
      (by rw [← Functor.map_comp, ha])).symm
  · let f := (baseChange b.left).map a ≫ (familySourceComparison N g b).hom
    have hf : f ≫ familyHom j (b ≫ g) = familyHom i b := by
      rw [show f ≫ familyHom j (b ≫ g) = (baseChange b.left).map a ≫ familyHom j' b by
        rw [Category.assoc, familyHom_evaluate_comp]]
      dsimp only [familyHom]
      rw [← Category.assoc, ← Functor.map_comp, ha]
    have hjet : D.eval (overScheme G n) (b ≫ g) = subgroupJetIdeal G n (familyHom i b) := by
      rw [Parameter.eval_comp, hg, subgroupJetIdeal_testMap G n i hi b]
    have hrep'' := isRepresentedBy_subgroupJetStabilizer G n D j hj hrep (b ≫ g)
      (familyHom i b) (isClosedSubgroup_familyHom i hi b) hjet
    have hopen : IsOpenImmersion ((baseChange b.left).map a).hom.hom.left ↔
        IsOpenImmersion f.hom.hom.left := by
      change IsOpenImmersion ((baseChange b.left).map a).hom.hom.left ↔
        IsOpenImmersion (((baseChange b.left).map a).hom.hom.left ≫
          (familySourceComparison N g b).hom.hom.hom.left)
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      exact (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ _).symm
    exact hopen.trans (openInStabilizer_iff (isClosedSubgroup_familyHom j hj (b ≫ g))
      hrep'' f hf).symm

/-- A smooth geometrically connected open subgroup is the actual relative
identity component, including for a locally finite-type group with nonflat total space. -/
theorem isRelativeIdentityComponent_of_open [LocallyOfFiniteType N.X.hom]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom] (j : H ⟶ N)
    [IsOpenImmersion j.hom.hom.left] : IsRelativeIdentityComponent N j := by
  apply IsRelativeIdentityComponent.of_range_residueFiber
  intro s
  let b := S.fromSpecResidueField s
  let Hs := (baseChange b).obj H
  let Ns := (baseChange b).obj N
  let js : Hs ⟶ Ns := (baseChange b).map j
  have : IsOpenImmersion js.hom.hom.left := MorphismProperty.overPullbackMap
    (P := @IsOpenImmersion) b j.hom.hom inferInstance
  have : LocallyOfFiniteType Ns.X.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom b))
  have : Smooth Hs.X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : ConnectedSpace Hs.X.left := inferInstanceAs (ConnectedSpace (H.X.hom.fiber s))
  have : Smooth Ns.X.hom := smooth_of_smooth_open_subgroup Ns Hs js
  simpa only [IdentityComponent.identitySet, PreconnectedSpace.connectedComponent_eq_univ, Set.image_univ]
    using RelativeIdentityComponent.image_identitySet_of_open js

/-- Two actual relative identity components have the same subgroup of all points. -/
theorem relativeIdentityComponent_range_eq {K : GroupScheme S} {i : H ⟶ N} {j : K ⟶ N}
    (hi : IsRelativeIdentityComponent N i) (hj : IsRelativeIdentityComponent N j) : range i = range j := by
  apply SubgroupFunctor.ext
  intro U
  apply SetLike.ext
  intro x
  rw [mem_range, mem_range, hi.factors_iff U x, hj.factors_iff U x]

end Langlands.GroupScheme.IdentityJet
