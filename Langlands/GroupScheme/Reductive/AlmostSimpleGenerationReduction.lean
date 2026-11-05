import Langlands.GroupScheme.Reductive.MinimalNormalFactor
import Langlands.GroupScheme.Reductive.AlmostSimpleGenerationStatement
import Langlands.GroupScheme.ReducedSubgroupAction
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Almost-simple generation from actual-root and centre premises -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The local closed-subgroup generation property, with full all-test ranges. -/
def IsGeneratedByNormalAlmostSimpleSubgroups
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsClosedSubgroup d →
    (∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
      IsAlmostSimple A → IsClosedSubgroup a →
      (SubgroupFunctor.range a).IsNormal →
      SubgroupFunctor.range a ≤ SubgroupFunctor.range d) →
    SubgroupFunctor.range d = ⊤

/-- Every homomorphism from a smooth connected group factors through the
reduced identity component of its target. -/
theorem range_le_identityCore_of_smooth_connected
    {C K : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType C.X.hom] [IsAffineHom C.X.hom]
    [Smooth K.X.hom] [ConnectedSpace K.X.left] (f : K ⟶ C) :
    SubgroupFunctor.range f ≤ SubgroupFunctor.range (ReducedSubgroup.identityCoreι C) := by
  let : IsReduced K.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k K.X.left K.X.hom
  apply SubgroupFunctor.range_le_of_factor
    (IdentityComponent.factor (reducedSubgroup C) (ReducedSubgroup.liftHom f))
  simp only [ReducedSubgroup.identityCoreι, ← Category.assoc,
    IdentityComponent.factor_identityComponentι, ReducedSubgroup.liftHom_fac]

/-- Internal almost-simple generation in a smooth connected normal subgroup
gives containment in any ambient closed competitor containing all ambient
normal almost-simple subgroups. -/
theorem IsGeneratedByNormalAlmostSimpleSubgroups.range_le_of_normal
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G H D : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple G)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hgen : IsGeneratedByNormalAlmostSimpleSubgroups H)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcontains : ∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
      IsAlmostSimple A → IsClosedSubgroup a →
      (SubgroupFunctor.range a).IsNormal →
      SubgroupFunctor.range a ≤ SubgroupFunctor.range d) :
    SubgroupFunctor.range h ≤ SubgroupFunctor.range d := by
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  have hfull := hgen (subgroupIntersection h d) (subgroupIntersectionFst h d)
    (isClosedSubgroup_subgroupIntersectionFst h hd) (by
      intro A a hA ha han
      have hn' := isNormal_range_comp_of_actual_roots hRoots hDichotomy hG
        T t hSplit hMax h hh hn a ha han
      have hrange := hcontains A (a ≫ h) hA (ha.comp hh) hn'
      let : IsClosedImmersion (a ≫ h).hom.hom.left := ha.comp hh
      let : Mono (a ≫ h).hom.hom := Over.mono_of_mono_left _
      obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hrange
      exact SubgroupFunctor.range_le_of_factor (pullback.lift a f hf.symm)
        (pullback.lift_fst a f hf.symm))
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ∈ (SubgroupFunctor.range (subgroupIntersectionFst h d)).carrier U := by
    rw [hfull]
    trivial
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨z ≫ (subgroupIntersectionSnd h d).hom.hom, ?_⟩
  have hw := congrArg (fun a => a.hom.hom) (subgroupIntersection_condition h d)
  simp only [Grp.comp_hom_hom] at hw
  rw [Category.assoc, ← hw, ← Category.assoc, hz]

/-- Root dichotomy and closed generation may use the smooth connected reduced
identity component of the full centralizer. Smooth connected root
representatives factor through that component. -/
theorem range_eq_top_of_normal_and_centralizerCore
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G H D C : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple G)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType C.X.hom] [IsAffineHom C.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (c : C ⟶ G) (hc : IsClosedSubgroup c)
    (hcRange : SubgroupFunctor.range c =
      (AutomorphicAction.conjugation h).fixedSubgroup)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hH : SubgroupFunctor.range h ≤ SubgroupFunctor.range d)
    (hC : SubgroupFunctor.range (ReducedSubgroup.identityCoreι C ≫ c) ≤
      SubgroupFunctor.range d) : SubgroupFunctor.range d = ⊤ := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsClosedImmersion c.hom.hom.left := hc
  let : Mono c.hom.hom := Over.mono_of_mono_left _
  apply hRoots k G hG T t hSplit hMax D d hd
  intro α hα
  rcases hDichotomy k G hG T t hSplit hMax H h hh hn α hα with hαH | hαC
  · exact le_trans hαH hH
  obtain ⟨U, j, hj, hjc, hUs, hUc⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hSplit.1 t α
      (mem_relativeRoots.mp hα).1
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hle : SubgroupFunctor.range j ≤ SubgroupFunctor.range c := by
    rw [hj.2, hcRange]
    exact hαC
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  have hfcore := range_le_identityCore_of_smooth_connected f
  rw [← hj.2]
  intro V x hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  have hfy : y ≫ f.hom.hom ∈
      (SubgroupFunctor.range (ReducedSubgroup.identityCoreι C)).carrier V :=
    hfcore V (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hfy
  apply hC V
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨z, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc, ← Grp.comp_hom_hom,
    hf, hy]

/-- Under the three structural premises, dimension induction gives the local
normal almost-simple generation property. -/
theorem isGeneratedByNormalAlmostSimpleSubgroups_of_actual_roots
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsSemisimple G) :
    IsGeneratedByNormalAlmostSimpleSubgroups G := by
  classical
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  apply smoothConnectedAffineGroup_lieDimension_induction
    (fun K => IsSemisimple K → IsGeneratedByNormalAlmostSimpleSubgroups K) ?_ G hG
  intro G _ _ _ ih hG D d hd hcontains
  by_cases hzero : SubgroupFunctor.range (𝟙 G) = ⊥
  · apply SubgroupFunctor.ext
    intro U
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      have hx : x ∈ (SubgroupFunctor.range (𝟙 G)).carrier U :=
        SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id x⟩
      rw [hzero] at hx
      change x = 1 at hx
      rw [hx]
      exact (SubgroupFunctor.range d).carrier U |>.one_mem
  let A := normalAlmostSimpleFactorOfActualRoots hCenter hRoots hDichotomy hG hzero
  let : Smooth A.group.X.hom := A.isAlmostSimple.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom A.group.X.hom :=
    A.isAlmostSimple.isSemisimple.isConnectedReductive.isAffineHom
  let : ConnectedSpace A.group.X.left :=
    A.isAlmostSimple.isSemisimple.isConnectedReductive.connectedSpace
  have hA : SubgroupFunctor.range A.inclusion ≤ SubgroupFunctor.range d :=
    hcontains A.group A.inclusion A.isAlmostSimple A.isClosedSubgroup A.isNormal
  let C := closedNormalCentralizer A.inclusion A.isNormal
  let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedSubgroup
  let : IsAffineHom C.group.X.hom := C.isClosedSubgroup.isAffineHom
  let : LocallyOfFiniteType C.group.X.hom := by
    rw [← C.inclusion.hom.hom.w]
    infer_instance
  let N := ReducedSubgroup.identityCore C.group
  let n : N ⟶ G := ReducedSubgroup.identityCoreι C.group ≫ C.inclusion
  have hnc : IsClosedSubgroup n := by
    change IsClosedImmersion
      ((ReducedSubgroup.identityCoreι C.group).hom.hom.left ≫
        C.inclusion.hom.hom.left)
    infer_instance
  have hnn : (SubgroupFunctor.range n).IsNormal :=
    ReducedSubgroup.isNormal_range_identityCoreι_comp
      C.inclusion C.isClosedSubgroup C.isNormal
  have hN : IsSemisimple N :=
    hG.of_normalSubgroup_of_normalReductiveCenterStatement hCenter n hnc hnn
  have hnproper : ¬ IsIso n := by
    intro hniso
    let : IsIso n := hniso
    let : IsClosedImmersion A.inclusion.hom.hom.left := A.isClosedSubgroup
    let : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
    apply A.isAlmostSimple.noncommutative
    intro U x y
    change x * y = y * x
    apply (cancel_mono A.inclusion.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have hc := C.commute U x
      (y ≫ (A.inclusion ≫ inv n).hom.hom ≫
        (ReducedSubgroup.identityCoreι C.group).hom.hom)
    have he : (A.inclusion ≫ inv n) ≫ n = A.inclusion := by
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hy :
        (y ≫ (A.inclusion ≫ inv n).hom.hom ≫
          (ReducedSubgroup.identityCoreι C.group).hom.hom) ≫
          C.inclusion.hom.hom = y ≫ A.inclusion.hom.hom := by
      rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
        ← Grp.comp_hom_hom, he]
    rw [hy] at hc
    exact hc.eq
  have hdim : Lie.dimension N < Lie.dimension G :=
    Lie.dimension_lt_of_proper_closedSubgroup n hnc hnproper
  have hgenN : IsGeneratedByNormalAlmostSimpleSubgroups N := ih N hdim hN
  obtain ⟨T, t, hMax⟩ := TorusExistence.exists_isMaximalTorus G
  have hSplit : IsSplitSubtorus t :=
    ⟨hMax.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting, hMax.2.1⟩
  have hNle : SubgroupFunctor.range n ≤ SubgroupFunctor.range d :=
    hgenN.range_le_of_normal hRoots hDichotomy hG T t hSplit hMax
      n hnc hnn d hd hcontains
  exact range_eq_top_of_normal_and_centralizerCore hRoots hDichotomy hG
    T t hSplit hMax A.inclusion A.isClosedSubgroup A.isNormal
    C.inclusion C.isClosedSubgroup C.range_eq d hd hA hNle

/-- The exact generation proposition follows from the three explicit
structural premises, at every universe. -/
theorem semisimpleAlmostSimpleGeneration_of_actualRoots
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u}) :
    SemisimpleAlmostSimpleGenerationStatement.{u} := by
  intro k _ _ G hG
  exact isGeneratedByNormalAlmostSimpleSubgroups_of_actual_roots hCenter hRoots hDichotomy G hG

/-- Construct the actual isomorphism from a closed competitor to the ambient
semisimple group, under the explicit structural premises. -/
def almostSimpleGenerationIsoOfActualRoots
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G D : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcontains : ∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
      IsAlmostSimple A → IsClosedSubgroup a →
      (SubgroupFunctor.range a).IsNormal →
      SubgroupFunctor.range a ≤ SubgroupFunctor.range d) : D ≅ G := by
  let : IsClosedImmersion d.hom.hom.left := hd
  exact (show (⊤ : SubgroupFunctor G).IsRepresentedBy d from
    ⟨Over.mono_of_mono_left _,
      isGeneratedByNormalAlmostSimpleSubgroups_of_actual_roots
        hCenter hRoots hDichotomy G hG D d hd hcontains⟩).topIso

/-- The generation isomorphism has the original closed inclusion as its
forward map. -/
theorem almostSimpleGenerationIsoOfActualRoots_hom
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G D : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcontains : ∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
      IsAlmostSimple A → IsClosedSubgroup a →
      (SubgroupFunctor.range a).IsNormal →
      SubgroupFunctor.range a ≤ SubgroupFunctor.range d) :
    (almostSimpleGenerationIsoOfActualRoots
      hCenter hRoots hDichotomy hG d hd hcontains).hom = d := by
  apply SubgroupFunctor.IsRepresentedBy.topIso_hom

end Langlands.GroupScheme
