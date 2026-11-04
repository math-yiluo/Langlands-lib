import Langlands.GroupScheme.Rational.SemigroupNormalRadicalReduction
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Reductive.UnipotentRadicalAction
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.IdentityComponentAction
import Langlands.GroupScheme.Rational.SemigroupBaseChange
import Langlands.GroupScheme.Rational.SemigroupZeroExcludedIntersection
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Structural reduction of all semigroup comparison properties -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section IdentityComponent

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S))

include hS

/-- Every generated semigroup subgroup lies in the ambient identity component. -/
theorem semigroupSubgroup_le_range_identityComponent :
    semigroupSubgroup b A ≤ SubgroupFunctor.range (identityComponentι G) := by
  obtain ⟨L, l, hl, _, _, hconn⟩ := isSmoothConnectedClosed_semigroupSubgroup b hS A
  let : ConnectedSpace L.X.left := hconn
  rw [← hl.2]
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2
    ⟨y ≫ (IdentityComponent.factor G l).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IdentityComponent.factor_identityComponentι]

/-- The actual generated subgroup agrees with the one inside the identity
component, after taking its inverse image. -/
theorem semigroupSubgroup_comap_identityComponent :
    (semigroupSubgroup b A).comap (identityComponentι G) =
      semigroupSubgroup b.onIdentityComponent A := by
  have heq := semigroupSubgroup_map_eq (identityComponentι G)
    (show IsClosedImmersion (identityComponentι G).hom.hom.left from inferInstance)
    b.onIdentityComponent b (fun _ s x => b.onIdentityComponent_act_comp s x) A
    (semigroupSubgroup_le_range_identityComponent b hS A)
  rw [← heq, SubgroupFunctor.comap_map_of_mono]

end IdentityComponent

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual radical representatives and their action stability discharge all
radical data in the conditional connected normal reduction. -/
theorem semigroup_comap_eq_of_normal_connected
    [ConnectedSpace G.X.left]
    (hPrerequisites : NormalSemigroupRadicalPrerequisites.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  let : Smooth S.toGrp.X.hom := hS.smooth
  obtain ⟨U, r, hr⟩ := unipotentRadicalExistence k G
  obtain ⟨V, s, hs⟩ := unipotentRadicalExistence k H
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U r hr
  obtain ⟨R, p, hp, hR⟩ := unipotentRadicalQuotient k H V s hs
  exact semigroup_comap_eq_of_normal_radical_quotients hPrerequisites
    hS b c i hi hn heq r s hr hs (hr.isStable b) (hs.isStable c) q p hq hp
    hQ.isConnectedReductive_of_isAlgClosed hR.isConnectedReductive_of_isAlgClosed A hzero

/-- Factoring through the actual identity component removes ambient
connectedness from the conditional normal comparison over an algebraically
closed field. -/
theorem semigroup_comap_eq_of_normal_algebraicallyClosed
    (hPrerequisites : NormalSemigroupRadicalPrerequisites.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  let j := identityComponentι G
  let f := IdentityComponent.factor G i
  have hcomp : f ≫ j = i := IdentityComponent.factor_identityComponentι G i
  have hj : IsClosedSubgroup j :=
    (show IsClosedImmersion j.hom.hom.left from inferInstance)
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hf : IsClosedSubgroup f := IsClosedSubgroup.of_comp hj (by rw [hcomp]; exact hi)
  have hcomp' : f.hom.hom ≫ j.hom.hom = i.hom.hom :=
    congrArg (fun v => v.hom.hom) hcomp
  have hrange : (SubgroupFunctor.range i).comap j = SubgroupFunctor.range f := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (cancel_mono j.hom.hom).mp ?_⟩
      rw [Category.assoc, hcomp']
      exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Category.assoc, hcomp']⟩
  have hnf : (SubgroupFunctor.range f).IsNormal := by
    rw [← hrange]
    exact hn.comap j
  have hef : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ f.hom.hom = b.onIdentityComponent.act s (h ≫ f.hom.hom) := by
    intro T s h
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hcomp', b.onIdentityComponent_act_comp,
      Category.assoc, hcomp', heq]
  rw [← hcomp, SubgroupFunctor.comap_comp,
    semigroupSubgroup_comap_identityComponent b hS A]
  exact semigroup_comap_eq_of_normal_connected hPrerequisites hS
    b.onIdentityComponent c f hf hnf hef A hzero

end AlgebraicallyClosed

section Field

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The conditional normal comparison descends from an algebraic closure by
fpqc reflection in the represented subgroup on H. -/
theorem semigroup_comap_eq_of_normal
    (hPrerequisites : NormalSemigroupRadicalPrerequisites.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  apply le_antisymm
  · obtain ⟨L, l, hl, _, _, _⟩ := isSmoothConnectedClosed_semigroupSubgroup c hS A
    let : Mono l.hom.hom := hl.1
    rw [← hl.2]
    let v := algebraBaseMap k (AlgebraicClosure k)
    let G' := (GroupScheme.baseChange v).obj G
    let H' := (GroupScheme.baseChange v).obj H
    let S' := (CommGroupScheme.baseChange v).obj S
    let i' := (GroupScheme.baseChange v).map i
    let : Flat v := TorusExistence.flat_algebraBaseMap (AlgebraicClosure k)
    let : Surjective v := TorusExistence.surjective_algebraBaseMap (AlgebraicClosure k)
    let : Smooth G'.X.hom := by
      change Smooth (pullback.snd G.X.hom v)
      infer_instance
    let : Smooth H'.X.hom := by
      change Smooth (pullback.snd H.X.hom v)
      infer_instance
    let : IsAffineHom G'.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom v)
      infer_instance
    let : IsAffineHom H'.X.hom := by
      change IsAffineHom (pullback.snd H.X.hom v)
      infer_instance
    let : ConnectedSpace H'.X.left := H.connectedSpace_baseChange_of_smooth_affine v
    have hn' : (SubgroupFunctor.range i').IsNormal := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange v
    have heq' : ∀ (T : Over (Spec (CommRingCat.of (AlgebraicClosure k))))
        (s : T ⟶ S'.X) (h : T ⟶ H'.X),
        (c.baseChange v).act s h ≫ i'.hom.hom =
          (b.baseChange v).act s (h ≫ i'.hom.hom) := by
      intro T s h
      apply (baseChangePointsEquiv v G T).injective
      rw [baseChangePointsEquiv_comp, AutomorphicAction.baseChangePointsEquiv_act,
        AutomorphicAction.baseChangePointsEquiv_act, baseChangePointsEquiv_comp]
      exact heq _ _ _
    have hzero' : 0 ∈ characterSemigroupBaseChange v S A :=
      ⟨0, hzero, map_zero _⟩
    have he := semigroup_comap_eq_of_normal_algebraicallyClosed
      (k := AlgebraicClosure k) (G := G') (H := H') (S := S')
      hPrerequisites (hS.baseChange v) (b.baseChange v) (c.baseChange v) i'
      (hi.baseChange v) hn' heq' (characterSemigroupBaseChange v S A) hzero'
    apply SubgroupFunctor.le_range_of_baseChange_le v l
    rw [hl.2, SubgroupFunctor.comap_baseChange,
      semigroupSubgroup_baseChange (K := AlgebraicClosure k) b hS A,
      semigroupSubgroup_baseChange (K := AlgebraicClosure k) c hS A]
    exact he.le
  · exact SubgroupFunctor.map_le_iff_le_comap.mp
      (semigroupSubgroup_map_le i hi c b heq A)

end Field

/-- The displayed independent structural propositions imply the exact existing
comparison proposition, including all three intersection alternatives. -/
theorem semigroupComparison_of_structuralPrerequisites
    (hPrerequisites : NormalSemigroupRadicalPrerequisites.{u}) :
    SemigroupComparisonStatement.{u} := by
  refine ⟨semigroupFunctoriality, semigroupSmoothQuotient, ?_⟩
  intro k _ G H hG hH hAffG hAffH hConnH S hS b c i hi heq A hcase
  let := hG
  let := hH
  let := hAffG
  let := hAffH
  let := hConnH
  rcases hcase with hzero | hsolv | hnormal
  · exact semigroup_comap_eq_of_zero_not_mem b c i heq semigroupRealization
      CoordinateWeights.coordinateSemigroupComparison.2 hS hi A hzero
  · by_cases hzero : 0 ∈ A
    · exact semigroup_comap_eq_of_solvable_of_zero_mem c hS hPrerequisites.2.2
        hsolv b i heq semigroupRealization hi A hzero
    · exact semigroup_comap_eq_of_zero_not_mem b c i heq semigroupRealization
        CoordinateWeights.coordinateSemigroupComparison.2 hS hi A hzero
  · by_cases hzero : 0 ∈ A
    · exact semigroup_comap_eq_of_normal hPrerequisites hS b c i hi hnormal heq A hzero
    · exact semigroup_comap_eq_of_zero_not_mem b c i heq semigroupRealization
        CoordinateWeights.coordinateSemigroupComparison.2 hS hi A hzero

end Langlands.GroupScheme.RelativeRoot
