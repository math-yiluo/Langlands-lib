import Langlands.GroupScheme.Cartan.Induction
import Langlands.GroupScheme.GeneratedFamily
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.DynamicSemigroupProof
import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.CentralizerSmooth
import Langlands.GroupScheme.Lie.TorusCentralizer

/-! # Closed generation of a dynamic parabolic by its nonnegative roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (hi : IsSplitSubtorus i) (nu : cocharacterLattice S)

include hi

/-- A nonnegative root functor lies in the dynamic parabolic, including
roots with zero pairing. -/
theorem subgroup_le_dynamicParabolic_of_nonneg (a : characterLattice S)
    (ha : a ≠ 0) (hpair : 0 ≤ latticePairing S a nu) :
    subgroup i a ≤ Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ i) := by
  rw [← weightFiltration_one_eq_subgroup hi.1 i a ha,
    (dynamicSemigroupComparison k G inferInstance inferInstance inferInstance S hi.1 i nu).1]
  apply semigroupSubgroup_mono
  rintro chi ⟨n, _, _, rfl⟩
  change 0 ≤ latticePairing S (n • a) nu
  rw [map_nsmul]
  exact nsmul_nonneg hpair _

/-- Every closed subgroup containing the whole-torus centralizer and all
nonnegative root functors contains the dynamic parabolic on every test scheme.
The closed competitor need not be smooth or connected. -/
theorem dynamicParabolic_le_of_nonnegative_rootSubgroups_le
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcent : torusCentralizer i ≤ SubgroupFunctor.range d)
    (hroot : ∀ a ∈ relativeRoots i, 0 ≤ latticePairing S a nu →
      subgroup i a ≤ SubgroupFunctor.range d) :
    Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ i) ≤
      SubgroupFunctor.range d := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom S.X.hom := hi.1.isAffineHom
  obtain ⟨Z, z, hzc, hzs, hz⟩ :=
    torusCentralizer_hasSmoothClosedRepresentative i hi inferInstance
  let : Smooth Z.X.hom := hzs
  let : IsAffineHom Z.X.hom := hzc.isAffineHom
  let : ConnectedSpace Z.X.left := hi.1.connectedSpace_centralizer i hz
  let Rpos := {a : relativeRoots i // 0 ≤ latticePairing S a.val nu}
  have hrep (a : Rpos) : IsSmoothConnectedClosed (subgroup i a.val.val) :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hi.1 i a.val.val a.val.property.1
  choose U j hj hjc hjs hjconn using hrep
  let A : Option Rpos → GroupScheme (Spec (CommRingCat.of k)) := fun q =>
    match q with
    | none => Z
    | some a => U a
  let f : ∀ q, A q ⟶ G := fun q =>
    match q with
    | none => z
    | some a => j a
  have hA : ∀ q, Smooth (A q).X.hom ∧ IsAffineHom (A q).X.hom ∧
      ConnectedSpace (A q).X.left := by
    intro q
    cases q with
    | none => exact ⟨hzs, hzc.isAffineHom, inferInstance⟩
    | some a => exact ⟨hjs a, (hjc a).isAffineHom, hjconn a⟩
  obtain ⟨H, e, hHs, hHa, hHconn, he⟩ :=
    FiniteGeneration.exists_smooth_generated_family (A := A) (a := f) hA
  let : Smooth H.X.hom := hHs
  let : IsAffineHom H.X.hom := hHa
  let : IsClosedImmersion e.hom.hom.left := he.1
  let : Mono e.hom.hom := Over.mono_of_mono_left _
  have hecent : torusCentralizer i ≤ SubgroupFunctor.range e := by
    rw [← hz.2]
    exact (factorsThrough_hom_iff_range_le z e).1 (he.2.1 none)
  have heroot (a : relativeRoots i) (hpair : 0 ≤ latticePairing S a.val nu) :
      subgroup i a.val ≤ SubgroupFunctor.range e := by
    rw [← (hj ⟨a, hpair⟩).2]
    exact (factorsThrough_hom_iff_range_le (j ⟨a, hpair⟩) e).1
      (he.2.1 (some ⟨a, hpair⟩))
  let chi := CommGroupScheme.groupHom nu ≫ i
  let P := Dynamic.Affine.parabolicScheme chi
  let p : P ⟶ G := Dynamic.Affine.parabolicHom chi
  have hp : (Dynamic.parabolic chi).IsRepresentedBy p :=
    Dynamic.Affine.isRepresentedBy_parabolicHom chi
  have hpc : IsClosedSubgroup p := Dynamic.Affine.isClosedSubgroup_parabolicHom chi
  let : Mono p.hom.hom := hp.1
  let : Smooth P.X.hom := (dynamicSmooth k G chi P p).1 hp
  let : ConnectedSpace P.X.left := ((dynamicConnected k G chi P p).2 inferInstance).1 hp
  let : IsAffineHom P.X.hom := hpc.isAffineHom
  have heP : SubgroupFunctor.range e ≤ SubgroupFunctor.range p := by
    apply he.2.2 P p hpc
    intro q
    apply (factorsThrough_hom_iff_range_le (f q) p).2
    rw [hp.2]
    cases q with
    | none =>
      exact hz.2.le.trans ((torusCentralizer_le_dynamicCentralizer i nu).trans
        (Dynamic.centralizer_le_parabolic chi))
    | some a =>
      exact (hj a).2.le.trans
        (subgroup_le_dynamicParabolic_of_nonneg i hi nu a.val.val a.val.property.1 a.property)
  have hLie : tangentSubmodule (Dynamic.parabolic chi) ≤
      tangentSubmodule (SubgroupFunctor.range e) := by
    rw [tangentSubmodule_parabolic_eq_semigroupWeightSpan hi.1 i nu]
    apply iSup_le
    intro a
    rw [actionWeightSpace_conjugation]
    by_cases ha : a.val = 0
    · rw [ha]
      intro X hX
      exact hecent _ (Lie.mem_torusCentralizer_of_mem_weightSpace_zero i X.toMul hX)
    · by_cases haw : weightSpace i a.val = ⊥
      · rw [haw]
        exact bot_le
      · exact (weightSpace_le_tangentSubmodule_subgroup i hi.1 ha).trans
          (tangentSubmodule_mono (heroot ⟨a.val, ha, haw⟩ a.property))
  let b : H ⟶ P := hp.factorHom e (by rw [← hp.2]; exact heP)
  have hb : b ≫ p = e := hp.factorHom_comp e _
  have hbc : IsClosedSubgroup b := IsClosedSubgroup.of_comp hpc (by rw [hb]; exact he.1)
  have hbtop : SubgroupFunctor.range b = ⊤ := by
    apply lieSubgroupEquality k P H b hbc
    intro X
    have hXp : (Lie.targetMap p k X).val ∈ (Dynamic.parabolic chi).carrier _ := by
      rw [← hp.2]
      exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hLie hXp)
    let Y : lieKernel H k :=
      ⟨y, mem_lieKernel_of_comp e y (hy ▸ (Lie.targetMap p k X).property)⟩
    refine ⟨Y, ?_⟩
    apply (cancel_mono p.hom.hom).mp
    change (y ≫ b.hom.hom) ≫ p.hom.hom = X.val ≫ p.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hb]
    exact hy
  have heD : SubgroupFunctor.range e ≤ SubgroupFunctor.range d := by
    apply he.2.2 D d hd
    intro q
    apply (factorsThrough_hom_iff_range_le (f q) d).2
    cases q with
    | none => exact hz.2.le.trans hcent
    | some a => exact (hj a).2.le.trans (hroot a.val.val a.val.property a.property)
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp (hp.2.symm ▸ hg)
  have hx : x ∈ (SubgroupFunctor.range b).carrier T := by rw [hbtop]; trivial
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply heD T
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hb]

/-- The all-test containment criterion for the dynamic parabolic. -/
def HasNonnegativeRootParabolicGeneration : Prop :=
  ∀ {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G),
    IsClosedSubgroup d →
    torusCentralizer i ≤ SubgroupFunctor.range d →
    (∀ a ∈ relativeRoots i, 0 ≤ latticePairing S a nu →
      subgroup i a ≤ SubgroupFunctor.range d) →
    Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ i) ≤ SubgroupFunctor.range d

/-- Smooth connected affine groups satisfy the criterion for every split
subtorus and every cocharacter of it. -/
theorem hasNonnegativeRootParabolicGeneration :
    HasNonnegativeRootParabolicGeneration i nu := by
  intro D d hd hcent hroot
  exact dynamicParabolic_le_of_nonnegative_rootSubgroups_le i hi nu d hd hcent hroot

end Langlands.GroupScheme.RelativeRoot
