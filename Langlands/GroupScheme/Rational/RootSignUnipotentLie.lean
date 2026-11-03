import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.MultiplicativeGeometry

/-! # Actual-root detection of dynamic unipotent inclusion through Lie algebras -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)

/-- For an arbitrary multiplicative-group action on a smooth connected affine
group, if every Lie vector has identity limit, every point has identity limit. -/
theorem unipotent_eq_top_of_lieKernel
    (hlie : ∀ X : lieKernel G k, X.val ∈ a.unipotent.carrier _) :
    a.unipotent = ⊤ := by
  let K := Affine.unipotentScheme a
  let κ := Affine.unipotentHom a
  have hκ : a.unipotent.IsRepresentedBy κ := Affine.isRepresentedBy_unipotentHom a
  have hκc : IsClosedSubgroup κ := Affine.isClosedSubgroup_unipotentHom a
  have : Mono κ.hom.hom := hκ.1
  have : Smooth K.X.hom := Affine.smooth_unipotentScheme a
  have htop : SubgroupFunctor.range κ = ⊤ := by
    refine lieSubgroupEquality k G K κ hκc fun X => ?_
    have hX := hlie X
    rw [← hκ.2] at hX
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hX
    refine ⟨⟨y, mem_lieKernel_of_comp κ y ?_⟩, hy⟩
    rw [hy]
    exact X.property
  rw [← hκ.2, htop]

end AutomorphicAction

namespace Dynamic

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Inclusion of the Lie kernels of two dynamic identity-limit subgroups for a
common commutative group implies inclusion on every test scheme. Connectedness
of the first unipotent representative follows from its polynomial contraction. -/
theorem unipotent_le_of_lieKernel_of_smooth
    (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S)
    (hlie : ∀ X : lieKernel G k,
      X.val ∈ (unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier _ →
      X.val ∈ (unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier _) :
    unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
      unipotent (CommGroupScheme.groupHom eta ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨H, j, hj, hjc⟩ :
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        (unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j ∧
          IsClosedSubgroup j :=
    ⟨_, _, Affine.isRepresentedBy_unipotentHom _,
      Affine.isClosedSubgroup_unipotentHom _⟩
  have : Mono j.hom.hom := hj.1
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Smooth H.X.hom := (dynamicSmooth k G _ H j).2.2 hj
  have : ConnectedSpace H.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _ hj
  let b := AutomorphicAction.cocharacterAction (CommGroupScheme.groupHom eta ≫ i)
  have hstable : b.IsStable (unipotent (CommGroupScheme.groupHom zeta ≫ i)) := by
    intro T t g hg
    dsimp only [b]
    rw [AutomorphicAction.cocharacterAction_eq_conjugation,
      ← AutomorphicAction.restrict_conjugation, AutomorphicAction.restrict_act]
    exact unipotent_isStable_conjugation i (CommGroupScheme.groupHom zeta)
      T (t ≫ (CommGroupScheme.groupHom eta).hom.hom) g hg
  let a := b.onRepresentedSubgroup j hj hstable
  have heqv : a.IsEquivariant b j := fun _ _ =>
    b.onRepresentedSubgroup_act_comp j hj hstable _ _
  have heq : a.unipotent =
      (unipotent (CommGroupScheme.groupHom eta ≫ i)).comap j := by
    have h := heqv.unipotent_eq_comap_of_isClosedSubgroup hjc
    simpa only [b, AutomorphicAction.cocharacterAction_unipotent] using h
  have htop : a.unipotent = ⊤ := by
    apply a.unipotent_eq_top_of_lieKernel
    intro X
    rw [heq, SubgroupFunctor.mem_comap]
    apply hlie (Lie.targetMap j k X)
    rw [← hj.2]
    exact SubgroupFunctor.mem_range.2 ⟨X.val, rfl⟩
  intro T g hg
  rw [← hj.2] at hg
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  have hh : h ∈ a.unipotent.carrier T := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [heq, SubgroupFunctor.mem_comap] at hh
  exact hh

/-- The earlier conditional interface follows from the unconditional smooth
radical comparison. -/
theorem unipotent_le_of_lieKernel
    (hCo : DynamicConnectedStatement.{u}) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S)
    (hlie : ∀ X : lieKernel G k,
      X.val ∈ (unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier _ →
      X.val ∈ (unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier _) :
    unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
      unipotent (CommGroupScheme.groupHom eta ≫ i) := by
  have _ := hCo
  exact unipotent_le_of_lieKernel_of_smooth i zeta eta hlie

end Dynamic

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The exact tangent submodule of a dynamic identity-limit subgroup is the
strictly positive torus weight span. -/
theorem tangentSubmodule_unipotent_eq_semigroupWeightSpan
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) =
      semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν) := by
  rw [semigroupWeightSpan_conjugation_positive hS i ν]
  ext X
  exact (dynamicLie k G (CommGroupScheme.groupHom ν ≫ i) X.toMul).2.2

/-- Unipotent inclusion implies containment of positive actual-root regions
without any smoothness or connectedness hypothesis. -/
theorem positive_rootSupport_of_unipotent_le
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S)
    (h : Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    ∀ χ ∈ relativeRoots i,
      0 < latticePairing S χ zeta → 0 < latticePairing S χ eta := by
  apply (positive_rootSupport_iff i zeta eta).mpr
  apply (semigroupWeightSpan_le_iff_on_weightSupport
    (AutomorphicAction.conjugation i) hS _ _).mp
  rw [← tangentSubmodule_unipotent_eq_semigroupWeightSpan hS i zeta,
    ← tangentSubmodule_unipotent_eq_semigroupWeightSpan hS i eta]
  intro X hX
  exact h _ hX

/-- On a smooth affine group, inclusion of dynamic identity-limit subgroups is
exactly containment of the positive regions on actual relative roots. -/
theorem unipotent_le_iff_positive_rootSupport_of_smooth
    [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ χ ∈ relativeRoots i,
        0 < latticePairing S χ zeta → 0 < latticePairing S χ eta := by
  constructor
  · exact positive_rootSupport_of_unipotent_le hS i zeta eta
  · intro h
    have hspan := (semigroupWeightSpan_le_iff_on_weightSupport
      (AutomorphicAction.conjugation i) hS _ _).mpr
        ((positive_rootSupport_iff i zeta eta).mp h)
    rw [semigroupWeightSpan_conjugation_positive hS i zeta,
      semigroupWeightSpan_conjugation_positive hS i eta] at hspan
    apply Dynamic.unipotent_le_of_lieKernel_of_smooth i zeta eta
    intro X hX
    exact (dynamicLie k G (CommGroupScheme.groupHom eta ≫ i) X).2.2.mpr
      (hspan ((dynamicLie k G (CommGroupScheme.groupHom zeta ≫ i) X).2.2.mp hX))

/-- The earlier conditional interface follows from the unconditional smooth
actual-root radical criterion. -/
theorem unipotent_le_iff_positive_rootSupport
    (hCo : DynamicConnectedStatement.{u}) [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ χ ∈ relativeRoots i,
        0 < latticePairing S χ zeta → 0 < latticePairing S χ eta := by
  have _ := hCo
  exact unipotent_le_iff_positive_rootSupport_of_smooth hS i zeta eta

end RelativeRoot

/-- Actual-root detection of dynamic radical inclusion for every homomorphism
from a split torus into a smooth affine group over any field. -/
def RootSignUnipotentInclusionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (_hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (zeta eta : cocharacterLattice S),
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ χ ∈ relativeRoots i,
        0 < latticePairing S χ zeta → 0 < latticePairing S χ eta

/-- The radical criterion has no dynamic connectedness premise. -/
theorem rootSignUnipotentInclusions : RootSignUnipotentInclusionsStatement.{u} := by
  intro k _ G _ _ S hS i zeta eta
  exact RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hS i zeta eta

/-- Dynamic connectedness alone suffices for the exact full root-sign target. -/
def RelativeRootSignInclusionsFromConnectedness : Prop :=
  DynamicConnectedStatement.{u} → RelativeRootSignInclusionsStatement.{u}

/-- Both root-sign inclusion conclusions follow from published Lie, smoothness,
and full-Lie subgroup-equality proofs, with parabolic connectedness retained
explicitly. -/
theorem relativeRootSignInclusions_of_connectedness :
    RelativeRootSignInclusionsFromConnectedness.{u} := by
  intro hCo k _ G hG T i hi zeta eta
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  constructor
  · exact RelativeRoot.parabolic_le_iff_nonnegative_rootSupport hCo hi.1.1 i zeta eta
  · exact (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hi.1.1 i zeta eta).mpr

end Langlands.GroupScheme
