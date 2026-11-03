import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Rational.WeightSupportVanishing
import Langlands.GroupScheme.Lie.ZeroTangentTriviality
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Semigroup subgroups with no occurring tangent weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A connected affine finite-type representative with zero tangent image
represents the identity subgroup on every test scheme. -/
theorem eq_bot_of_isRepresentedBy_of_tangentSubmodule_eq_bot
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) {F : SubgroupFunctor G} (hj : F.IsRepresentedBy j)
    (hF : tangentSubmodule F = ⊥) : F = ⊥ := by
  have : Mono j.hom.hom := hj.1
  have hrange : LinearMap.range (Lie.targetMapLinear j k) = ⊥ :=
    ((hasLieImage_iff_tangentSubmodule_eq F _).mp
      (hasLieImage_of_isRepresentedBy j hj)).symm.trans hF
  have hzero (X : Additive (lieKernel H k)) : X = 0 := by
    apply Lie.targetMapLinear_injective j k
    have hX : Lie.targetMapLinear j k X ∈
        (⊥ : Submodule k (Additive (lieKernel G k))) := by
      rw [← hrange]
      exact LinearMap.mem_range_self _ X
    simpa only [Submodule.mem_bot, map_zero] using hX
  have : Subsingleton (lieKernel H k) := ⟨fun X Y =>
    Additive.ofMul.injective ((hzero (Additive.ofMul X)).trans
      (hzero (Additive.ofMul Y)).symm)⟩
  rw [← hj.2]
  apply le_antisymm
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [Lie.points_eq_one_of_subsingleton_lieKernel H T y, MonObj.one_comp]
    exact Subgroup.one_mem _
  · intro T x hx
    have hx : x = 1 := hx
    subst x
    exact Subgroup.one_mem _

/-- A smooth connected closed subgroup with zero tangent image is the identity
subgroup on all tests. -/
theorem IsSmoothConnectedClosed.eq_bot_of_tangentSubmodule_eq_bot
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hLie : tangentSubmodule F = ⊥) : F = ⊥ := by
  obtain ⟨H, j, hj, hclosed, hsmooth, hconn⟩ := hF
  have : IsAffineHom H.X.hom := hclosed.isAffineHom
  have : Smooth H.X.hom := hsmooth
  have : ConnectedSpace H.X.left := hconn
  exact eq_bot_of_isRepresentedBy_of_tangentSubmodule_eq_bot j hj hLie

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)

include hS

/-- An empty support makes the tangent image of a represented stable subgroup
zero. Only the representative needs to be locally of finite type. -/
theorem tangentSubmodule_eq_bot_of_actionWeightSupport_eq_empty
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (j : H ⟶ G) {F : SubgroupFunctor G} (hj : F.IsRepresentedBy j)
    (hstable : b.IsStable F) (hsupport : actionWeightSupport b F = ∅) :
    tangentSubmodule F = ⊥ := by
  rw [tangentSubmodule_eq_iSup_weight_inf b hS j hj hstable]
  apply iSup_eq_bot.mpr
  intro χ
  by_contra hχ
  have hmem := (mem_actionWeightSupport_iff b F χ).mpr hχ
  simp only [hsupport, Set.mem_empty_iff_false] at hmem

/-- A smooth connected invariant closed subgroup with no occurring weights is
the identity subgroup, without assuming semigroup realization. -/
theorem IsSmoothConnectedClosed.eq_bot_of_actionWeightSupport_eq_empty
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : b.IsStable F) (hsupport : actionWeightSupport b F = ∅) : F = ⊥ := by
  obtain ⟨H, j, hj, hclosed, hsmooth, hconn⟩ := hF
  have : IsAffineHom H.X.hom := hclosed.isAffineHom
  have : Smooth H.X.hom := hsmooth
  have : ConnectedSpace H.X.left := hconn
  exact eq_bot_of_isRepresentedBy_of_tangentSubmodule_eq_bot j hj
    (tangentSubmodule_eq_bot_of_actionWeightSupport_eq_empty b hS j hj hstable hsupport)

/-- If a semigroup selects no ambient tangent weight, every generator is
trivial and its generated all-test subgroup is trivial. -/
theorem semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization
    (A : AddSubsemigroup (characterLattice S)) (hA : HasNoAmbientWeights b A) :
    semigroupSubgroup b A = ⊥ := by
  apply le_antisymm
  · apply (semigroupSubgroup_le_iff b A ⊥).mpr
    intro F hF
    have hsupport : actionWeightSupport b F = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro χ hχ
      exact hA χ (hF.2.2 hχ)
        (actionWeightSupport_mono b (fun _ _ _ => Subgroup.mem_top _) hχ)
    exact le_of_eq
      (IsSmoothConnectedClosed.eq_bot_of_actionWeightSupport_eq_empty
        b hS hF.1 hF.2.1 hsupport)
  · intro T x hx
    have hx : x = 1 := hx
    subst x
    exact Subgroup.one_mem _

/-- The empty-semigroup subgroup is trivial, with no ambient smoothness or
semigroup realization hypothesis. -/
theorem semigroupSubgroup_bot_without_realization :
    semigroupSubgroup b ⊥ = ⊥ := by
  apply semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization b hS
  intro χ hχ
  exact False.elim hχ

/-- Every representative of a semigroup with no ambient weights is canonically
isomorphic to the trivial group scheme. -/
def noAmbientWeightsRepresentativeIso
    (A : AddSubsemigroup (characterLattice S)) (hA : HasNoAmbientWeights b A)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (semigroupSubgroup b A).IsRepresentedBy j) :
    H ≅ Grp.trivial (Over (Spec (CommRingCat.of k))) :=
  hj.isoOfIsRepresentedBy (by
    rw [semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization b hS A hA]
    exact bot_isRepresentedBy_kernelUnit G)

end Langlands.GroupScheme.RelativeRoot
