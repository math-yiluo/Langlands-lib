import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights

/-! # Actual root maps induced by smooth quotient homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot.SmoothQuotient

section Base

variable {B : Scheme.{u}} {S : CommGroupScheme B}
    {H G U V : GroupScheme B}
    (i : S.toGrp ⟶ H) (q : H ⟶ G) (a : characterLattice S)
    (j : U ⟶ H) (l : V ⟶ G)
    (hj : (subgroup i a).IsRepresentedBy j)
    (hl : (subgroup (i ≫ q) a).IsRepresentedBy l)

include hj in
/-- The original composite root map lands in the full target root functor. -/
theorem range_comp_le :
    SubgroupFunctor.range (j ≫ q) ≤ subgroup (i ≫ q) a := by
  rintro T _ ⟨x, rfl⟩
  change (x ≫ j.hom.hom) ≫ q.hom.hom ∈ _
  exact comp_mem_subgroup i a q (hj.pointsEquiv T x).property

/-- The canonical map between actual root representatives induced by `q`. -/
def rootMap : U ⟶ V :=
  hl.factorHom (j ≫ q) (range_comp_le i q a j hj)

/-- The root map has the prescribed composite in the ambient target. -/
theorem rootMap_comp : rootMap i q a j l hj hl ≫ l = j ≫ q :=
  hl.factorHom_comp _ _

end Base

section Field

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ H) (q : H ⟶ G) (a : characterLattice S) (ha : a ≠ 0)
    (j : U ⟶ H) (l : V ⟶ G)
    (hj : (subgroup i a).IsRepresentedBy j)
    (hl : (subgroup (i ≫ q) a).IsRepresentedBy l)

omit [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [Smooth G.X.hom] in
private theorem conjugation_equivariant :
    ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      (AutomorphicAction.conjugation i).act s x ≫ q.hom.hom =
        (AutomorphicAction.conjugation (i ≫ q)).act s (x ≫ q.hom.hom) := by
  intro T s x
  simp only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

include hS ha in
/-- A smooth scheme surjection induces a smooth scheme surjection between
every pair of full root representatives, for every nonzero character. -/
theorem rootMap_smooth_surjective
    (hq : Smooth q.hom.hom.left) (hqs : Surjective q.hom.hom.left) :
    Smooth (rootMap i q a j l hj hl).hom.hom.left ∧
      Surjective (rootMap i q a j l hj hl).hom.hom.left := by
  have hj' : (semigroupSubgroup (AutomorphicAction.conjugation i)
      (cyclicTail a 1)).IsRepresentedBy j := by
    change (weightFiltration (AutomorphicAction.conjugation i) a 1).IsRepresentedBy j
    rwa [weightFiltration_one_eq_subgroup hS i a ha]
  have hl' : (semigroupSubgroup (AutomorphicAction.conjugation (i ≫ q))
      (cyclicTail a 1)).IsRepresentedBy l := by
    change (weightFiltration (AutomorphicAction.conjugation (i ≫ q)) a 1).IsRepresentedBy l
    rwa [weightFiltration_one_eq_subgroup hS (i ≫ q) a ha]
  obtain ⟨p, hp, hps, hpurj⟩ := semigroupSmoothQuotient k H G
    inferInstance inferInstance inferInstance inferInstance S hS
    (AutomorphicAction.conjugation i) (AutomorphicAction.conjugation (i ≫ q))
    q hq hqs (conjugation_equivariant i q)
    (cyclicTail a 1) U V j l hj' hl'
  have he : rootMap i q a j l hj hl = p :=
    hl.hom_ext ((rootMap_comp i q a j l hj hl).trans hp)
  rw [he]
  exact ⟨hps, hpurj⟩

include hS ha hj hl in
/-- The full original composite has smooth scheme-theoretic kernel.
This retains the entire kernel, including all infinitesimal test points. -/
theorem smooth_kernel_comp
    (hq : Smooth q.hom.hom.left) (hqs : Surjective q.hom.hom.left) :
    Smooth (kernel (j ≫ q)).X.hom := by
  let p := rootMap i q a j l hj hl
  have : Smooth p.hom.hom.left :=
    (rootMap_smooth_surjective hS i q a ha j l hj hl hq hqs).1
  have : Smooth (kernel p).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme p) inferInstance
  have : Mono l.hom.hom := hl.1
  have hk : SubgroupFunctor.range (kernelι (j ≫ q)) =
      SubgroupFunctor.range (kernelι p) := by
    rw [← rootMap_comp i q a j l hj hl]
    exact range_kernelι_comp_mono p l
  exact KernelRepresentative.smooth (j ≫ q) (kernelι p) hk

variable [IsAffineHom U.X.hom]

include hS ha hj in
/-- The original root-to-target differential has exactly the full target
positive cyclic weight span. Only smoothness of the ambient map is needed
for this linear conclusion. -/
theorem lie_range_comp (hq : Smooth q.hom.hom.left) :
    LinearMap.range (Lie.targetMapLinear (j ≫ q) k) =
      semigroupWeightSpan (AutomorphicAction.conjugation (i ≫ q)) (cyclicTail a 1) := by
  have : Mono j.hom.hom := hj.1
  have hr : LinearMap.range (Lie.targetMapLinear j k) =
      semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) := by
    rw [← tangentSubmodule_range j, hj.2]
    exact tangentSubmodule_subgroup i a hS ha
  rw [Lie.targetMapLinear_comp, LinearMap.range_comp, hr]
  exact map_semigroupWeightSpan_eq_of_smooth
    (AutomorphicAction.conjugation i) (AutomorphicAction.conjugation (i ≫ q))
    hS q (conjugation_equivariant i q) hq (cyclicTail a 1)

end Field

end Langlands.GroupScheme.RelativeRoot.SmoothQuotient
