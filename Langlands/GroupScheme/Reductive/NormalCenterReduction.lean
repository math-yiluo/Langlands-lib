import Langlands.GroupScheme.GroupLikeClosedSubgroup
import Langlands.GroupScheme.Adjoint.Action
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Reductive.NormalCenterStatement
import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusStatement
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.TrivialAction

/-! # Full-centre containment from a centre-containing split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {A H Z : GroupScheme B} (a : AutomorphicAction A H)

/-- The induced actual automorphic action on a represented full centre. -/
def onRepresentedCenter (z : Z ⟶ H) (hz : (center H).IsRepresentedBy z) :
    AutomorphicAction A Z :=
  a.onRepresentedSubgroup z hz a.isStable_center

/-- The centre inclusion intertwines the induced action and the original one. -/
theorem onRepresentedCenter_act_comp (z : Z ⟶ H)
    (hz : (center H).IsRepresentedBy z) {T : Over B}
    (h : T ⟶ A.X) (x : T ⟶ Z.X) :
    (a.onRepresentedCenter z hz).act h x ≫ z.hom.hom =
      a.act h (x ≫ z.hom.hom) :=
  a.onRepresentedSubgroup_act_comp z hz a.isStable_center h x

end AutomorphicAction

section SplitCenter

variable {k : Type u} [Field k]
    {G H Z S : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffine G.X.left] [ConnectedSpace G.X.left]
    [IsAffine Z.X.left]

/-- If the full centre of a normal subgroup embeds as a closed subgroup of a
split torus, that centre maps into the full centre of the smooth connected
ambient group. No smoothness of the centre is required. -/
theorem center_le_comap_of_normal_of_center_split_embedding
    (i : H ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (z : Z ⟶ H) (hz : (center H).IsRepresentedBy z)
    (hS : IsSplitTorus S) (j : Z ⟶ S) (hj : IsClosedSubgroup j) :
    center H ≤ (center G).comap i := by
  have hn' : (SubgroupFunctor.range i).IsNormalizedBy
      (SubgroupFunctor.range (𝟙 G)) := by
    intro T g x _ hx
    exact hn T g x (Subgroup.mem_top _) hx
  let a := AutomorphicAction.ofNormalizedConjugation i (𝟙 G) hn'
  let b := a.onRepresentedCenter z hz
  intro T x hx
  change x ≫ i.hom.hom ∈ (center G).carrier T
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.1 (hz.2.symm ▸ hx)
  intro V d g
  have ht := hS.act_eq_self_of_isClosedSubgroup j hj b g (d ≫ c)
  have he := congrArg (fun p => p ≫ z.hom.hom) ht
  rw [AutomorphicAction.onRepresentedCenter_act_comp] at he
  have he' := congrArg (fun p => p ≫ i.hom.hom) he
  have hconj := SubgroupFunctor.lift_comp_normalizedConjugation_comp
    i (𝟙 G) hn' g ((d ≫ c) ≫ z.hom.hom)
  change a.act g ((d ≫ c) ≫ z.hom.hom) ≫ i.hom.hom = _ at hconj
  rw [he'] at hconj
  simp only [Grp.id_hom_hom, Category.comp_id, Category.assoc, hc] at hconj
  exact ((mul_inv_eq_iff_eq_mul.mp hconj.symm) :
    g * (d ≫ x ≫ i.hom.hom) = (d ≫ x ≫ i.hom.hom) * g).symm

end SplitCenter

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, the trivial-action specialization of
the fixed-torus proposition implies full-centre containment for a normal
connected reductive subgroup. -/
theorem center_le_comap_of_normal_of_fixedCenterContainingTorus_of_isAlgClosed
    (hFixed : FixedCenterContainingTorusStatement.{u})
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    center H ≤ (center G).comap i := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k H hH
  let : IsClosedImmersion z.hom.hom.left := hz.1
  let : IsAffineHom Z.X.hom := by
    rw [← z.hom.hom.w]
    infer_instance
  let : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  obtain ⟨S, t, hS, ht, hc, _⟩ := hFixed k H hH
    (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm
    (AutomorphicAction.trivial _ H)
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  have htrep : (SubgroupFunctor.range t).IsRepresentedBy t := ⟨inferInstance, rfl⟩
  let j := htrep.factorHom z (hz.2 ▸ hc)
  have hj : IsClosedSubgroup j := IsClosedSubgroup.of_comp ht (by
    rw [SubgroupFunctor.IsRepresentedBy.factorHom_comp]
    exact hz.1)
  exact center_le_comap_of_normal_of_center_split_embedding
    i hn z hz.isRepresentedBy hS j hj

end AlgebraicallyClosed

end Langlands.GroupScheme
