import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalInclusion
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Reductivity of smooth connected normal closed subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H V : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {s : V ⟶ H}

/-- In an ambient group with trivial ground-field radical, the radical of
a smooth connected affine normal closed subgroup has trivial full range. -/
theorem IsUnipotentRadical.range_eq_bot_of_normal
    (hs : IsUnipotentRadical s) (hG : HasTrivialUnipotentRadical G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    SubgroupFunctor.range s = ⊥ := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hkill : SubgroupFunctor.range (s ≫ i) = ⊥ :=
    hG V (s ≫ i) (hs.isClosedSubgroup.comp hi) hs.smooth
      hs.connectedSpace hs.isUnipotent (hs.isNormal_comp i hi hn)
  apply le_antisymm
  · intro T x hx
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    change v ≫ s.hom.hom = 1
    apply (cancel_mono i.hom.hom).mp
    have hx : v ≫ (s ≫ i).hom.hom ∈
        (SubgroupFunctor.range (s ≫ i)).carrier T :=
      SubgroupFunctor.mem_range.2 ⟨v, rfl⟩
    rw [hkill] at hx
    simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot,
      Grp.comp_hom_hom, Category.assoc, MonObj.one_comp] using hx
  · intro T
    exact (show (⊥ : Subgroup (T ⟶ H.X)) ≤
      (SubgroupFunctor.range s).carrier T from bot_le)

/-- The radical of such a normal subgroup is canonically isomorphic to
the trivial group scheme, including on all nonreduced tests. -/
def IsUnipotentRadical.normalSubgroupTrivialIso
    (hs : IsUnipotentRadical s) (hG : HasTrivialUnipotentRadical G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    V ≅ Grp.trivial (Over (Spec (CommRingCat.of k))) := by
  let : IsClosedImmersion s.hom.hom.left := hs.isClosedSubgroup
  let : Mono s.hom.hom := Over.mono_of_mono_left _
  exact (show (⊥ : SubgroupFunctor H).IsRepresentedBy s from
    ⟨inferInstance, hs.range_eq_bot_of_normal hG i hi hn⟩).isoOfIsRepresentedBy
      (bot_isRepresentedBy_kernelUnit H)

@[simp] theorem IsUnipotentRadical.normalSubgroupTrivialIso_hom_comp
    (hs : IsUnipotentRadical s) (hG : HasTrivialUnipotentRadical G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    (hs.normalSubgroupTrivialIso hG i hi hn).hom ≫ kernelUnit H = s := by
  let : IsClosedImmersion s.hom.hom.left := hs.isClosedSubgroup
  let : Mono s.hom.hom := Over.mono_of_mono_left _
  exact (show (⊥ : SubgroupFunctor H).IsRepresentedBy s from
    ⟨inferInstance, hs.range_eq_bot_of_normal hG i hi hn⟩).isoOfIsRepresentedBy_hom_comp
      (bot_isRepresentedBy_kernelUnit H)

/-- Triviality of the radical passes to smooth connected affine normal
closed subgroups over an algebraically closed field. -/
theorem HasTrivialUnipotentRadical.of_normalSubgroup
    (hG : HasTrivialUnipotentRadical G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    HasTrivialUnipotentRadical H := by
  obtain ⟨V, s, hs⟩ := unipotentRadicalExistence k H
  have hsbot := hs.range_eq_bot_of_normal hG i hi hn
  intro W j hj hsmooth hconnected hunipotent hnormal
  apply le_antisymm
  · rw [← hsbot]
    exact hs.greatest W j hj hsmooth hconnected hunipotent hnormal
  · intro T
    exact (show (⊥ : Subgroup (T ⟶ H.X)) ≤
      (SubgroupFunctor.range j).carrier T from bot_le)

end AlgebraicallyClosed

section GeneralField

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- Every smooth connected normal closed subgroup of a connected
reductive group over a field is connected reductive. -/
theorem IsConnectedReductive.of_normalSubgroup
    (hG : IsConnectedReductive G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    IsConnectedReductive H := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom H.X.hom := by
    rw [← i.hom.hom.w]
    infer_instance
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  let b := toAlgebraicClosure k
  let G' := (GroupScheme.baseChange b).obj G
  let H' := (GroupScheme.baseChange b).obj H
  let i' := (GroupScheme.baseChange b).map i
  let : Smooth G'.X.hom := by
    change Smooth (Limits.pullback.snd G.X.hom b)
    infer_instance
  let : Smooth H'.X.hom := by
    change Smooth (Limits.pullback.snd H.X.hom b)
    infer_instance
  let : IsAffineHom H'.X.hom := by
    change IsAffineHom (Limits.pullback.snd H.X.hom b)
    infer_instance
  let : ConnectedSpace H'.X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have hn' : (SubgroupFunctor.range i').IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  exact hG.hasTrivialGeometricUnipotentRadical.of_normalSubgroup
    (G := G') (H := H') i' (hi.baseChange b) hn'

end GeneralField

end Langlands.GroupScheme
