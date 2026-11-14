import Langlands.GroupScheme.Absolute.UnipotentQuotientParabolics
import Langlands.GroupScheme.Rational.ParabolicFunctor
import Langlands.GroupScheme.SubgroupFunctor.FpqcComap

/-! # The parabolic order correspondence for a unipotent quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace UnipotentQuotientParabolics

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)

include hq

/-- Full inverse image sends actual parabolic subgroup functors to actual
parabolic subgroup functors. -/
theorem isParabolicFunctor_comap {F : SubgroupFunctor Q}
    (hF : IsParabolicFunctor F) : IsParabolicFunctor (F.comap q) := by
  obtain ⟨P, j, hj, rfl⟩ := hF
  exact ⟨SubgroupPreimage.groupScheme q j, SubgroupPreimage.inclusion q j,
    isParabolicSubgroup_preimage q hq j hj, SubgroupPreimage.range_inclusion q j⟩

/-- Full inverse image is an order embedding on actual parabolic subgroup
functors. -/
def parabolicComapOrderEmbedding : ParabolicFunctor Q ↪o ParabolicFunctor G where
  toFun F := ⟨F.val.comap q, isParabolicFunctor_comap q hq F.property⟩
  inj' := by
    intro F E h
    obtain ⟨P, j, hj, hjF⟩ := F.property
    obtain ⟨R, i, hi, hiE⟩ := E.property
    have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
    have : Mono i.hom.hom := hi.isClosedSubgroup.mono_overHom
    have hval : F.val.comap q = E.val.comap q := congrArg Subtype.val h
    apply Subtype.ext
    apply le_antisymm
    · exact (SubgroupFunctor.comap_le_iff_of_isRepresentedBy q
        (show E.val.IsRepresentedBy i from ⟨inferInstance, hiE⟩)).mp hval.le
    · exact (SubgroupFunctor.comap_le_iff_of_isRepresentedBy q
        (show F.val.IsRepresentedBy j from ⟨inferInstance, hjF⟩)).mp hval.ge
  map_rel_iff' := by
    intro F E
    obtain ⟨P, j, hj, hjE⟩ := E.property
    have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
    exact SubgroupFunctor.comap_le_iff_of_isRepresentedBy q
      (show E.val.IsRepresentedBy j from ⟨inferInstance, hjE⟩)

/-- Every actual source parabolic is the full inverse image of an actual
target parabolic. -/
theorem parabolicComapOrderEmbedding_surjective :
    Function.Surjective (parabolicComapOrderEmbedding q hq) := by
  intro F
  obtain ⟨P, i, hi, hiF⟩ := F.property
  obtain ⟨I, j, p, hj, _, _, _, _, _, heq, _⟩ :=
    exists_parabolic_image q hq i hi
  exact ⟨⟨SubgroupFunctor.range j, ⟨I, j, hj, rfl⟩⟩,
    Subtype.ext (heq.trans hiF)⟩

/-- The inclusion order of actual parabolics is unchanged by a quotient
with smooth connected unipotent actual kernel. The forward map is full
inverse image on all scheme tests. -/
def parabolicComapOrderIso : ParabolicFunctor Q ≃o ParabolicFunctor G :=
  OrderIso.ofSurjective (parabolicComapOrderEmbedding q hq)
    (parabolicComapOrderEmbedding_surjective q hq)

@[simp] theorem parabolicComapOrderIso_apply_coe (F : ParabolicFunctor Q) :
    (parabolicComapOrderIso q hq F).val = F.val.comap q :=
  rfl

/-- The inverse order map is characterized by its exact full inverse image. -/
@[simp] theorem parabolicComapOrderIso_symm_comap (F : ParabolicFunctor G) :
    ((parabolicComapOrderIso q hq).symm F).val.comap q = F.val := by
  exact congrArg Subtype.val ((parabolicComapOrderIso q hq).apply_symm_apply F)

end UnipotentQuotientParabolics

/-- Full inverse image under a supplied unipotent-kernel quotient is an
order isomorphism of the existing actual parabolic subgroup functors. -/
def UnipotentQuotientParabolicOrderStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left],
    HasSmoothConnectedUnipotentKernel q →
      ∃ e : ParabolicFunctor Q ≃o ParabolicFunctor G,
        (∀ F : ParabolicFunctor Q, (e F).val = F.val.comap q) ∧
        (∀ F : ParabolicFunctor G, (e.symm F).val.comap q = F.val)

/-- The parabolic order correspondence follows from constructed parabolic
images, actual preimages, and fpqc reflection of represented containment. -/
theorem unipotentQuotientParabolicOrder :
    UnipotentQuotientParabolicOrderStatement.{u} := by
  intro k _ G Q _ _ _ _ q _ _ _ hq
  exact ⟨UnipotentQuotientParabolics.parabolicComapOrderIso q hq,
    UnipotentQuotientParabolics.parabolicComapOrderIso_apply_coe q hq,
    UnipotentQuotientParabolics.parabolicComapOrderIso_symm_comap q hq⟩

end Langlands.GroupScheme
