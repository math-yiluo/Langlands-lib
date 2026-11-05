import Langlands.GroupScheme.Reductive.SplitRadicalWoundQuotientStatement
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionStatement
import Langlands.GroupScheme.Rational.SplitSeriesExtension
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent
import Langlands.GroupScheme.Rational.VectorGroupSplit
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.SubgroupPreimageKernel
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction

/-! # Woundness reduction for the quotient by a split radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual central closed additive subgroup, with its representative,
inclusion, and natural one-dimensional vector coordinates. -/
structure CentralAdditiveClosedSubgroup {k : Type u} [Field k]
    (Q : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ Q
  isClosedSubgroup : IsClosedSubgroup inclusion
  isCentral : IsCentral inclusion
  isVectorGroupOfDimension : RelativeRoot.IsVectorGroupOfDimension group 1

namespace CentralAdditiveClosedSubgroup

variable {k : Type u} [Field k]
    {Q : GroupScheme (Spec (CommRingCat.of k))}

/-- The bundled data has precisely the existential meaning used by the
published central additive-subgroup criterion. -/
theorem nonempty_iff :
    Nonempty (CentralAdditiveClosedSubgroup Q) ↔
      ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ Q),
        IsClosedSubgroup j ∧ IsCentral j ∧
          RelativeRoot.IsVectorGroupOfDimension V 1 := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.group, A.inclusion, A.isClosedSubgroup, A.isCentral,
      A.isVectorGroupOfDimension⟩
  · rintro ⟨V, j, hj, hjz, hV⟩
    exact ⟨⟨V, j, hj, hjz, hV⟩⟩

end CentralAdditiveClosedSubgroup

namespace SubgroupPreimage

variable {k : Type u} [Field k]
    {G N Q H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    {i : N ⟶ G} {q : G ⟶ Q}

/-- An actual inverse image of a split subgroup under an fppf quotient with
smooth connected split kernel is split, with the existing finite-series meaning. -/
theorem isSplitUnipotent_of_fppfQuotient
    (hi : IsClosedSubgroup i) [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (hN : RelativeRoot.IsSplitUnipotent N)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (j : H ⟶ Q) (hj : IsClosedSubgroup j)
    (hH : RelativeRoot.IsSplitUnipotent H) :
    RelativeRoot.IsSplitUnipotent (groupScheme q j) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := hi.isAffineHom
  let : GeometricallyConnected N.X.hom := geometricallyConnected_of_connected N
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : IsAffineHom (groupScheme q j).X.hom := isAffineHom q j hj
  let : IsAffineHom (kernel q).X.hom := KernelRepresentative.isAffineHom q i hq.2.2.2
  let : Smooth (kernel q).X.hom := KernelRepresentative.smooth q i hq.2.2.2
  let : GeometricallyConnected (kernel q).X.hom :=
    KernelRepresentative.geometricallyConnected q i hq.2.2.2
  let e := kernelOverIso q j
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let : Smooth (kernel (projection q j)).X.hom := by
    rw [← e.hom.w]
    infer_instance
  let : GeometricallyConnected (kernel (projection q j)).X.hom := by
    have hp : IsPullback e.hom.left (kernel (projection q j)).X.hom
        (kernel q).X.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using e.hom.w⟩
    exact MorphismProperty.of_isPullback hp inferInstance
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  let : Flat (projection q j).hom.hom.left := flat_projection q j
  let : Surjective (projection q j).hom.hom.left := surjective_projection q j
  let : LocallyOfFinitePresentation (projection q j).hom.hom.left :=
    MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance
  let : QuasiCompact (projection q j).hom.hom.left := quasiCompact_projection q j
  have hK : RelativeRoot.IsSplitUnipotent (kernel (projection q j)) :=
    hN.of_iso ((KernelRepresentative.iso q i hq.2.2.2).symm.trans (kernelIso q j).symm)
  obtain ⟨m, hm⟩ := hK
  obtain ⟨n, hn⟩ := hH
  exact ⟨m + n, hm.of_fppfQuotient n (kernelι (projection q j)) (projection q j)
    (inferInstanceAs (IsClosedImmersion (kernelι (projection q j)).hom.hom.left))
    inferInstance ⟨inferInstance, inferInstance, inferInstance, rfl⟩ hn⟩

end SubgroupPreimage

namespace IsSplitUnipotentRadical

variable {k : Type u} [Field k]
    {G N Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    {i : N ⟶ G} (hi : IsSplitUnipotentRadical i)
    {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)

include hi hq

/-- A quotient by a represented split radical has no central closed additive
subgroup. This uses maximality only on the normal inverse image. -/
theorem not_exists_central_additive_closed_subgroup :
    ¬ ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ Q),
      IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension V 1 := by
  rintro ⟨V, j, hj, hjz, hV⟩
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := hi.isClosedSubgroup.isAffineHom
  let : Smooth N.X.hom := hi.smooth
  let : ConnectedSpace N.X.left := hi.connectedSpace
  let : GeometricallyConnected N.X.hom := geometricallyConnected_of_connected N
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  let : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hi.smooth
  let : GeometricallyConnected (kernel q).X.hom :=
    KernelRepresentative.geometricallyConnected q i hq.2.2.2
  let : Smooth V.X.hom := hV.smooth
  let : ConnectedSpace V.X.left := hV.connectedSpace
  let : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj
  have hsplit := SubgroupPreimage.isSplitUnipotent_of_fppfQuotient
    hi.isClosedSubgroup hi.isSplitUnipotent hq j hj hV.isSplitUnipotent
  have hle : SubgroupFunctor.range (SubgroupPreimage.inclusion q j) ≤
      SubgroupFunctor.range (kernelι q) := by
    rw [hq.2.2.2]
    exact hi.greatest _ _ (SubgroupPreimage.isClosedSubgroup q j hj)
      (SubgroupPreimage.smooth q j)
      (SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q j)
      hsplit.isUnipotent hsplit (SubgroupPreimage.isNormal q j hjz.range_isNormal)
  have hj0 := SubgroupPreimage.range_eq_bot_of_range_inclusion_le_kernel q j hle
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨x, hx⟩ := hV.exists_rationalPoint_ne_one (by decide)
  apply hx
  apply (cancel_mono j.hom.hom).mp
  have hxj : x ≫ j.hom.hom ∈ (SubgroupFunctor.range j).carrier _ := ⟨x, rfl⟩
  rw [hj0, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hxj
  exact hxj.trans (MonObj.one_comp _).symm

/-- There is no actual central closed additive-subgroup datum in a quotient
by a represented split radical. -/
theorem isEmpty_centralAdditiveClosedSubgroup :
    IsEmpty (CentralAdditiveClosedSubgroup Q) :=
  ⟨fun A => hi.not_exists_central_additive_closed_subgroup hq
    (CentralAdditiveClosedSubgroup.nonempty_iff.mp ⟨A⟩)⟩

/-- The central additive-subgroup criterion makes every supplied smooth
connected affine quotient by a split radical wound when its source is unipotent. -/
theorem hasConstantAffineLineMaps_quotient_of_criterion
    (hcriterion : UnipotentWoundCriterionStatement.{u})
    [Smooth Q.X.hom] [ConnectedSpace Q.X.left] (hG : IsUnipotent G) :
    HasConstantAffineLineMaps Q :=
  (hcriterion k Q inferInstance inferInstance inferInstance (hq.isUnipotent hG)).mpr
    (hi.not_exists_central_additive_closed_subgroup hq)

end IsSplitUnipotentRadical

end Langlands.GroupScheme
