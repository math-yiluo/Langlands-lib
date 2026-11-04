import Langlands.GroupScheme.Lie.UnipotentSemisimpleStatement
import Langlands.GroupScheme.Nilpotent.CentralTorusStatement
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Semisimple tangent lifts through kernels with unipotent quotient -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
    {G N Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A semisimple actual tangent element lifts canonically through a monomorphic
kernel inclusion when its affine finite-type quotient is unipotent. The
unipotent vanishing theorem is retained as the explicit structural input. -/
def unipotentQuotientTangentFactor
    (hvan : UnipotentSemisimpleStatement.{u})
    (i : N ⟶ G) (hi : Mono i.hom.hom) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hAff : IsAffineHom Q.X.hom) (hLFT : LocallyOfFiniteType Q.X.hom)
    (hU : IsUnipotent Q) (X : lieKernel G k) (hX : IsSemisimpleElement G X) :
    lieKernel N k := by
  have hz := hvan k Q hAff hLFT hU (targetMap q k X) (hX.map q)
  have hm : X.val ∈ (SubgroupFunctor.range i).carrier
      ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) := by
    rw [← hker, mem_range_kernelι_iff]
    exact congrArg Subtype.val hz
  let hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨hi, rfl⟩
  let y := (hrep.pointsEquiv _).symm ⟨X.val, hm⟩
  have hy : y ≫ i.hom.hom = X.val := hrep.pointsEquiv_symm_comp _
  have : Mono i.hom.hom := hi
  refine ⟨y, mem_lieKernel_of_comp i y ?_⟩
  rw [hy]
  exact X.property

@[simp]
theorem targetMap_unipotentQuotientTangentFactor
    (hvan : UnipotentSemisimpleStatement.{u})
    (i : N ⟶ G) (hi : Mono i.hom.hom) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hAff : IsAffineHom Q.X.hom) (hLFT : LocallyOfFiniteType Q.X.hom)
    (hU : IsUnipotent Q) (X : lieKernel G k) (hX : IsSemisimpleElement G X) :
    targetMap i k
      (unipotentQuotientTangentFactor hvan i hi q hker hAff hLFT hU X hX) = X := by
  apply Subtype.ext
  exact (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨hi, rfl⟩).pointsEquiv_symm_comp _

/-- For an fppf quotient of a smooth group, finite type of the target follows
from smooth-target descent. Thus no separate target finiteness premise is needed. -/
theorem exists_tangent_lift_of_unipotent_fppf_quotient
    (hvan : UnipotentSemisimpleStatement.{u}) [Smooth G.X.hom]
    (i : N ⟶ G) (hi : Mono i.hom.hom) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hAff : IsAffineHom Q.X.hom) (hU : IsUnipotent Q)
    (X : lieKernel G k) (hX : IsSemisimpleElement G X) :
    ∃ Y : lieKernel N k, targetMap i k Y = X := by
  have : Smooth Q.X.hom := hq.smooth_target
  exact ⟨unipotentQuotientTangentFactor hvan i hi q hq.2.2.2 hAff
    inferInstance hU X hX, targetMap_unipotentQuotientTangentFactor
      hvan i hi q hq.2.2.2 hAff inferInstance hU X hX⟩

/-- Conditional on the two explicit structural inputs, one central maximal
torus of a smooth connected affine nilpotent group contains every semisimple
actual tangent element. The chosen torus is independent of the tangent element. -/
theorem exists_maximalTorus_forall_semisimple_tangent
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i ∧ IsCentral i ∧
        ∀ X : lieKernel G k, IsSemisimpleElement G X →
          ∃ Y : lieKernel T.toGrp k, targetMap i k Y = X := by
  obtain ⟨T, i, Q, q, hmax, hc, hAff, hU, hq⟩ := hstructure k G hG
  have : IsClosedImmersion i.hom.hom.left := hmax.2.1
  have hi : Mono i.hom.hom := Over.mono_of_mono_left _
  exact ⟨T, i, hmax, hc, fun X hX =>
    exists_tangent_lift_of_unipotent_fppf_quotient hvan i hi q hq hAff hU X hX⟩

end Langlands.GroupScheme.Lie
