import Langlands.GroupScheme.Lie.UnipotentQuotientTangent
import Langlands.GroupScheme.Unipotent.TorusHom
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Semisimple tangent vectors in prescribed maximal tori of nilpotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G N Q : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every torus maps into the full kernel of a homomorphism with affine
unipotent target, on every test scheme. -/
theorem range_torus_le_unipotent_kernel
    (q : G ⟶ Q) (hAff : IsAffineHom Q.X.hom) (hU : IsUnipotent Q)
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range (kernelι q) := by
  let := hAff
  have hz : j ≫ q = 0 := hT.hom_eq_zero_of_isUnipotent hU (j ≫ q)
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply (mem_range_kernelι_iff q _).mpr
  change (y ≫ j.hom.hom) ≫ q.hom.hom = 1
  rw [Category.assoc]
  change y ≫ (j ≫ q).hom.hom = 1
  rw [hz]
  exact MonObj.comp_one y

/-- The canonical factor of a torus through a monomorphic inclusion whose
all-test range is the full kernel of an affine unipotent quotient. -/
def torusUnipotentKernelFactor
    (i : N ⟶ G) (hi : Mono i.hom.hom) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hAff : IsAffineHom Q.X.hom) (hU : IsUnipotent Q)
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) : T.toGrp ⟶ N :=
  (show (SubgroupFunctor.range i).IsRepresentedBy i from ⟨hi, rfl⟩).factorHom j
    (by rw [← hker]; exact range_torus_le_unipotent_kernel q hAff hU j hT)

@[simp]
theorem torusUnipotentKernelFactor_comp
    (i : N ⟶ G) (hi : Mono i.hom.hom) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hAff : IsAffineHom Q.X.hom) (hU : IsUnipotent Q)
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) :
    torusUnipotentKernelFactor i hi q hker hAff hU j hT ≫ i = j :=
  (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨hi, rfl⟩).factorHom_comp j _

/-- A maximal torus equals any closed torus that is the full kernel of an
affine unipotent quotient. No conjugacy or rational-point hypothesis is used. -/
theorem isIso_torusUnipotentKernelFactor
    {N : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : N.toGrp ⟶ G) (hi : Mono i.hom.hom)
    (hN : IsTorus N.toGrp) (hic : IsClosedSubgroup i) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hAff : IsAffineHom Q.X.hom) (hU : IsUnipotent Q)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j) :
    IsIso (torusUnipotentKernelFactor i hi q hker hAff hU j hj.1) :=
  hj.2.2 N i _ hN hic
    (torusUnipotentKernelFactor_comp i hi q hker hAff hU j hj.1)

namespace Lie

/-- Conditional on the exact central-torus and unipotent-vanishing statements,
every prescribed maximal torus of a smooth connected affine nilpotent group
contains every semisimple actual tangent vector. -/
theorem exists_tangent_lift_of_nilpotent_maximalTorus
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (X : lieKernel G k) (hX : IsSemisimpleElement G X) :
    ∃ Y : lieKernel T.toGrp k, targetMap j k Y = X := by
  obtain ⟨N, i, Q, q, hmax, _, hAff, hU, hq⟩ := hstructure k G hG
  have : IsClosedImmersion i.hom.hom.left := hmax.2.1
  have hi : Mono i.hom.hom := Over.mono_of_mono_left _
  let f := torusUnipotentKernelFactor i hi q hq.2.2.2 hAff hU j hj.1
  have hf : f ≫ i = j :=
    torusUnipotentKernelFactor_comp i hi q hq.2.2.2 hAff hU j hj.1
  have : IsIso f :=
    isIso_torusUnipotentKernelFactor i hi hmax.1 hmax.2.1 q hq.2.2.2 hAff hU j hj
  have hinv : inv f ≫ j = i := by
    rw [← hf, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  obtain ⟨Y, hY⟩ := exists_tangent_lift_of_unipotent_fppf_quotient
    hvan i hi q hq hAff hU X hX
  refine ⟨targetMap (inv f) k Y, ?_⟩
  apply Subtype.ext
  change (Y.val ≫ (inv f).hom.hom) ≫ j.hom.hom = X.val
  rw [Category.assoc, ← Grp.comp_hom_hom, hinv]
  exact congrArg Subtype.val hY

end Lie

end Langlands.GroupScheme
