import Langlands.GroupScheme.Lie.NilpotentTorusTangent
import Langlands.GroupScheme.Lie.TorusElementCentralizer
import Langlands.GroupScheme.Lie.ElementCentralizerTorus
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.CentralizerSmoothProof
import Langlands.GroupScheme.Cartan.LieInduction

/-! # Conditional Cartan tangent containment and maximal-torus preservation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H D : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

namespace Lie

/-- A monomorphic homomorphism reflects all-test centralization of a tangent
vector, when that vector is already lifted to its source. -/
theorem range_le_elementCentralizer_of_mono
    (j : H ⟶ G) (hj : Mono j.hom.hom)
    (i : T.toGrp ⟶ H) (Y : lieKernel H k)
    (h : SubgroupFunctor.range (i ≫ j) ≤ elementCentralizer G (targetMap j k Y)) :
    SubgroupFunctor.range i ≤ elementCentralizer H Y := by
  intro U x hx A _ _ a
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hc := h U (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩) A a
  rw [lieKernelMap_target] at hc
  apply (commute_iff_eq _ _).mpr
  apply hj.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simpa only [constant, affineMap_apply, lieKernelTarget_val,
    Grp.comp_hom_hom, Category.assoc] using hc.eq

section Cartan

variable [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (i : T.toGrp ⟶ H) (hi : IsMaximalTorus i)
    (d : D ⟶ H) (hrep : (torusCentralizer i).IsRepresentedBy d)
    (hd : IsClosedSubgroup d)
    (hconn : ConnectedSpace D.X.left) (hnil : IsNilpotentGroupScheme D)
    (X : lieKernel H k) (hfix : SubgroupFunctor.range i ≤ elementCentralizer H X)
    (hsem : ∀ Y : lieKernel D k, targetMap d k Y = X → IsSemisimpleElement D Y)

/-- The canonical tangent factor into a prescribed maximal torus. The
connected nilpotence of its represented Cartan and semisimplicity of the
Cartan lift are explicit premises. -/
def cartanTangentFactor : lieKernel T.toGrp k := by
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth D.X.hom :=
    torusCentralizerSmooth k H T i hi.1 hi.2.1 D d hrep hd
  have : IsClosedImmersion d.hom.hom.left := hd
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  let : ConnectedSpace D.X.left := hconn
  let Y := torusCentralizerTangentFactor i d hrep X hfix
  have hY : targetMap d k Y = X :=
    targetMap_torusCentralizerTangentFactor i d hrep X hfix
  exact Classical.choose
    (exists_tangent_lift_of_nilpotent_maximalTorus hstructure hvan hnil
      (torusCentralizerFactor i hrep)
      (hi.isMaximalTorus_torusCentralizerFactor hrep hd) Y (hsem Y hY))

@[simp]
theorem targetMap_cartanTangentFactor :
    targetMap i k
      (cartanTangentFactor hstructure hvan i hi d hrep hd hconn hnil X hfix hsem) = X := by
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth D.X.hom :=
    torusCentralizerSmooth k H T i hi.1 hi.2.1 D d hrep hd
  have : IsClosedImmersion d.hom.hom.left := hd
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  let : ConnectedSpace D.X.left := hconn
  let Y := torusCentralizerTangentFactor i d hrep X hfix
  have hY : targetMap d k Y = X :=
    targetMap_torusCentralizerTangentFactor i d hrep X hfix
  have he := Classical.choose_spec
    (exists_tangent_lift_of_nilpotent_maximalTorus hstructure hvan hnil
      (torusCentralizerFactor i hrep)
      (hi.isMaximalTorus_torusCentralizerFactor hrep hd) Y (hsem Y hY))
  change targetMap i k
    (Classical.choose (exists_tangent_lift_of_nilpotent_maximalTorus
      hstructure hvan hnil (torusCentralizerFactor i hrep)
      (hi.isMaximalTorus_torusCentralizerFactor hrep hd) Y (hsem Y hY))) = X
  rw [← hY]
  apply Subtype.ext
  rw [lieKernelTarget_val, lieKernelTarget_val, ← congrArg Subtype.val he]
  change _ = (_ ≫ (torusCentralizerFactor i hrep).hom.hom) ≫ d.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, torusCentralizerFactor_comp]

end Cartan

end Lie

end Langlands.GroupScheme
