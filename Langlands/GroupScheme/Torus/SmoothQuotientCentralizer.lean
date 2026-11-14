import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Lie.TargetCoefficients
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Lie.SurjectiveDifferentialLifting
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.KernelRepresentativeTransport

/-! # Smooth homomorphisms restricted to whole-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSmoothQuotient

section Base

variable {S : Scheme.{u}} {T : CommGroupScheme S}
  {G H C E : GroupScheme S}
  (i : T.toGrp ⟶ G) (q : G ⟶ H)
  (j : C ⟶ G) (l : E ⟶ H)
  (hj : (torusCentralizer i).IsRepresentedBy j)
  (hl : (torusCentralizer (i ≫ q)).IsRepresentedBy l)

include hj in
/-- Postcomposition preserves commutation with every torus point on every
refinement of a test scheme. -/
theorem range_comp_le :
    SubgroupFunctor.range (j ≫ q) ≤ torusCentralizer (i ≫ q) := by
  rintro U _ ⟨x, rfl⟩ V a t
  have h := congrArg (fun z => z ≫ q.hom.hom)
    (((hj.pointsEquiv U x).property V a t).eq)
  apply (commute_iff_eq _ _).mpr
  change (a ≫ x ≫ (j ≫ q).hom.hom) * (t ≫ (i ≫ q).hom.hom) =
    (t ≫ (i ≫ q).hom.hom) * (a ≫ x ≫ (j ≫ q).hom.hom)
  simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
    Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp] using h

/-- Restrict an actual homomorphism to representatives of the full
whole-torus centralizers. -/
def centralizerMap : C ⟶ E :=
  hl.factorHom (j ≫ q) (range_comp_le i q j hj)

@[reassoc]
theorem centralizerMap_comp :
    centralizerMap i q j l hj hl ≫ l = j ≫ q :=
  hl.factorHom_comp _ _

end Base

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H C E : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [Smooth G.X.hom] [Smooth H.X.hom]
  [IsAffineHom C.X.hom] [IsAffineHom E.X.hom]
  [Smooth C.X.hom] [Smooth E.X.hom]
  (hT : IsSplitTorus T.toGrp)
  (i : T.toGrp ⟶ G) (q : G ⟶ H)
  (j : C ⟶ G) (l : E ⟶ H)
  (hj : (torusCentralizer i).IsRepresentedBy j)
  (hl : (torusCentralizer (i ≫ q)).IsRepresentedBy l)

include hT in
omit [Smooth C.X.hom] [Smooth E.X.hom] in
/-- Smoothness of the ambient map gives a surjective actual differential
on full whole-torus centralizers, including disconnected representatives. -/
theorem centralizerMap_differential_surjective
    (hq : Smooth q.hom.hom.left) :
    Function.Surjective (Lie.targetMapLinear (centralizerMap i q j l hj hl) k) := by
  let : Mono j.hom.hom := hj.1
  let : Mono l.hom.hom := hl.1
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  intro Y
  have hY : Lie.targetMapLinear l k Y ∈ weightSpace (i ≫ q) 0 := by
    apply Lie.mem_weightSpace_zero_of_mem_torusCentralizer (i ≫ q)
      (Lie.targetMap l k Y.toMul)
    rw [← hl.2]
    exact ⟨Y.toMul.val, rfl⟩
  obtain ⟨X0, hX0⟩ := Lie.targetMapLinear_surjective_of_smooth q k hq
    (Lie.targetMapLinear l k Y)
  obtain ⟨X, hX, hXY⟩ :=
    Lie.exists_weightSpace_preimage q i hT hY ⟨X0, hX0⟩
  have hXrange : X ∈ LinearMap.range (Lie.targetMapLinear j k) := by
    rw [← RelativeRoot.tangentSubmodule_range j, hj.2]
    exact Lie.mem_torusCentralizer_of_mem_weightSpace_zero i X.toMul hX
  obtain ⟨Z, rfl⟩ := hXrange
  refine ⟨Z, ?_⟩
  apply Lie.targetMapLinear_injective l k
  have hc := congrArg (fun f : C ⟶ H => Lie.targetMapLinear f k Z)
    (centralizerMap_comp i q j l hj hl)
  simpa only [Lie.targetMapLinear_comp, LinearMap.comp_apply] using hc.trans hXY

include hT in
/-- A smooth homomorphism restricts to a smooth homomorphism between full
whole-torus centralizers. Surjectivity of this restriction is not asserted. -/
theorem centralizerMap_smooth (hq : Smooth q.hom.hom.left) :
    Smooth (centralizerMap i q j l hj hl).hom.hom.left :=
  Lie.smooth_of_surjective_differential (centralizerMap i q j l hj hl)
    inferInstance (centralizerMap_differential_surjective hT i q j l hj hl hq)

include hT i l hj hl in
/-- The original composite from a full centralizer into the ambient target
has smooth full scheme-theoretic kernel. -/
theorem smooth_kernel_comp (hq : Smooth q.hom.hom.left) :
    Smooth (kernel (j ≫ q)).X.hom := by
  let p := centralizerMap i q j l hj hl
  let : Smooth p.hom.hom.left := centralizerMap_smooth hT i q j l hj hl hq
  have : Smooth (kernel p).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme p) inferInstance
  let : Mono l.hom.hom := hl.1
  have hk : SubgroupFunctor.range (kernelι (j ≫ q)) =
      SubgroupFunctor.range (kernelι p) := by
    rw [← centralizerMap_comp i q j l hj hl]
    exact range_kernelι_comp_mono p l
  exact KernelRepresentative.smooth (j ≫ q) (kernelι p) hk

end Field

end Langlands.GroupScheme.TorusSmoothQuotient
