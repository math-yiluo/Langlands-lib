import Langlands.GroupScheme.SubgroupFunctor.QuotientPreimage
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.ActionDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Closed subgroup embeddings induced on fpqc quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {B G BQ Q : GroupScheme S}
    (i : B ⟶ G) (q : G ⟶ Q) (qB : B ⟶ BQ)
    (hkernel : range (kernelι qB) ≤ (range (kernelι q)).comap i)

include hkernel in
/-- Compatibility of actual kernels is precisely enough to descend the
subgroup inclusion followed by the ambient quotient. -/
theorem kernel_comp_quotient_eq_zero :
    kernelι qB ≫ (i ≫ q) = 0 := by
  apply Grp.hom_ext
  change (kernelι qB).hom.hom ≫ (i ≫ q).hom.hom = 1
  rw [Grp.comp_hom_hom, ← Category.assoc]
  apply (mem_range_kernelι_iff q _).mp
  apply hkernel (kernel qB).X
  exact mem_range.mpr ⟨𝟙 (kernel qB).X, Category.id_comp _⟩

variable [Flat qB.hom.hom.left] [Surjective qB.hom.hom.left]
    [QuasiCompact qB.hom.hom.left]

/-- The actual homomorphism induced on the two supplied quotient groups. -/
def quotientSubgroupHom : BQ ⟶ Q :=
  FpqcHomDescent.hom qB (i ≫ q)
    (kernel_comp_quotient_eq_zero i q qB hkernel)

/-- The induced homomorphism completes the original quotient square. -/
theorem quotientSubgroupHom_square :
    i ≫ q = qB ≫ quotientSubgroupHom i q qB hkernel :=
  (FpqcHomDescent.fac qB (i ≫ q)
    (kernel_comp_quotient_eq_zero i q qB hkernel)).symm

include hkernel in
/-- No other homomorphism can complete this square. -/
theorem quotientSubgroupHom_unique (j : BQ ⟶ Q) (hj : i ≫ q = qB ≫ j) :
    j = quotientSubgroupHom i q qB hkernel :=
  FpqcHomDescent.unique qB (i ≫ q)
    (kernel_comp_quotient_eq_zero i q qB hkernel) j hj.symm

section ExactKernel

variable
    (hkernel' : (range (kernelι q)).comap i ≤ range (kernelι qB))

include hkernel hkernel' in
/-- With exact inverse image of the ambient kernel, the quotient subgroup
homomorphism has trivial kernel on every test scheme. -/
theorem quotientSubgroupHom_point_eq_one {T : Over S} (x : T ⟶ BQ.X)
    (hx : x ≫ (quotientSubgroupHom i q qB hkernel).hom.hom = 1) : x = 1 := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift qB x
  intro V p b hp
  rw [MonObj.comp_one, hp]
  apply (mem_range_kernelι_iff qB b).mp
  apply hkernel' V
  apply (mem_range_kernelι_iff q (b ≫ i.hom.hom)).mpr
  have hs : i.hom.hom ≫ q.hom.hom =
      qB.hom.hom ≫ (quotientSubgroupHom i q qB hkernel).hom.hom :=
    congrArg (fun f => f.hom.hom)
      (quotientSubgroupHom_square i q qB hkernel)
  calc
    _ = (b ≫ qB.hom.hom) ≫
        (quotientSubgroupHom i q qB hkernel).hom.hom := by
      rw [Category.assoc, hs, ← Category.assoc]
    _ = (p ≫ x) ≫
        (quotientSubgroupHom i q qB hkernel).hom.hom := by rw [hp]
    _ = 1 := by rw [Category.assoc, hx, MonObj.comp_one]

include hkernel hkernel' in
/-- The induced quotient subgroup morphism is monic over the original base. -/
theorem quotientSubgroupHom_mono :
    Mono (quotientSubgroupHom i q qB hkernel).hom.hom := by
  constructor
  intro T x y hxy
  have he : (x⁻¹ * y) ≫
      (quotientSubgroupHom i q qB hkernel).hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, inv_mul_cancel]
  exact inv_mul_eq_one.mp
    (quotientSubgroupHom_point_eq_one i q qB hkernel hkernel' (x⁻¹ * y) he)

variable [Mono i.hom.hom]
    (hcontain : range (kernelι q) ≤ range i)

include hkernel hkernel' hcontain in
/-- The induced quotient square is cartesian on actual schemes over the base. -/
theorem quotientSubgroupHom_isPullback :
    IsPullback i.hom.hom qB.hom.hom q.hom.hom
      (quotientSubgroupHom i q qB hkernel).hom.hom := by
  let j := quotientSubgroupHom i q qB hkernel
  have : Mono j.hom.hom := quotientSubgroupHom_mono i q qB hkernel hkernel'
  have hs : i.hom.hom ≫ q.hom.hom = qB.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom)
      (quotientSubgroupHom_square i q qB hkernel)
  let liftPoint := fun (c : PullbackCone q.hom.hom j.hom.hom) =>
    quotientPreimagePoint i q qB j
      (quotientSubgroupHom_square i q qB hkernel) hcontain c.fst
      (mem_range.mpr ⟨c.snd, c.condition.symm⟩)
  have hfst (c : PullbackCone q.hom.hom j.hom.hom) :
      liftPoint c ≫ i.hom.hom = c.fst :=
    quotientPreimagePoint_comp i q qB j
      (quotientSubgroupHom_square i q qB hkernel) hcontain c.fst
      (mem_range.mpr ⟨c.snd, c.condition.symm⟩)
  refine ⟨⟨hs⟩, ⟨PullbackCone.IsLimit.mk _ liftPoint hfst ?_ ?_⟩⟩
  · intro c
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, ← hs, ← Category.assoc, hfst, c.condition]
  · intro c m hm hn
    apply (cancel_mono i.hom.hom).mp
    exact hm.trans (hfst c).symm

include hkernel hkernel' hcontain in
/-- If the ambient quotient is fpqc, closedness descends from the original
subgroup to its actual quotient embedding. -/
theorem quotientSubgroupHom_isClosedSubgroup
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (quotientSubgroupHom i q qB hkernel) := by
  let j := quotientSubgroupHom i q qB hkernel
  have hpb : IsPullback i.hom.hom.left qB.hom.hom.left q.hom.hom.left
      j.hom.hom.left :=
    (quotientSubgroupHom_isPullback i q qB hkernel hkernel' hcontain).map
      (Over.forget S)
  have : Mono j.hom.hom := quotientSubgroupHom_mono i q qB hkernel hkernel'
  have : IsClosedImmersion i.hom.hom.left := hi
  have : UniversallyClosed j.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hpb ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : LocallyOfFiniteType j.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @LocallyOfFiniteType) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hpb ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsProper j.hom.hom.left := ⟨⟩
  exact (IsClosedImmersion.iff_isProper_and_mono j.hom.hom.left).mpr
    ⟨inferInstance, inferInstance⟩

include hkernel hcontain in
/-- The quotient embedding has exactly the original subgroup as inverse image. -/
theorem quotientSubgroupHom_comap_range :
    (range (quotientSubgroupHom i q qB hkernel)).comap q = range i :=
  comap_range_eq_of_fpqc_square i q qB
    (quotientSubgroupHom i q qB hkernel)
    (quotientSubgroupHom_square i q qB hkernel) hcontain

end ExactKernel

end Langlands.GroupScheme.SubgroupFunctor
