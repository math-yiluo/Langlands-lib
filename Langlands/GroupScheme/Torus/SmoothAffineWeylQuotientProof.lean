import Langlands.GroupScheme.Torus.SmoothAffineWeylQuotientStatement
import Langlands.GroupScheme.Torus.RelativeNormalizerSmooth
import Langlands.GroupScheme.Torus.CentralizerOpenInNormalizer
import Langlands.GroupScheme.Torus.CentralizerQuotient
import Langlands.GroupScheme.HomogeneousQuotientGroup

/-! # The smooth-affine torus Weyl quotient over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- The general smooth-affine torus Weyl quotient, with actual all-test
normalizer, centralizer, and kernel over every base scheme. -/
theorem smoothAffineTorusWeylQuotient : SmoothAffineTorusWeylQuotientStatement.{u} := by
  intro S G hGs hGa T t hT ht
  let : Smooth G.X.hom := hGs
  let : IsAffineHom G.X.hom := hGa
  let : Mono t.hom.hom.left := ht.mono
  obtain ⟨N, n, hnclosed, hnfp, hNs, hnrep⟩ :=
    relativeTorusSmoothNormalizerModel t hT ht
  let : Smooth N.X.hom := hNs
  let : IsClosedImmersion n.hom.hom.left := hnclosed
  let : IsAffineHom N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  obtain ⟨Z, z, hzclosed, hZs, hzrep⟩ := relativeTorusCentralizerModel t hT hGs
  obtain ⟨c, hcn, hcopen, hcrep⟩ :=
    relativeTorusCentralizerNormalizerInclusion t hT n hnrep z hzrep
  let : Mono c.hom.hom := hcrep.1
  have hcclosed : IsClosedSubgroup c :=
    IsClosedSubgroup.of_comp hnclosed (by rw [hcn]; exact hzclosed)
  let D := TorusCentralizerQuotient.homogeneousQuotient t hT n c hcrep hcclosed hZs
  let : Smooth D.projection.left := D.smooth_projection
  let : Surjective D.projection.left := D.surjective_projection
  have hnormal : (SubgroupFunctor.range c).IsNormal := by
    rw [hcrep.2]
    intro U g x _ hx
    change (g * x * g⁻¹) ≫ n.hom.hom ∈ (torusCentralizer t).carrier U
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    apply torusCentralizer_isNormalizedBy_torusNormalizer t U
      (g ≫ n.hom.hom) (x ≫ n.hom.hom) ?_ hx
    rw [← hnrep.2]
    exact ⟨g, rfl⟩
  let W := D.groupScheme hnormal
  let q : N ⟶ W := D.groupProjection hnormal
  have hq := D.groupProjection_isFppfQuotient hnormal
  have hWe : Etale W.X.hom :=
    etale_of_open_subgroup_quotient c hcopen D.projection D.fibers
  refine ⟨N, n, Z, z, W, q, hnclosed, hnrep, hzclosed, hzrep,
    D.separated, D.quasiCompact, hWe, hq.1, hq.2.1, hq.2.2.1, ?_⟩
  intro U y
  rw [← SubgroupFunctor.mem_comap, ← hcrep.2, ← hq.2.2.2, mem_range_kernelι_iff]

end Langlands.GroupScheme
