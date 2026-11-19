import Langlands.CommutativeAlgebra.ZariskiMainFactorization
import Langlands.Geometry.Analytic.AffineAnalytificationFibreIsolationConverse
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteCharts
import Langlands.Geometry.Analytic.AffineAnalytificationPrincipalOpenTransport
import Langlands.Geometry.Analytic.AffineAnalytificationQuasiFiniteStatement
import Langlands.Geometry.Analytic.FiniteCompactNeighborhoods

/-! # Affine analytification detects quasi-finiteness -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set Filter AffinoidAtlasPresentation IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

private theorem quasiFinite_of_analyticQuasifinite
    (hg : StrongHom.IsQuasifinite (A := presentation K Q) (B := presentation K P)
      (saturatedHom K P Q f)) :
    f.toRingHom.QuasiFinite := by
  apply FibreIsolationConverse.quasiFinite_of_forall_isolated P Q f
  intro y
  let : T1Space (presentation K Q).space := inferInstanceAs (T1Space (Space K Q))
  let g := saturatedHom K P Q f
  obtain ⟨V, U, hV, hU, hy, hfin⟩ := hg y
  have hxU : g.baseMap y ∈ U := hfin.1 ⟨y, hy, rfl⟩
  obtain ⟨I, -, hI, hIN⟩ :=
    (atlas K P).exists_finite_recognized_nhds_subset (g.baseMap y) U (hU.mem_nhds hxU)
  obtain ⟨W, hWI, -⟩ := Set.mem_iUnion₂.1 (mem_of_mem_nhds hIN)
  have hF := hfin.finite_fibre W (hI W hWI).2 (hI W hWI).1
  let F : Set (Space K Q) := (V ∩ g.baseMap ⁻¹' {g.baseMap y}) \ {y}
  have hFc : IsClosed F := hF.sdiff.isClosed
  refine ⟨V \ F, hV.sdiff hFc, ⟨hy, ?_⟩, ?_⟩
  · rintro ⟨-, hyy⟩
    exact hyy rfl
  · intro z hz hzy
    by_contra hne
    exact hz.2 ⟨⟨hz.1, hzy⟩, hne⟩

private theorem isFiniteAt_of_finite_preimage_charts
    (hf : f.toRingHom.Finite) (y : Space K Q) :
    (saturatedHom K P Q f).IsFiniteAt y := by
  obtain ⟨m, s, hs⟩ := exists_chart K P (baseMap K P Q f y)
  let n := representative K P (m + 1)
  have hx : baseMap K P Q f y ∈ interior (range (chart K P n.val)) := by
    rw [range_representative K P (m + 1), mem_interior_iff_mem_nhds]
    exact range_chart_mem_nhds K P ⟨s, hs⟩
  obtain ⟨S, h, hpre, hfin⟩ := FiniteCharts.exists_isFiniteBanach_preimage P Q f hf n
  have hy : y ∈ interior (range ((saturated K Q).presentation.atlas.chart S)) := by
    rw [hpre]
    exact interior_maximal (preimage_mono interior_subset)
      (isOpen_interior.preimage (baseMap K P Q f).continuous) hx
  refine StrongHom.isFiniteAt_of_finite_charts
    (A := presentation K Q) (B := presentation K P) (g := saturatedHom K P Q f) S
    ((atlas K P).originalSaturatedIndex n) h hfin hy ?_
  change baseMap K P Q f y ∈
    interior (range ((atlas K P).saturatedChart ((atlas K P).originalSaturatedIndex n)))
  rwa [(atlas K P).range_saturatedChart]

private theorem isFiniteAt_of_quasiFinite
    (hf : f.toRingHom.QuasiFinite) (y : Space K Q) :
    (saturatedHom K P Q f).IsFiniteAt y := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  let : (kernel K Q y).IsPrime := kernel_isPrime K Q y
  obtain ⟨C, hC, hfin, hCtype, r, hr, hrq, hclear⟩ :=
    CommutativeAlgebra.ZariskiMainFactorization.exists_finite_subalgebra_pow_mul_mem
      f hf (kernel K Q y)
  let : Algebra.FiniteType K C := hCtype
  let R := FinitePolynomialPresentation.ofFiniteType K C
  let f₀ := f.codRestrict C hC
  rw [← AlgHom.val_comp_codRestrict f C hC]
  refine PrincipalOpenTransport.isFiniteAt_comp_of_away R Q C.val ⟨r, hr⟩ P f₀
    Subtype.val_injective ?_ y ?_
    (isFiniteAt_of_finite_preimage_charts P R f₀ hfin (baseMap K R Q C.val y))
  · intro b
    obtain ⟨n, hn⟩ := hclear b
    exact ⟨⟨_, hn⟩, n, rfl⟩
  · rw [pointSeminorm_baseMap]
    exact fun h => hrq ((mem_kernel K Q y r).mpr h)

/-- An affine algebraic map is quasi-finite exactly when its analytification
is finite at every point. -/
theorem affineAnalytificationQuasiFinite :
    AffineAnalytificationQuasiFiniteStatement.{u, v, w} := by
  intro K _ _ _ A _ _ B _ _ P Q f
  exact ⟨isFiniteAt_of_quasiFinite P Q f, quasiFinite_of_analyticQuasifinite P Q f⟩

end Langlands.Analytic.AffineAnalytification
