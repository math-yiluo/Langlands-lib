import Langlands.Geometry.Analytic.SpaceAnalytificationRationalPointsStatement
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleRationalNeighborhood
import Langlands.Geometry.Analytic.SpaceAnalytificationRationalPointContinuity
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective

/-! # Hausdorffness and the topology of rational points of analytifications -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory Opposite Set Topology SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open AffineAnalytification

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

set_option backward.isDefEq.respectTransparency false in
private theorem isInducing_rationalPoint (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    (P₀ : FinitePolynomialPresentation K K) :
    @IsInducing _ _ (etaleChartTopology K X) _ (rationalPoint p P₀) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  have hcont : Continuous (rationalPoint p P₀) := hp.continuous_rationalPoint P₀
  refine ⟨le_antisymm hcont.le_induced ?_⟩
  intro W hW
  apply (@isOpen_iff_forall_mem_open _ (TopologicalSpace.induced (rationalPoint p P₀) _) W).2
  intro y hy
  obtain ⟨c, q, hc, hq⟩ :=
    exists_affine_chart_pointMap_eq (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX) hXft y
  let : IsAffine c.scheme.left := hc
  let : LocallyOfFiniteType c.scheme.hom := c.locallyOfFiniteType
  let A := AffineCoordinateRing K c.scheme
  let P := FinitePolynomialPresentation.ofFiniteType K A
  let e := affineSchemeOverIso K c.scheme
  let a := AlgebraicSpace.hom c.hom
  let aA := (schemeYoneda _).map e.inv ≫ a
  let x : RingPoints K X A := uliftYonedaEquiv aA
  have hx : IsEtale (pointHom K x) := by
    change IsEtale (uliftYonedaEquiv.symm (uliftYonedaEquiv aA))
    rw [Equiv.symm_apply_apply]
    exact IsEtale.comp (isEtale_map e.inv inferInstance) c.isEtale
  let ePoints := affineSchemePointHomeomorph K c.scheme K
  have hchange (r : RingPoint K c.scheme K) :
      RingPoints.changeRing (ePoints r).toAlgHom x = c.pointMap r := by
    have hr : ringTestMap K (ePoints r).toAlgHom = r ≫ e.hom := by
      apply Over.OverMorphism.ext
      exact affineSchemePointEquiv_spec K K r
    change X.presheaf.map (ringTestMap K (ePoints r).toAlgHom).op (uliftYonedaEquiv aA) = _
    rw [← schemeYoneda_app_up aA (ringTestMap K (ePoints r).toAlgHom)]
    change a.app (op (ringTest K K))
      (ULift.up (ringTestMap K (ePoints r).toAlgHom ≫ e.inv)) = _
    rw [hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  let φ := ePoints q
  have hyx : RingPoints.changeRing φ.toAlgHom x = y := (hchange q).trans hq
  have hchart : Continuous c.pointMap := by
    have h := c.continuous_pointMap
    rw [schemePointTopology_eq_affine K c.scheme K] at h
    exact h
  have hpre : IsOpen ((fun ψ : AlgPoint K A K => RingPoints.changeRing ψ.toAlgHom x) ⁻¹' W) := by
    have hmap : (fun ψ : AlgPoint K A K => RingPoints.changeRing ψ.toAlgHom x) =
        c.pointMap ∘ ePoints.symm := by
      funext ψ
      have h := hchange (ePoints.symm ψ)
      rwa [ePoints.apply_symm_apply] at h
    rw [hmap]
    exact (hchart.comp ePoints.symm.continuous).isOpen_preimage _ hW
  obtain ⟨V, hV, hVeq⟩ :=
    (RationalPointComparison.isEmbedding_analyticPoint K P).isInducing.isOpen_iff.mp hpre
  obtain ⟨U, hU, hφU, hLift⟩ := hp.etaleChartRationalNeighborhoods hX P₀ P x hx φ
  let F : Space K P → localizedSpaceFunctor.obj Y := localizedSpaceFunctor.map (p A P x)
  have hF : IsOpenMap F := etaleOpenMap K _ (hp.etale_map P x hx)
  let G := F '' (V ∩ U)
  refine ⟨rationalPoint p P₀ ⁻¹' G, ?_,
    isOpen_induced_iff.mpr ⟨G, hF _ (hV.inter hU), rfl⟩, ?_⟩
  · rintro y' ⟨z, ⟨hzV, hzU⟩, hzEq⟩
    obtain ⟨ψ, hψ⟩ := hLift z hzU y' hzEq
    have hy' : RingPoints.changeRing ψ.toAlgHom x = y' :=
      hp.rationalPoint_injective hX P₀ ((hp.rationalPoint_changeRing P₀ P x ψ).trans
        ((congrArg F hψ).trans hzEq))
    have hψV : ψ ∈ analyticPoint K P ⁻¹' V := by
      change analyticPoint K P ψ ∈ V
      rwa [hψ]
    rw [hVeq] at hψV
    exact hy' ▸ (show RingPoints.changeRing ψ.toAlgHom x ∈ W from hψV)
  · have hφW :
        φ ∈ (fun ψ : AlgPoint K A K => RingPoints.changeRing ψ.toAlgHom x) ⁻¹' W := by
      change RingPoints.changeRing φ.toAlgHom x ∈ W
      rwa [hyx]
    rw [← hVeq] at hφW
    exact ⟨analyticPoint K P φ, ⟨hφW, hφU⟩,
      (hp.rationalPoint_changeRing P₀ P x φ).symm.trans (congrArg (rationalPoint p P₀) hyx)⟩

/-- The analytification of a separated algebraic space locally of finite type
is Hausdorff, and its rational-point map is an embedding for the étale-chart topology. -/
theorem spaceAnalytificationRationalPoints : SpaceAnalytificationRationalPointsStatement.{u} := by
  intro K _ _ _ X hX hXft Y p hp
  refine ⟨hp.t2Space_of_isSeparated hX, ?_⟩
  intro P₀
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  exact ⟨isInducing_rationalPoint hp hX hXft P₀, hp.rationalPoint_injective hX P₀⟩

end Langlands.Analytic.SpaceAnalytification
