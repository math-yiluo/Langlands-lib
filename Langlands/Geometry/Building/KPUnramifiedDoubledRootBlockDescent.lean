import Langlands.Geometry.Building.KPUnramifiedScaledRootDepth
import Langlands.Geometry.Building.UnramifiedDoubledRootDepthModelStatement
import Langlands.GroupScheme.UnramifiedIntegralRationalFactorDescent

/-! # Conditional doubled-root block descent for concrete apartment lifts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance doubledRootBlockAffineHom {F : Type u} [Field F]
    {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

local notation "Fur" => UnramifiedClosure F

/-- Exact comparison on all maximal-unramified points with the doubled-root
scaled subgroup at twice the intended block depth. -/
def IsDoubledRootDepthModelAt
    (y : P.Apartment) (a : relativeRoots P.i) (r : ℝ≥0)
    {U : GroupScheme (Spec (CommRingCat.of F))} (q : U ⟶ G)
    (M : IntegralModel 𝒪[F] F U) : Prop :=
  ∀ w : rationalPoints (baseChanged F Fur U),
    M.HasIntegralCoordinates Fur (baseChangeCoeffEquiv F Fur U w) ↔
      rationalPoints.map
        ((GroupScheme.baseChange (algebraBaseMap F Fur)).map q) w ∈
          L.scaledRootDepth y (2 • a.val) (2 * (r : ℝ))

/-- A smooth connected model with the exact doubled-depth comparison suffices
to descend the uniform upper fibre to the two lower factors at their original
common depth. Model existence remains a hypothesis. -/
theorem block_mem_rootFiber_of_doubledRootModel
    (y : P.Apartment) (a : relativeRoots P.i)
    (h2a : 2 • a.val ∈ relativeRoots P.i)
    (U : GroupScheme (Spec (CommRingCat.of F))) (q : U ⟶ G)
    (hq : (RelativeRoot.subgroup P.i (2 • a.val)).IsRepresentedBy q)
    (hqc : IsClosedSubgroup q)
    (r : ℝ≥0) (M : IntegralModel 𝒪[F] F U) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    (hmodel : L.IsDoubledRootDepthModelAt y a r q M)
    (g : rationalPoints G)
    (hg : rationalExtend F Fur G g ∈
      L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r) :
    g ∈ P.apartment.filtrationBlock y (fun _ => (r : ℝ)) a.val := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsClosedImmersion q.hom.hom.left := hqc
  let : IsAffineHom U.X.hom := by
    rw [← q.hom.hom.w]
    infer_instance
  let : Smooth U.X.hom :=
    RelativeRoot.smooth_of_isRepresentedBy_subgroup
      P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (2 • a.val) h2a.1 hq
  obtain ⟨x, hx, z, hz, hxz⟩ :=
    (L.mem_rootFiltrationSpan_iff_exists_scaled_mul y a r.property _).mp hg
  have h2aK : characterLattice.baseChange (algebraBaseMap F Fur) P.S
      (2 • a.val) ≠ 0 :=
    ((mem_roots_baseChange_iff (K := Fur) G P.S
      P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (2 • a.val)).mpr h2a).1
  have hzroot : z ∈ rootGroupPoints
      ((GroupScheme.baseChange (algebraBaseMap F Fur)).map P.i)
      (characterLattice.baseChange (algebraBaseMap F Fur) P.S (2 • a.val)) := by
    have hle := torusRestrictedRootDepthSubgroup_le_rootGroupPoints
      (P.isMaximalSplitTorus.isSplitSubtorus.1.baseChange (algebraBaseMap F Fur))
      t.isMaximalSplitTorus.isSplitSubtorus.1
      (L.apartment.isRootDatumValuation_of_mem (L.e y).mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F Fur)).map t.f)
      (characterLattice.baseChange (algebraBaseMap F Fur) P.S (2 • a.val)) h2aK r
    rw [fieldFactorization (t := t)] at hle
    exact hle hz
  have hqK := hq.baseChange (algebraBaseMap F Fur)
  rw [← RelativeRoot.subgroup_baseChange (algebraBaseMap F Fur) P.i (2 • a.val)] at hqK
  change z ∈ (RelativeRoot.subgroup
    ((GroupScheme.baseChange (algebraBaseMap F Fur)).map P.i)
    (characterLattice.baseChange (algebraBaseMap F Fur) P.S (2 • a.val))).carrier
      (Over.mk (𝟙 _)) at hzroot
  rw [← hqK.2] at hzroot
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hzroot
  have hwmap : rationalPoints.map
      ((GroupScheme.baseChange (algebraBaseMap F Fur)).map q) w = z := hw
  have hinter : M.IsRationalIntersectionModel q
      (L.scaledRootDepth y (2 • a.val) r) (L.scaledRootDepth y a r) := by
    intro v
    have hi : L.scaledRootDepth y (2 • a.val) r ⊓ L.scaledRootDepth y a r =
        L.scaledRootDepth y (2 • a.val) (2 * (r : ℝ)) :=
      (inf_comm _ _).trans (L.scaledRootDepth_inf_double y a r.property)
    exact (hmodel v).trans ((SetLike.ext_iff.mp hi) _).symm
  obtain ⟨v, u, hgu, hv, hu⟩ :=
    M.exists_rational_right_factorization_of_rationalIntersectionModel hM hconn q
      (L.scaledRootDepth y (2 • a.val) r) (L.scaledRootDepth y a r) hinter
      (fun σ v hv => L.rationalConjugate_mem_scaledRootDepth y (2 • a.val) r σ v hv)
      (fun σ v hv => L.rationalConjugate_mem_scaledRootDepth y a r σ v hv)
      g w x (by rwa [hwmap]) hx (by rw [hwmap]; exact hxz.symm)
  have hvF : v ∈ P.filtration y a r := by
    rw [L.filtration_eq_restrictedDepth y a r]
    exact hv
  have huF : rationalPoints.map q u ∈ P.filtration y (2 • a.val) r := by
    rw [L.filtration_eq_restrictedDepth y ⟨2 • a.val, h2a⟩ r]
    exact hu
  apply P.apartment.mem_filtrationBlock.mpr
  refine ⟨v, hvF, rationalPoints.map q u, ?_, hgu.symm⟩
  rw [P.apartment.doubleFiltration_of_mem y a.val r h2a]
  exact huF

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
