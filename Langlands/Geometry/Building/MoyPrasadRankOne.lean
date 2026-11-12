import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.ChamberRankOne
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Rank-one depth exchange with the actual centralizer filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)
    (hZ : Zf.IsCommutatorFriendly) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r s : NNReal) (hpos : 0 < r + s)

include hZ ha hpos in
/-- The opposite-root factorization retains both root depths, and its
actual centralizer factor has depth at least their sum. -/
theorem exists_rankOne_depth_factorization
    {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a r) (hv : v ∈ P.filtration x (-a) s) :
    ∃ v' ∈ P.filtration x (-a) s,
      ∃ z ∈ Zf.filtration (r + s),
        ∃ u' ∈ P.filtration x a r,
          v' * rationalPoints.map P.centralizer.j z * u' = u * v := by
  by_cases hu1 : u = 1
  · subst u
    exact ⟨v, hv, 1, (Zf.filtration (r + s)).one_mem,
      1, (P.filtration x a r).one_mem, by simp⟩
  by_cases hv1 : v = 1
  · subst v
    exact ⟨1, (P.filtration x (-a) s).one_mem,
      1, (Zf.filtration (r + s)).one_mem, u, hu, by simp⟩
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hneg : -a ∈ relativeRoots P.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x ha
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hu.1 hu1
  obtain ⟨t', ht'⟩ := KPApartmentData.exists_val_eq_coe x hneg hv.1 hv1
  have hrt : (r : ℝ) ≤ t := by
    have h := hu.2
    rw [ht, WithTop.coe_le_coe] at h
    exact h
  have hst : (s : ℝ) ≤ t' := by
    have h := hv.2
    rw [ht', WithTop.coe_le_coe] at h
    exact h
  have hsum : 0 < t + t' := by
    have hpos' : 0 < (r : ℝ) + (s : ℝ) := by exact_mod_cast hpos
    linarith
  have hspan := relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  obtain ⟨v', hv', zG, hzG, u', hu', heq, hvt, hut, -⟩ :=
    P.apartment.exists_rankOne_factorization hT (hT.finite_relativeRoots P.i)
      hspan hrank x ha hneg hu.1 hu1 hv.1 hv1 ht ht' hsum
  let T : Over (Spec (CommRingCat.of F)) := Over.mk (𝟙 _)
  have hzG' : zG ∈ (torusCentralizer P.i).carrier T := by
    rwa [torusCentralizer_carrier_base]
  let z := (P.centralizer.isRepresentedBy.pointsEquiv T).symm ⟨zG, hzG'⟩
  have hz : rationalPoints.map P.centralizer.j z = zG :=
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp P.centralizer.isRepresentedBy _
  let depth : NNReal := ⟨t + t', hsum.le⟩
  have hdepth : 0 < depth := hsum
  have hvalue :
      (((depth : ℝ) : WithTop ℝ)) = x.val a u + x.val (-a) v := by
    rw [ht, ht', ← WithTop.coe_add]
    rfl
  have hcomm :
      v⁻¹ * u * v * u⁻¹ =
        (v⁻¹ * v') * rationalPoints.map P.centralizer.j z * (u' * u⁻¹) := by
    rw [hz]
    calc v⁻¹ * u * v * u⁻¹ = v⁻¹ * (u * v) * u⁻¹ := by group
      _ = v⁻¹ * (v' * zG * u') * u⁻¹ := by rw [heq]
      _ = (v⁻¹ * v') * zG * (u' * u⁻¹) := by group
  have hzdepth : z ∈ Zf.filtration depth :=
    hZ x ⟨a, ha⟩ u v hu.1 hu1 hv.1 hv1 depth hdepth hvalue
      (v⁻¹ * v') (u' * u⁻¹) z
      ((rootGroupPoints P.i (-a)).mul_mem ((rootGroupPoints P.i (-a)).inv_mem hv.1) hv')
      ((rootGroupPoints P.i a).mul_mem hu' ((rootGroupPoints P.i a).inv_mem hu.1)) hcomm
  have hrsdepth : r + s ≤ depth := by
    change (r + s : NNReal) ≤ ⟨t + t', hsum.le⟩
    apply NNReal.coe_le_coe.mp
    change (r : ℝ) + (s : ℝ) ≤ t + t'
    linarith
  refine ⟨v', ⟨hv', (WithTop.coe_le_coe.mpr hst).trans hvt⟩,
    z, Zf.antitone hrsdepth hzdepth,
    u', ⟨hu', (WithTop.coe_le_coe.mpr hrt).trans hut⟩, ?_⟩
  rw [hz]
  exact heq.symm

/-- Actual coordinates for exchanging two opposite root-depth elements;
the central coordinate is in the original filtration at the sum depth. -/
def rankOneMoyPrasadCoordinates
    (u : P.filtration x a r) (v : P.filtration x (-a) s) :
    {p : P.filtration x (-a) s × Zf.filtration (r + s) × P.filtration x a r //
      (p.1 : rationalPoints G) *
        rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        (p.2.2 : rationalPoints G) = (u : rationalPoints G) * (v : rationalPoints G)} := by
  apply Classical.choice
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    Zf.exists_rankOne_depth_factorization hZ x ha r s hpos u.property v.property
  exact ⟨⟨(⟨v', hv'⟩, ⟨z, hz⟩, ⟨u', hu'⟩), heq⟩⟩

include hZ ha hpos in
/-- The corresponding literal set-product exchange with its full actual
centralizer-filtration factor, retaining the two original root depths. -/
theorem filtration_mul_opposite_filtration_subset_depth :
    (P.filtration x a r : Set (rationalPoints G)) * P.filtration x (-a) s ⊆
      (P.filtration x (-a) s : Set (rationalPoints G)) *
        (Zf.image (r + s) : Set (rationalPoints G)) * P.filtration x a r := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    Zf.exists_rankOne_depth_factorization hZ x ha r s hpos hu hv
  change u * v ∈ _
  rw [← heq]
  exact Set.mul_mem_mul (Set.mul_mem_mul hv'
    (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)) hu'

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
