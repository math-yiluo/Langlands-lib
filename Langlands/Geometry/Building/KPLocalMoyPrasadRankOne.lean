import Langlands.Geometry.Building.IntegerMoyPrasadBlockSubgroups
import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer

/-! # Positive-depth rank-one exchange over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise NNReal
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
    (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The commutator clause of KP Lemma 7.2.3 for the actual torus filtration.
This internal predicate is precisely the first clause of S1 at `B` and `hZ`. -/
def LocalTorusCommutatorFriendly : Prop :=
  ∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
    u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
    ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
    ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
      v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
      u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
      z ∈ B.centralizerTorusFiltration hZ r

/-- The opposite-root factorization retains both root depths, and its
actual centralizer factor has depth at least their sum. -/
theorem exists_rankOne_depth_factorization
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r s : NNReal) (hpos : 0 < r + s)
    {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a r) (hv : v ∈ B.filtration x (-a) s) :
    ∃ v' ∈ B.filtration x (-a) s,
      ∃ z ∈ B.centralizerTorusFiltration hZ (r + s),
        ∃ u' ∈ B.filtration x a r,
          v' * rationalPoints.map B.centralizer.j z * u' = u * v := by
  by_cases hu1 : u = 1
  · subst u
    exact ⟨v, hv, 1, (B.centralizerTorusFiltration hZ (r + s)).one_mem,
      1, (B.filtration x a r).one_mem, by simp⟩
  by_cases hv1 : v = 1
  · subst v
    exact ⟨1, (B.filtration x (-a) s).one_mem,
      1, (B.centralizerTorusFiltration hZ (r + s)).one_mem, u, hu, by simp⟩
  let : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus
  have hneg : -a ∈ relativeRoots B.i :=
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
  have hspan := relativeRootsRestrictedCharactersSpan (UnramifiedClosure F) H B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus
  obtain ⟨v', hv', zG, hzG, u', hu', heq, hvt, hut, -⟩ :=
    B.apartment.exists_rankOne_factorization hT (hT.finite_relativeRoots B.i)
      hspan hrank x ha hneg hu.1 hu1 hv.1 hv1 ht ht' hsum
  let T : Over (Spec (CommRingCat.of (UnramifiedClosure F))) := Over.mk (𝟙 _)
  have hzG' : zG ∈ (torusCentralizer B.i).carrier T := by
    rwa [torusCentralizer_carrier_base]
  let z := (B.centralizer.isRepresentedBy.pointsEquiv T).symm ⟨zG, hzG'⟩
  have hz : rationalPoints.map B.centralizer.j z = zG :=
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp B.centralizer.isRepresentedBy _
  let depth : NNReal := ⟨t + t', hsum.le⟩
  have hdepth : 0 < depth := hsum
  have hvalue :
      (((depth : ℝ) : WithTop ℝ)) = x.val a u + x.val (-a) v := by
    rw [ht, ht', ← WithTop.coe_add]
    rfl
  have hcomm :
      v⁻¹ * u * v * u⁻¹ =
        (v⁻¹ * v') * rationalPoints.map B.centralizer.j z * (u' * u⁻¹) := by
    rw [hz]
    calc v⁻¹ * u * v * u⁻¹ = v⁻¹ * (u * v) * u⁻¹ := by group
      _ = v⁻¹ * (v' * zG * u') * u⁻¹ := by rw [heq]
      _ = (v⁻¹ * v') * zG * (u' * u⁻¹) := by group
  have hzdepth : z ∈ B.centralizerTorusFiltration hZ depth :=
    hZcomm x ⟨a, ha⟩ u v hu.1 hu1 hv.1 hv1 depth hdepth hvalue
      (v⁻¹ * v') (u' * u⁻¹) z
      ((rootGroupPoints B.i (-a)).mul_mem ((rootGroupPoints B.i (-a)).inv_mem hv.1) hv')
      ((rootGroupPoints B.i a).mul_mem hu' ((rootGroupPoints B.i a).inv_mem hu.1)) hcomm
  have hrsdepth : r + s ≤ depth := by
    change (r + s : NNReal) ≤ ⟨t + t', hsum.le⟩
    apply NNReal.coe_le_coe.mp
    change (r : ℝ) + (s : ℝ) ≤ t + t'
    linarith
  refine ⟨v', ⟨hv', (WithTop.coe_le_coe.mpr hst).trans hvt⟩,
    z, B.centralizerTorusFiltration_antitone hZ hrsdepth hzdepth,
    u', ⟨hu', (WithTop.coe_le_coe.mpr hrt).trans hut⟩, ?_⟩
  rw [hz]
  exact heq.symm

/-- The corresponding literal set-product exchange with its full actual
centralizer-filtration factor, retaining the two original root depths. -/
theorem filtration_mul_opposite_filtration_subset_depth
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r s : NNReal) (hpos : 0 < r + s) :
    (B.filtration x a r : Set (rationalPoints H)) * B.filtration x (-a) s ⊆
      (B.filtration x (-a) s : Set (rationalPoints H)) *
        (B.centralizerTorusImage hZ (r + s) : Set (rationalPoints H)) * B.filtration x a r := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    B.exists_rankOne_depth_factorization hZ hZcomm x ha r s hpos hu hv
  change u * v ∈ _
  rw [← heq]
  exact Set.mul_mem_mul (Set.mul_mem_mul hv'
    (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)) hu'


/-- Exchange an original doubled-root element with an opposite ordinary
root element. The new positive coordinate stays in the original two-factor
block at the original doubled-root depth. -/
def doublePositiveMoyPrasadCoordinates
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) (h2a : 2 • a ∈ relativeRoots B.i)
    (r s : NNReal) (hpos : 0 < r / 2 + s)
    (u : B.filtration x (2 • a) r) (v : B.filtration x (-a) s) :
    {p : B.filtration x (-a) s × B.centralizerTorusFiltration hZ (r / 2 + s) ×
        B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints H) *
        rationalPoints.map B.centralizer.j (p.2.1 : rationalPoints B.centralizer.Z) *
        (p.2.2 : rationalPoints H) = (u : rationalPoints H) * (v : rationalPoints H)} := by
  apply Classical.choice
  have huBlock : (u : rationalPoints H) ∈
      B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    refine ⟨1, (B.filtration x a r).one_mem, u, ?_, one_mul _⟩
    rw [B.apartment.doubleFiltration_of_mem x a r h2a]
    exact u.property
  have hOneBlock : (1 : rationalPoints H) ∈
      B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    exact ⟨1, (B.filtration x a r).one_mem,
      1, (B.apartment.doubleFiltration x a r).one_mem, one_mul _⟩
  by_cases hu1 : (u : rationalPoints H) = 1
  · exact ⟨⟨(v, 1, ⟨1, hOneBlock⟩), by simp [hu1]⟩⟩
  by_cases hv1 : (v : rationalPoints H) = 1
  · exact ⟨⟨(1, 1, ⟨u, huBlock⟩), by simp [hv1]⟩⟩
  have huHalf : (u : rationalPoints H) ∈ B.filtration x a (r / 2 : NNReal) := by
    have h := B.apartment.filtration_double_le_half x ha h2a (r : ℝ) u.property
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    B.exists_rankOne_depth_factorization hZ hZcomm x ha (r / 2) s hpos huHalf v.property
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha huHalf.1 hu1
  have hneg : -a ∈ relativeRoots B.i := by
    let : Smooth H.X.hom := B.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  obtain ⟨t', ht'⟩ := KPApartmentData.exists_val_eq_coe x hneg v.property.1 hv1
  have hrt : (r : ℝ) / 2 ≤ t := by
    have h := huHalf.2
    rw [ht, WithTop.coe_le_coe] at h
    exact h
  have hst : (s : ℝ) ≤ t' := by
    have h := v.property.2
    rw [ht', WithTop.coe_le_coe] at h
    exact h
  have hsum : 0 < t + t' := by
    have hpos' : 0 < (r : ℝ) / 2 + (s : ℝ) := by exact_mod_cast hpos
    linarith
  have hdelta := B.rankOne_double_positive_difference (exists_order_eq_one F) x ha h2a u.property.1 hu1
    v.property.1 hv1 hv'.1
    (map_mem_centralizerPoints B.centralizer.isRepresentedBy z) hu'.1 heq.symm ht ht' hsum
  have hdeltaFil : u' * (u : rationalPoints H)⁻¹ ∈ B.filtration x a r := by
    refine ⟨(rootGroupPoints B.i a).mul_mem hu'.1
      ((rootGroupPoints B.i a).inv_mem huHalf.1), ?_⟩
    apply le_trans (WithTop.coe_le_coe.mpr ?_) hdelta
    linarith [s.coe_nonneg]
  have hu'Block : u' ∈ B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    refine ⟨u' * (u : rationalPoints H)⁻¹, hdeltaFil, u, ?_, inv_mul_cancel_right _ _⟩
    rw [B.apartment.doubleFiltration_of_mem x a r h2a]
    exact u.property
  exact ⟨⟨(⟨v', hv'⟩, ⟨z, hz⟩, ⟨u', hu'Block⟩), heq⟩⟩


end Langlands.Geometry.Building.MaximalUnramified.BuildingData
