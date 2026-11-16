import Langlands.Geometry.Building.IntegerMixedConjugation
import Langlands.Geometry.Building.KPLocalMoyPrasadRootConjugation

/-! # K-level mixed conjugation from its actual central estimate -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise NNReal
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
    (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- Mixed opposite conjugation has the original full-depth coordinates
once its actual middle coordinate has that depth. -/
def doubleOppositeConjugationCoordinatesOfCentralBound
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i) (r : NNReal) (hr : 0 < r)
    (u : B.filtration x a 0) (v : B.filtration x (-(2 • a)) r)
    (hcentral : ∀ (v' : rationalPoints H), v' ∈ rootGroupPoints B.i (-a) →
      ∀ (z : rationalPoints B.centralizer.Z) (u' : rationalPoints H),
      u' ∈ rootGroupPoints B.i a →
      v' * rationalPoints.map B.centralizer.j z * u' =
        (u : rationalPoints H) * (v : rationalPoints H) → z ∈ B.centralizerTorusFiltration hZ r) :
    {p : B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) ×
        B.centralizerTorusFiltration hZ r × B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints H) *
        rationalPoints.map B.centralizer.j (p.2.1 : rationalPoints B.centralizer.Z) *
        (p.2.2 : rationalPoints H) =
          (u : rationalPoints H) * (v : rationalPoints H) * (u : rationalPoints H)⁻¹} := by
  apply Classical.choice
  let : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hna : -a ∈ relativeRoots B.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  have h2na : 2 • (-a) ∈ relativeRoots B.i := by
    have hn := KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x h2a
    simpa only [smul_neg] using hn
  have hvHalf : (v : rationalPoints H) ∈ B.filtration x (-a) (r / 2 : NNReal) := by
    have h := B.apartment.filtration_double_le_half x hna h2na (r : ℝ)
      (by simpa only [smul_neg] using v.property)
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h
  obtain ⟨v', hv', z, -, u', hu', heq⟩ :=
    B.exists_rankOne_depth_factorization hZ hZcomm x ha 0 (r / 2)
      (by simpa only [zero_add] using div_pos hr (by norm_num : (0 : NNReal) < 2))
      u.property hvHalf
  have hz := hcentral v' hv'.1 z u' hu'.1 heq
  have hnegBlock := B.mul_double_opposite_mem_block_centralizer_root (exists_order_eq_one F) x ha h2a
    r hr u.property v.property
  obtain ⟨_, ⟨d, hd, c, hc, rfl⟩, w, hw, hnegEq⟩ := hnegBlock
  have huniqueNeg := B.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'.1⟩,
      ⟨rationalPoints.map B.centralizer.j z,
        map_mem_centralizerPoints B.centralizer.isRepresentedBy z⟩, ⟨u', hu'.1⟩))
    (a₂ := (⟨d, B.apartment.filtrationBlock_subset_rootGroupPoints x
      (fun _ => (r : ℝ)) (-a) hd⟩, ⟨c, hc⟩, ⟨w, hw⟩))
    (heq.trans hnegEq.symm)
  have hv'd : v' = d :=
    congrArg (fun p : rootGroupPoints B.i (-a) × centralizerPoints B.i ×
      rootGroupPoints B.i a => (p.1 : rationalPoints H)) huniqueNeg
  have hposBlock := B.conjugate_double_opposite_mem_root_centralizer_block (exists_order_eq_one F) x ha h2a
    r hr u.property v.property
  obtain ⟨_, ⟨n, hn, c', hc', rfl⟩, q, hq, hposEq⟩ := hposBlock
  have hcompare : v' * rationalPoints.map B.centralizer.j z *
      (u' * (u : rationalPoints H)⁻¹) = n * c' * q := by
    rw [← mul_assoc, heq]
    exact hposEq.symm
  have huniquePos := B.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'.1⟩,
      ⟨rationalPoints.map B.centralizer.j z,
        map_mem_centralizerPoints B.centralizer.isRepresentedBy z⟩,
      ⟨u' * (u : rationalPoints H)⁻¹,
        (rootGroupPoints B.i a).mul_mem hu'.1 ((rootGroupPoints B.i a).inv_mem u.property.1)⟩))
    (a₂ := (⟨n, hn⟩, ⟨c', hc'⟩,
      ⟨q, B.apartment.filtrationBlock_subset_rootGroupPoints x (fun _ => (r : ℝ)) a hq⟩))
    hcompare
  have hu'q : u' * (u : rationalPoints H)⁻¹ = q :=
    congrArg (fun p : rootGroupPoints B.i (-a) × centralizerPoints B.i ×
      rootGroupPoints B.i a => (p.2.2 : rationalPoints H)) huniquePos
  refine ⟨⟨(⟨v', hv'd ▸ hd⟩, ⟨z, hz⟩,
    ⟨u' * (u : rationalPoints H)⁻¹, hu'q ▸ hq⟩), ?_⟩⟩
  change v' * rationalPoints.map B.centralizer.j z * (u' * (u : rationalPoints H)⁻¹) =
    (u : rationalPoints H) * (v : rationalPoints H) * (u : rationalPoints H)⁻¹
  rw [← mul_assoc, heq]

/-- Only the actual middle-coordinate estimate remains for mixed
doubled-opposite conjugation in the original Moy–Prasad subgroup. -/
theorem conjugate_double_opposite_mem_moyPrasad_of_central_bound
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i) (r : NNReal) (hr : 0 < r)
    {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x (-(2 • a)) r)
    (hcentral : ∀ (v' : rationalPoints H), v' ∈ rootGroupPoints B.i (-a) →
      ∀ (z : rationalPoints B.centralizer.Z) (u' : rationalPoints H),
      u' ∈ rootGroupPoints B.i a →
      v' * rationalPoints.map B.centralizer.j z * u' = u * v → z ∈ B.centralizerTorusFiltration hZ r) :
    u * v * u⁻¹ ∈ B.moyPrasad hZ x r := by
  let p := B.doubleOppositeConjugationCoordinatesOfCentralBound hZ hZcomm x ha h2a r hr
    ⟨u, hu⟩ ⟨v, hv⟩ hcentral
  rw [← p.property]
  have hna : -a ∈ relativeRoots B.i := by
    let : Smooth H.X.hom := B.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  exact (B.moyPrasad hZ x r).mul_mem ((B.moyPrasad hZ x r).mul_mem
    (B.block_subset_moyPrasad hZ x r hna p.val.1.property)
    (B.centralizerTorusImage_le_moyPrasad hZ x r ⟨p.val.2.1, p.val.2.1.property, rfl⟩))
    (B.block_subset_moyPrasad hZ x r ha p.val.2.2.property)


end Langlands.Geometry.Building.MaximalUnramified.BuildingData
