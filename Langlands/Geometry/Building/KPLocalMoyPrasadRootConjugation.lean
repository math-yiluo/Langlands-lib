import Langlands.Geometry.Building.IntegerRootConjugation
import Langlands.Geometry.Building.KPLocalMoyPrasadRankOne
import Langlands.Geometry.Building.KPLocalMoyPrasadCovariance
import Langlands.Geometry.Building.KPQuasiSplitLocalTorusFiltrationStatement
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer

/-! # Actual torus-depth coordinates for K-level opposite conjugation -/

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

/-- Actual original coordinates for the conjugate of an opposite
positive-depth root element by a depth-zero root element. -/
def rootConjugationMoyPrasadCoordinates
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r)
    (u : B.filtration x a 0) (v : B.filtration x (-a) r) :
    {p : B.filtration x (-a) r × B.centralizerTorusFiltration hZ r ×
        B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints H) *
        rationalPoints.map B.centralizer.j (p.2.1 : rationalPoints B.centralizer.Z) *
        (p.2.2 : rationalPoints H) =
          (u : rationalPoints H) * (v : rationalPoints H) * (u : rationalPoints H)⁻¹} := by
  apply Classical.choice
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    B.exists_rankOne_depth_factorization hZ hZcomm x ha 0 r (by simpa only [zero_add] using hr)
      u.property v.property
  rw [zero_add] at hz
  have halt := B.conjugate_opposite_mem_root_centralizer_block (exists_order_eq_one F) x ha r hr u.property v.property
  obtain ⟨_, ⟨n, hn, c, hc, rfl⟩, q, hq, halt⟩ := halt
  have hcomp : v' * rationalPoints.map B.centralizer.j z *
      (u' * (u : rationalPoints H)⁻¹) = n * c * q := by
    rw [← mul_assoc, heq]
    exact halt.symm
  have hunique := B.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'.1⟩,
      ⟨rationalPoints.map B.centralizer.j z,
        map_mem_centralizerPoints B.centralizer.isRepresentedBy z⟩,
      ⟨u' * (u : rationalPoints H)⁻¹,
        (rootGroupPoints B.i a).mul_mem hu'.1 ((rootGroupPoints B.i a).inv_mem u.property.1)⟩))
    (a₂ := (⟨n, hn⟩, ⟨c, hc⟩,
      ⟨q, B.apartment.filtrationBlock_subset_rootGroupPoints x (fun _ => (r : ℝ)) a hq⟩))
    hcomp
  have hlast : u' * (u : rationalPoints H)⁻¹ = q :=
    congrArg (fun p : rootGroupPoints B.i (-a) × centralizerPoints B.i ×
      rootGroupPoints B.i a => (p.2.2 : rationalPoints H)) hunique
  refine ⟨⟨(⟨v', hv'⟩, ⟨z, hz⟩,
    ⟨u' * (u : rationalPoints H)⁻¹, hlast ▸ hq⟩), ?_⟩⟩
  change v' * rationalPoints.map B.centralizer.j z *
      (u' * (u : rationalPoints H)⁻¹) =
    (u : rationalPoints H) * (v : rationalPoints H) * (u : rationalPoints H)⁻¹
  rw [← mul_assoc, heq]

/-- Opposite-root conjugation preserves the original positive-depth
Moy–Prasad subgroup, including the required doubled-root factor. -/
theorem conjugate_opposite_mem_moyPrasad
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x (-a) r) :
    u * v * u⁻¹ ∈ B.moyPrasad hZ x r := by
  let p := B.rootConjugationMoyPrasadCoordinates hZ hZcomm x ha r hr ⟨u, hu⟩ ⟨v, hv⟩
  rw [← p.property]
  have hneg : -a ∈ relativeRoots B.i := by
    let : Smooth H.X.hom := B.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  exact (B.moyPrasad hZ x r).mul_mem ((B.moyPrasad hZ x r).mul_mem
    (B.filtration_le_moyPrasad hZ x ⟨-a, hneg⟩ r p.val.1.property)
    (B.centralizerTorusImage_le_moyPrasad hZ x r ⟨p.val.2.1, p.val.2.1.property, rfl⟩))
    (B.block_subset_moyPrasad hZ x r ha p.val.2.2.property)


end Langlands.Geometry.Building.MaximalUnramified.BuildingData
