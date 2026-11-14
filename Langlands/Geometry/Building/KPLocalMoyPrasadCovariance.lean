import Langlands.Geometry.Building.KPLocalMoyPrasadGroupProperties
import Langlands.Geometry.Building.KPLocalMoyPrasadBlockExchange
import Langlands.Geometry.Building.ChamberPositiveCollection
import Langlands.Geometry.Building.UnramifiedStabilizerDescent

/-! # Covariance reductions for the K-level Moy–Prasad groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal commutatorElement TensorProduct
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

local instance : MulAction (normalizerPoints B.i) B.Apartment :=
  inferInstanceAs (MulAction (normalizerPoints B.i) B.apartment.Apartment)

local instance : MulAction (rationalPoints H) B.ReducedBuilding :=
  inferInstanceAs (MulAction (rationalPoints H) B.apartment.ReducedBuilding)

/-- The root-generator conjugation input for normality of the local Moy–Prasad groups.
This predicate names a bound; its definition does not assert that the bound holds. -/
def RootFiltrationConjugationBound : Prop :=
  ∀ (x : B.Apartment) (r : ℝ≥0) (a b : relativeRoots B.i)
    (u v : rationalPoints H), u ∈ B.filtration x a 0 → v ∈ B.filtration x b r →
      u * v * u⁻¹ ∈ B.moyPrasad hZ x r

/-- The root-generated point fixer is contained in the zero Moy–Prasad group. -/
theorem sharpFixer_le_moyPrasad_zero (x : B.Apartment) :
    B.sharpFixer {x} ≤ B.moyPrasad hZ x 0 := by
  change B.apartment.sharpFixer {x} ≤ B.moyPrasad hZ x 0
  rw [← B.apartment.sharpFiltration_zero x]
  exact B.sharpFiltration_le_moyPrasad hZ x 0

/-- The two factors of a root block are generators of the same-depth group. -/
theorem block_subset_moyPrasad (x : B.Apartment) (r : ℝ≥0)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆ B.moyPrasad hZ x r := by
  rintro g ⟨v, hv, w, hw, rfl⟩
  refine (B.moyPrasad hZ x r).mul_mem
    (B.filtration_le_moyPrasad hZ x ⟨a, ha⟩ r hv) ?_
  by_cases h2a : 2 • a ∈ relativeRoots B.i
  · rw [B.apartment.doubleFiltration_of_mem x a r h2a] at hw
    exact B.filtration_le_moyPrasad hZ x ⟨2 • a, h2a⟩ r hw
  · rw [B.apartment.doubleFiltration_of_not_mem x a r h2a] at hw
    rw [Subgroup.mem_bot.mp hw]
    exact Subgroup.one_mem _

/-- V3 handles conjugation of nonopposite directions by a depth-zero root element. -/
theorem conjugate_root_mem_moyPrasad_of_nonopposite
    (x : B.Apartment) {a b : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) (hb : b ∈ relativeRoots B.i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : RealTorusSpace.Vstar B.S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a))
    (r : ℝ≥0) {u v : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x b r) :
    u * v * u⁻¹ ∈ B.moyPrasad hZ x r := by
  have hcomm : ⁅B.filtration x a 0, B.filtration x b r⁆ ≤ B.moyPrasad hZ x r := by
    refine (B.apartment.filtration_commutator_le x ha hb hnon 0 r).trans ?_
    refine iSup_le fun p => iSup_le fun q => iSup_le fun hp => iSup_le fun hq =>
      iSup_le fun hroot => ?_
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hdepth : (r : ℝ) ≤ (p : ℝ) * 0 + (q : ℝ) * r := by
      simpa only [mul_zero, zero_add, one_mul] using
        mul_le_mul_of_nonneg_right hq1 r.coe_nonneg
    exact (B.apartment.filtration_antitone x _ hdepth).trans
      (B.filtration_le_moyPrasad hZ x ⟨p • a + q • b, hroot⟩ r)
  have heq : u * v * u⁻¹ = ⁅u, v⁆ * v := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact (B.moyPrasad hZ x r).mul_mem
    (hcomm (Subgroup.commutator_mem_commutator hu hv))
    (B.filtration_le_moyPrasad hZ x ⟨b, hb⟩ r hv)

/-- Root compatibility handles conjugation of the torus term by root elements. -/
theorem conjugate_image_mem_moyPrasad
    (hZr : ∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
      ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
        z * u * z⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : ℝ≥0) {u z : rationalPoints H}
    (hu : u ∈ B.filtration x a 0) (hz : z ∈ B.centralizerTorusImage hZ r) :
    u * z * u⁻¹ ∈ B.moyPrasad hZ x r := by
  have h := hZr x ⟨a, ha⟩ r 0 z⁻¹ ((B.centralizerTorusImage hZ r).inv_mem hz) u hu
  rw [add_zero, inv_inv] at h
  have heq : u * z * u⁻¹ = z * (z⁻¹ * u * z * u⁻¹) := by group
  rw [heq]
  exact (B.moyPrasad hZ x r).mul_mem
    (B.centralizerTorusImage_le_moyPrasad hZ x r hz)
    (B.block_subset_moyPrasad hZ x r ha h)

set_option maxHeartbeats 800000 in
/-- Root compatibility and root conjugation imply normalization by the sharp fixer. -/
theorem sharpFixer_le_normalizer_moyPrasad_of_root_conjugation
    (hZr : ∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
      ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
        z * u * z⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1)
    (x : B.Apartment) (r : ℝ≥0)
    (hroot : ∀ (a b : relativeRoots B.i) (u v : rationalPoints H),
      u ∈ B.filtration x a 0 → v ∈ B.filtration x b r →
        u * v * u⁻¹ ∈ B.moyPrasad hZ x r) :
    B.sharpFixer {x} ≤ Subgroup.normalizer (B.moyPrasad hZ x r : Set (rationalPoints H)) := by
  change B.apartment.sharpFixer {x} ≤ _
  refine iSup_le fun a => ?_
  rw [B.apartment.rootFixer_singleton]
  apply Subgroup.le_normalizer_iff.mpr
  intro u hu g hg
  have hle : B.moyPrasad hZ x r ≤ (B.moyPrasad hZ x r).comap
      (MulAut.conj u).toMonoidHom := by
    conv_lhs => rw [B.moyPrasad_eq_sup_iSup]
    refine sup_le ?_ (iSup_le fun b v hv => ?_)
    · intro z hz
      change u * z * u⁻¹ ∈ B.moyPrasad hZ x r
      exact B.conjugate_image_mem_moyPrasad hZ hZr x a.2 r hu hz
    · change u * v * u⁻¹ ∈ B.moyPrasad hZ x r
      exact hroot a b u v hu hv
  exact hle hg

/-- The torus-depth image normalizes the whole same-point Moy–Prasad group. -/
theorem torusImage_normalizes_moyPrasad (x : B.Apartment) (r s : ℝ≥0) :
    B.centralizerTorusImage hZ r ≤
      Subgroup.normalizer (B.moyPrasad hZ x s : Set (rationalPoints H)) := by
  rw [B.moyPrasad_eq_sup_iSup]
  refine (le_inf ?_ ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  · apply Subgroup.le_normalizer_iff.mpr
    intro z hz t ht
    have hcomm : Commute z t := by
      obtain ⟨z, _, rfl⟩ := hz
      obtain ⟨t, _, rfl⟩ := ht
      let := hZ.isCommMonObj
      exact (Commute.all z t).map (rationalPoints.map B.centralizer.j)
    simpa only [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one] using ht
  · exact (le_iInf fun a : relativeRoots B.i =>
      B.image_le_normalizer_filtration hZ x r a s).trans
      (Subgroup.iInf_normalizer_le_normalizer_iSup _)

/-- Once root conjugation is controlled, all generators give full normality. -/
theorem localMoyPrasadNormality_of_root_conjugation
    (hZr : ∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
      ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
        z * u * z⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1)
    (hroot : B.RootFiltrationConjugationBound hZ) :
    LocalMoyPrasadNormality B hZ := by
  intro x r
  rw [B.moyPrasad_eq_sup]
  refine sup_le (B.torusImage_normalizes_moyPrasad hZ x 0 r) ?_
  change B.apartment.sharpFiltration x (fun _ => (0 : ℝ)) ≤ _
  rw [B.apartment.sharpFiltration_zero]
  exact B.sharpFixer_le_normalizer_moyPrasad_of_root_conjugation hZ hZr x r (hroot x r)

/-- Normalizer stability of the torus term suffices for conjugation covariance. -/
theorem conj_mem_moyPrasad_normalizer
    (hZn : ∀ (n : normalizerPoints B.i) (r : ℝ≥0),
      (B.centralizerTorusImage hZ r).map
          (MulAut.conj (n : rationalPoints H)).toMonoidHom =
        B.centralizerTorusImage hZ r)
    (x : B.Apartment) (r : ℝ≥0) (n : normalizerPoints B.i)
    {g : rationalPoints H} (hg : g ∈ B.moyPrasad hZ x r) :
    (n : rationalPoints H) * g * (n : rationalPoints H)⁻¹ ∈
      B.moyPrasad hZ (n • x) r := by
  have hle : B.moyPrasad hZ x r ≤ (B.moyPrasad hZ (n • x) r).comap
      (MulAut.conj (n : rationalPoints H)).toMonoidHom := by
    rw [B.moyPrasad_eq_sup_iSup]
    refine sup_le ?_ (iSup_le fun a => ?_)
    · apply (Subgroup.map_le_iff_le_comap).mp
      rw [hZn n r]
      exact B.centralizerTorusImage_le_moyPrasad hZ (n • x) r
    · intro u hu
      exact B.filtration_le_moyPrasad hZ (n • x)
        ⟨weylAction B.i n a, weylAction_mapsTo_relativeRoots B.i n a.2⟩ r
        (B.apartment.conj_mem_filtration n hu)
  exact hle hg

/-- Conjugation by an apartment normalizer is an equality at unchanged depth. -/
theorem moyPrasad_map_conj_normalizer
    (hZn : ∀ (n : normalizerPoints B.i) (r : ℝ≥0),
      (B.centralizerTorusImage hZ r).map
          (MulAut.conj (n : rationalPoints H)).toMonoidHom =
        B.centralizerTorusImage hZ r)
    (x : B.Apartment) (r : ℝ≥0) (n : normalizerPoints B.i) :
    (B.moyPrasad hZ x r).map (MulAut.conj (n : rationalPoints H)).toMonoidHom =
      B.moyPrasad hZ (n • x) r := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact B.conj_mem_moyPrasad_normalizer hZ hZn x r n hg
  · intro g hg
    refine ⟨(n : rationalPoints H)⁻¹ * g * (n : rationalPoints H), ?_, ?_⟩
    · have h := B.conj_mem_moyPrasad_normalizer hZ hZn (n • x) r n⁻¹ hg
      rwa [Subgroup.coe_inv, inv_inv, inv_smul_smul] at h
    · change (n : rationalPoints H) *
        ((n : rationalPoints H)⁻¹ * g * (n : rationalPoints H)) *
          (n : rationalPoints H)⁻¹ = g
      group

set_option maxHeartbeats 800000 in
/-- Building equivariance follows from normality and apartment normalizer covariance. -/
theorem localMoyPrasadEquivariance_of_normality
    (hnorm : LocalMoyPrasadNormality B hZ)
    (hZn : ∀ (n : normalizerPoints B.i) (r : ℝ≥0),
      (B.centralizerTorusImage hZ r).map
          (MulAut.conj (n : rationalPoints H)).toMonoidHom =
        B.centralizerTorusImage hZ r) :
    LocalMoyPrasadEquivariance B hZ := by
  refine ⟨?_, fun n x r => B.moyPrasad_map_conj_normalizer hZ hZn x r n⟩
  intro g x x' hx r
  change ApartmentQuotient.apartment B.apartment.sharpFixerFamily x' =
    g • ApartmentQuotient.apartment B.apartment.sharpFixerFamily x at hx
  have hquot : ApartmentQuotient.mk B.apartment.sharpFixerFamily (g, x) =
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, x') := by
    simpa only [ApartmentQuotient.mk_eq_smul_apartment, one_smul] using hx.symm
  obtain ⟨n, hn, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily g 1 x x').1 hquot
  change g⁻¹ * 1 * (n : rationalPoints H) ∈ B.apartment.sharpFixer {x} at hp
  have hp0 : g⁻¹ * (n : rationalPoints H) ∈ B.moyPrasad hZ x 0 :=
    B.sharpFixer_le_moyPrasad_zero hZ x
      (by change g⁻¹ * (n : rationalPoints H) ∈ B.apartment.sharpFixer {x}
          simpa only [mul_one] using hp)
  have hpinv := (B.moyPrasad hZ x 0).inv_mem hp0
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm x r hpinv)
  change (B.moyPrasad hZ x r).map
      (MulAut.conj (g⁻¹ * (n : rationalPoints H))⁻¹).toMonoidHom =
        B.moyPrasad hZ x r at hmap
  have hcomp : (MulAut.conj g).toMonoidHom =
      (MulAut.conj (n : rationalPoints H)).toMonoidHom.comp
        (MulAut.conj (g⁻¹ * (n : rationalPoints H))⁻¹).toMonoidHom := by
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hcomp, ← Subgroup.map_map, hmap, B.moyPrasad_map_conj_normalizer hZ hZn, hn]

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
