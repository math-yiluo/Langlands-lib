import Langlands.Geometry.Building.MoyPrasadRootConjugation

/-! # Normalizer covariance of the original Moy–Prasad subgroup family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise commutatorElement
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

/-- Conjugation by an actual normalizer point preserves the unchanged
depth at its translated apartment point. -/
theorem conj_mem_moyPrasad_normalizer (hZn : Zf.IsNormalizerStable)
    (x : P.Apartment) (r : NNReal) (n : normalizerPoints P.i)
    {g : rationalPoints G} (hg : g ∈ Zf.moyPrasad x r) :
    (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈
      Zf.moyPrasad (n • x) r := by
  have hle : Zf.moyPrasad x r ≤ (Zf.moyPrasad (n • x) r).comap
      (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
    rw [moyPrasad, P.apartment.sharpFiltration_eq_iSup]
    refine sup_le ?_ (iSup_le fun a => ?_)
    · apply (Subgroup.map_le_iff_le_comap).mp
      rw [hZn n n.property r]
      exact Zf.image_le_moyPrasad (n • x) r
    · intro u hu
      exact Zf.filtration_le_moyPrasad (n • x)
        ⟨weylAction P.i n a, weylAction_mapsTo_relativeRoots P.i n a.2⟩ r
        (P.apartment.conj_mem_filtration n hu)
  exact hle hg

/-- The actual original subgroup family is covariant under the actual
normalizer action on the apartment. -/
def moyPrasadNormalizerFamily (hZn : Zf.IsNormalizerStable) (r : NNReal) :
    CovariantSubgroupFamily (normalizerPoints P.i) P.Apartment where
  toFun x := Zf.moyPrasad x r
  isConjCovariant n x _g hg := Zf.conj_mem_moyPrasad_normalizer hZn x r n hg

/-- Normalizer conjugation is an exact equality on the original subgroups. -/
theorem moyPrasad_map_conj_normalizer (hZn : Zf.IsNormalizerStable)
    (x : P.Apartment) (r : NNReal) (n : normalizerPoints P.i) :
    (Zf.moyPrasad x r).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      Zf.moyPrasad (n • x) r := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact Zf.conj_mem_moyPrasad_normalizer hZn x r n hg
  · intro g hg
    refine ⟨(n : rationalPoints G)⁻¹ * g * (n : rationalPoints G), ?_, ?_⟩
    · change (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∈ Zf.moyPrasad x r
      have h := Zf.conj_mem_moyPrasad_normalizer hZn (n • x) r n⁻¹ hg
      rwa [Subgroup.coe_inv, inv_inv, inv_smul_smul] at h
    · change (n : rationalPoints G) *
        ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G)) *
          (n : rationalPoints G)⁻¹ = g
      group

/-- The actual normalizer conjugation as a multiplicative equivalence
between the unchanged original Moy–Prasad subgroups. -/
def moyPrasadNormalizerEquiv (hZn : Zf.IsNormalizerStable)
    (x : P.Apartment) (r : NNReal) (n : normalizerPoints P.i) :
    Zf.moyPrasad x r ≃* Zf.moyPrasad (n • x) r :=
  ((MulAut.conj (n : rationalPoints G)).subgroupMap (Zf.moyPrasad x r)).trans
    (MulEquiv.subgroupCongr (Zf.moyPrasad_map_conj_normalizer hZn x r n))

/-- V3 gives the original prescribed depth for nonopposite root directions
when the conjugating root element has depth zero. -/
theorem conjugate_root_mem_moyPrasad_of_nonopposite
    (x : P.Apartment) {a b : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) (hb : b ∈ relativeRoots P.i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : RealTorusSpace.Vstar P.S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a))
    (r : NNReal) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x b r) :
    u * v * u⁻¹ ∈ Zf.moyPrasad x r := by
  have hcomm : ⁅P.filtration x a 0, P.filtration x b r⁆ ≤ Zf.moyPrasad x r := by
    refine (P.apartment.filtration_commutator_le x ha hb hnon 0 r).trans ?_
    refine iSup_le fun p => iSup_le fun q => iSup_le fun hp => iSup_le fun hq =>
      iSup_le fun hroot => ?_
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hdepth : (r : ℝ) ≤ (p : ℝ) * 0 + (q : ℝ) * r := by
      simpa only [mul_zero, zero_add, one_mul] using
        mul_le_mul_of_nonneg_right hq1 r.coe_nonneg
    exact (P.apartment.filtration_antitone x _ hdepth).trans
      (Zf.filtration_le_moyPrasad x ⟨p • a + q • b, hroot⟩ r)
  have heq : u * v * u⁻¹ = ⁅u, v⁆ * v := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact (Zf.moyPrasad x r).mul_mem
    (hcomm (Subgroup.commutator_mem_commutator hu hv))
    (Zf.filtration_le_moyPrasad x ⟨b, hb⟩ r hv)

/-- Root compatibility controls conjugation of the original middle
coordinate by a depth-zero root element. -/
theorem conjugate_image_mem_moyPrasad (hZr : Zf.IsRootCompatible)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) {u z : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hz : z ∈ Zf.image r) :
    u * z * u⁻¹ ∈ Zf.moyPrasad x r := by
  have h := hZr x ⟨a, ha⟩ r 0 z⁻¹ ((Zf.image r).inv_mem hz) u hu
  rw [add_zero, inv_inv] at h
  have heq : u * z * u⁻¹ = z * (z⁻¹ * u * z * u⁻¹) := by group
  rw [heq]
  exact (Zf.moyPrasad x r).mul_mem (Zf.image_le_moyPrasad x r hz)
    (Zf.block_subset_moyPrasad x r ha h)

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
