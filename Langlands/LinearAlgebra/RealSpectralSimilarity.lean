import Langlands.LinearAlgebra.GeneralizedEigenspaceRank
import Langlands.LinearAlgebra.MatrixSpectralRank
import Langlands.LinearAlgebra.RealSpectralInterpolation
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Similarity after small real semisimple shifts -/

noncomputable section

open Matrix Polynomial Module Filter
open scoped Topology

set_option autoImplicit false

namespace Langlands

variable {n : ℕ}

local notation "RMat" => Matrix (Fin n) (Fin n) ℝ
local notation "CMat" => Matrix (Fin n) (Fin n) ℂ
local notation "Vec" => (Fin n → ℂ)

private theorem shiftedMatrixRank_eq_finrank (A : CMat) (z : ℂ) (k : ℕ) :
    shiftedMatrixRank A z k = Module.finrank ℂ
      (LinearMap.range ((Matrix.toLinAlgEquiv' A - z • (1 : End ℂ Vec)) ^ k)) := by
  let L : CMat ≃ₐ[ℂ] End ℂ Vec := Matrix.toLinAlgEquiv'
  change Module.finrank ℂ (LinearMap.range (L ((A - z • 1) ^ k))) = _
  rw [map_pow, map_sub, map_smul, map_one]

private theorem mem_realMatrixSpectralRoots_iff (A : RMat) (z : ℂ) :
    z ∈ realMatrixSpectralRoots A ↔
      Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (realMatrixComplexification n A)) z := by
  let B := realMatrixComplexification n A
  change z ∈ matrixSpectralRoots B ↔ Module.End.HasEigenvalue B.mulVecLin z
  rw [mem_matrixSpectralRoots, Polynomial.mem_roots B.charpoly_monic.ne_zero,
    Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin]

/-- For a conjugation-compatible root matching preserving multiplicities and shifted ranks,
adding the interpolated semisimple displacement to the first matrix makes it similar to the second. -/
theorem exists_realUnitIntertwiner_realMatrixSpectralShift (A B : RMat)
    (e : realMatrixSpectralRoots A ≃ realMatrixSpectralRoots B)
    (hstar : ∀ z, e (realMatrixSpectralRootStar A z) = realMatrixSpectralRootStar B (e z))
    (hm : ∀ z, (realMatrixComplexification n B).charpoly.roots.count (e z : ℂ) =
      (realMatrixComplexification n A).charpoly.roots.count (z : ℂ))
    (hr : ∀ (z : realMatrixSpectralRoots A) (k : Fin (n + 1)),
      shiftedMatrixRank (realMatrixComplexification n B) (e z) k =
        shiftedMatrixRank (realMatrixComplexification n A) z k) :
    ∃ u : RMatˣ, (u : RMat) * (A + realMatrixSpectralShift A (fun z => (e z : ℂ) - (z : ℂ))) =
      B * (u : RMat) := by
  classical
  let L : CMat ≃ₐ[ℂ] End ℂ Vec := Matrix.toLinAlgEquiv'
  let f := L (realMatrixComplexification n A)
  let g := L (realMatrixComplexification n B)
  let U (z : realMatrixSpectralRoots A) := f.maxGenEigenspace (z : ℂ)
  let W (z : realMatrixSpectralRoots B) := g.maxGenEigenspace (z : ℂ)
  have hU : DirectSum.IsInternal U :=
    isInternal_finset_maxGenEigenspace f _ (mem_realMatrixSpectralRoots_iff A)
  have hW : DirectSum.IsInternal W :=
    isInternal_finset_maxGenEigenspace g _ (mem_realMatrixSpectralRoots_iff B)
  have hWe : DirectSum.IsInternal (fun z => W (e z)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (hW.submodule_iSupIndep.comp e.injective) (by
        rw [e.surjective.iSup_comp W]
        exact hW.submodule_iSup_eq_top)
  have hmatch (z : realMatrixSpectralRoots A) :
      ∃ E : U z ≃ₗ[ℂ] W (e z), ∀ v,
        E (generalizedEigenNilpotent f (z : ℂ) v) = generalizedEigenNilpotent g (e z : ℂ) (E v) := by
    apply exists_generalizedEigenNilpotent_equiv f g (z : ℂ) (e z : ℂ) rfl
    · have hfm : f.charpoly = (realMatrixComplexification n A).charpoly := Matrix.charpoly_mulVecLin _
      have hgm : g.charpoly = (realMatrixComplexification n B).charpoly := Matrix.charpoly_mulVecLin _
      rw [hfm, hgm, ← Polynomial.count_roots, ← Polynomial.count_roots]
      exact (hm z).symm
    · intro k hk
      have hk' : k ≤ n := by simpa only [Module.finrank_fin_fun] using hk
      exact (shiftedMatrixRank_eq_finrank _ _ _).symm.trans
        ((hr z ⟨k, Nat.lt_succ_of_le hk'⟩).symm.trans (shiftedMatrixRank_eq_finrank _ _ _))
  choose E hE using hmatch
  let d (z : realMatrixSpectralRoots A) := (e z : ℂ) - (z : ℂ)
  let Z := realMatrixSpectralShift A d
  have hd (z : realMatrixSpectralRoots A) : d (realMatrixSpectralRootStar A z) = star (d z) := by
    simp only [d, hstar, coe_realMatrixSpectralRootStar, star_sub]
  let F := L (realMatrixComplexification n (A + Z))
  have hF (v : Vec) : F v = f v + L (realMatrixComplexification n Z) v := by
    change L (realMatrixComplexification n (A + Z)) v = _
    rw [map_add, map_add, LinearMap.add_apply]
  have hZ (z : realMatrixSpectralRoots A) (v : Vec) (hv : v ∈ U z) :
      L (realMatrixComplexification n Z) v = d z • v := realMatrixSpectralShift_apply A d hd z v hv
  have hFU (z : realMatrixSpectralRoots A) : Set.MapsTo F (U z) (U z) := by
    intro v hv
    rw [hF, hZ z v hv]
    exact (U z).add_mem (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) z hv) ((U z).smul_mem _ hv)
  have hFval (z : realMatrixSpectralRoots A) (v : U z) :
      F v = (generalizedEigenNilpotent f (z : ℂ) v : Vec) + (e z : ℂ) • (v : Vec) := by
    rw [hF, hZ z _ v.property, coe_generalizedEigenNilpotent_apply]
    simp only [d, sub_smul]
    abel
  have hEW (z : realMatrixSpectralRoots A) (v : U z) :
      (E z ⟨F v, hFU z v.property⟩ : Vec) = g (E z v : Vec) := by
    have hval : (⟨F v, hFU z v.property⟩ : U z) =
        generalizedEigenNilpotent f (z : ℂ) v + (e z : ℂ) • v := Subtype.ext (hFval z v)
    rw [hval, map_add, map_smul, hE]
    change (generalizedEigenNilpotent g (e z : ℂ) (E z v) : Vec) +
      (e z : ℂ) • (E z v : Vec) = g (E z v : Vec)
    rw [coe_generalizedEigenNilpotent_apply, sub_add_cancel]
  obtain ⟨G, _, hG⟩ := exists_intertwiningLinearEquiv_of_internal U (fun z => W (e z))
    hU hWe F g E hFU hEW
  let u : CMatˣ :=
    { val := L.symm G.toLinearMap
      inv := L.symm G.symm.toLinearMap
      val_inv := L.injective (by rw [map_mul, map_one, L.apply_symm_apply, L.apply_symm_apply]
                                 apply LinearMap.ext
                                 intro v
                                 exact G.apply_symm_apply v)
      inv_val := L.injective (by rw [map_mul, map_one, L.apply_symm_apply, L.apply_symm_apply]
                                 apply LinearMap.ext
                                 intro v
                                 exact G.symm_apply_apply v) }
  have hu : (u : CMat) * realMatrixComplexification n (A + Z) =
      realMatrixComplexification n B * (u : CMat) := by
    apply L.injective
    change L (L.symm G.toLinearMap * realMatrixComplexification n (A + Z)) =
      L (realMatrixComplexification n B * L.symm G.toLinearMap)
    rw [map_mul, map_mul, L.apply_symm_apply]
    apply LinearMap.ext
    intro v
    exact hG v
  exact exists_realUnitIntertwiner_of_complex (A + Z) B u hu

/-- The invariant spectral label on real matrices is computed on the complexification. -/
def realMatrixSpectralRankLabel (A : RMat) : ℕ ×ₗ ℕ :=
  matrixSpectralRankLabel (realMatrixComplexification n A)

theorem isOpen_realMatrixSpectralRankLabel_gt (p : ℕ ×ₗ ℕ) :
    IsOpen {A : RMat | p < realMatrixSpectralRankLabel A} :=
  (isOpen_matrixSpectralRankLabel_gt (n := n) p).preimage (continuous_realMatrixComplexification n)

theorem realMatrixSpectralRankLabel_transpose (A : RMat) :
    realMatrixSpectralRankLabel Aᵀ = realMatrixSpectralRankLabel A := by
  rw [realMatrixSpectralRankLabel, realMatrixComplexification_transpose, matrixSpectralRankLabel_transpose]
  rfl

theorem realMatrixSpectralRankLabel_units_conj (u : RMatˣ) (A : RMat) :
    realMatrixSpectralRankLabel ((u : RMat) * A * (↑u⁻¹ : RMat)) =
      realMatrixSpectralRankLabel A := by
  let v := Units.map (realMatrixComplexification n).toMonoidHom u
  unfold realMatrixSpectralRankLabel
  rw [map_mul, map_mul]
  exact matrixSpectralRankLabel_units_conj v _

theorem realMatrixSpectralRankLabel_bounds (A : RMat) :
    (ofLex (realMatrixSpectralRankLabel A)).1 ≤ n ∧
      (ofLex (realMatrixSpectralRankLabel A)).2 ≤ n * ((n + 1) * n) :=
  ⟨card_matrixSpectralRoots_le _, matrixSpectralRankSum_le _⟩

/-- Every sufficiently nearby real matrix on the fixed-label locus is similar to a displacement
by an arbitrarily small element of the real semisimple polynomial algebra. -/
theorem eventually_exists_realSpectralShift_similar (A : RMat) {U : Set RMat} (hU : U ∈ 𝓝 0) :
    ∀ᶠ B in 𝓝 A, realMatrixSpectralRankLabel B = realMatrixSpectralRankLabel A →
      ∃ Z ∈ U, Z ∈ Algebra.adjoin ℝ {matrixSemisimplePart A} ∧
        ∃ u : RMatˣ, (u : RMat) * (A + Z) = B * (u : RMat) := by
  have hshift : (realMatrixSpectralShift A) ⁻¹' U ∈ 𝓝 (0 : realMatrixSpectralRoots A → ℂ) :=
    (continuous_realMatrixSpectralShift A).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hshift
  obtain ⟨r, hr, hre, hsep, _⟩ := exists_eventually_matrixSpectralClusters
    (realMatrixComplexification n A) hε
  have hmatch := (continuous_realMatrixComplexification n).continuousAt.eventually
    (eventually_matrixSpectralRanks_eq_of_label_eq (realMatrixComplexification n A) hr)
  filter_upwards [hmatch] with B hB hlabel
  obtain ⟨e, he⟩ := hB hlabel
  let d (z : realMatrixSpectralRoots A) : ℂ := (e z : ℂ) - (z : ℂ)
  have hd : dist d 0 < ε := (dist_pi_lt_iff hε).mpr (fun z => by
    simpa only [d, Pi.zero_apply, dist_eq_norm, sub_zero] using (he z).1.trans_le hre)
  exact ⟨realMatrixSpectralShift A d, hball (Metric.mem_ball.mpr hd),
    realMatrixSpectralShift_mem_adjoin A d,
    exists_realUnitIntertwiner_realMatrixSpectralShift A B e
      (realMatrixSpectralMatch_star e hsep (fun z => (he z).1)) (fun z => (he z).2.1)
      (fun z => (he z).2.2)⟩

end Langlands
