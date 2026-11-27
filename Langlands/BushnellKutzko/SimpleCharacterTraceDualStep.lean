import Langlands.BushnellKutzko.TraceDualLatticeCalculus
import Langlands.BushnellKutzko.AdjointLatticeLifting
import Langlands.BushnellKutzko.RefinementCore
import Mathlib.Order.ModularLattice

/-! # Extending the simple-character trace dual away from the cutoff -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V

/-- If two parameters agree modulo the indicated ambient step, their adjoint
images of a deep submodule agree modulo the shifted step. -/
theorem adjointMap_image_sup_eq_of_sub_mem (L : LatticeChain O F V) (b c : A)
    {i j : ℤ} (hbc : b - c ∈ L.endFiltration i)
    (M : Submodule O A) (hM : M ≤ L.endFiltration j) :
    M.map (adjointMap O b) ⊔ L.endFiltration (i + j) =
      M.map (adjointMap O c) ⊔ L.endFiltration (i + j) := by
  have hle {b c : A} (hbc : b - c ∈ L.endFiltration i) :
      M.map (adjointMap O b) ⊔ L.endFiltration (i + j) ≤
        M.map (adjointMap O c) ⊔ L.endFiltration (i + j) := by
    apply sup_le ?_ le_sup_right
    rintro _ ⟨x, hx, rfl⟩
    have h : adjointMap O b x = adjointMap O c x + ((b - c) * x - x * (b - c)) := by
      change b * x - x * b = (c * x - x * c) + ((b - c) * x - x * (b - c))
      noncomm_ring
    rw [h]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hx)
      (commutator_mem_endFiltration L hbc (hM hx))
  refine le_antisymm (hle hbc) (hle ?_)
  rw [← neg_sub]
  exact neg_mem hbc

/-- Above the cutoff a shallow and a deep description differ by one
intersection with the ambient filtration. This identity holds for the
filtered layer of any ambient submodule. -/
theorem layer_eq_deep_inf_of_le (L : LatticeChain O F V) (M : Submodule O A) {i j : ℤ} (hij : i ≤ j) :
    M ⊓ L.endFiltration j = (M ⊓ L.endFiltration i) ⊓ L.endFiltration j := by
  rw [inf_assoc, inf_eq_right.mpr (L.endFiltration_antitone hij)]

/-- Below the cutoff, the relative lattice accounts for the additional
shallow part of a layer defined from a relative order and a deep lattice. -/
theorem layer_eq_relative_sup_deep_of_le (L : LatticeChain O F V) (b : A)
    (M : Submodule O A) {i j : ℤ} (hi : 0 ≤ i) (hij : i ≤ j) (hM : M ≤ L.endFiltration j) :
    (centralizerLattice L b 0 ⊔ M) ⊓ L.endFiltration i =
      centralizerLattice L b i ⊔ ((centralizerLattice L b 0 ⊔ M) ⊓ L.endFiltration j) := by
  have factor (k : ℤ) (hk : 0 ≤ k) (hm : M ≤ L.endFiltration k) :
      (centralizerLattice L b 0 ⊔ M) ⊓ L.endFiltration k = centralizerLattice L b k ⊔ M := by
    rw [sup_comm, sup_inf_assoc_of_le _ hm, sup_comm]
    congr 1
    ext x
    exact ⟨fun ⟨⟨_, ha⟩, hp⟩ => ⟨hp, ha⟩,
      fun ⟨hp, ha⟩ => ⟨⟨L.endFiltration_antitone hk hp, ha⟩, hp⟩⟩
  rw [factor i hi (hM.trans (L.endFiltration_antitone hij)), factor j (hi.trans hij) hM, ← sup_assoc]
  have hQ : centralizerLattice L b j ≤ centralizerLattice L b i :=
    fun _ h => ⟨L.endFiltration_antitone hij h.1, h.2⟩
  rw [sup_eq_left.mpr hQ]

/-- The adjoint image at the cutoff contains the part of the entire adjoint
range at the complementary depth. -/
theorem inf_adjointRange_le_image_of_mixed_le (L : LatticeChain O F V) [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (b : A) (j k : ℤ) (J : Submodule O A)
    (hInv : ∀ m : ℤ, (1 : A) ∈ centralizerLattice L b m * centralizerLattice L b (-m))
    (hCrit : ∀ i > k, i ∉ criticalIndexSet L b) (hJ : mixedAdjointLattice L b j k ≤ J) :
    L.endFiltration (j + k) ⊓ ((adjointMap F b).range.restrictScalars O) ≤ J.map (adjointMap O b) := by
  intro x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨y, hy, hyx⟩ := exists_mixedAdjointLattice_lift L b hInv hπ
    (L.exists_uniformizer_pow_mem_endFiltration hπ) hCrit hx.1 hx.2
  exact ⟨y, hJ hy, hyx⟩

/-- A modular-lattice calculation for the complementary depth below the
cutoff, after dualizing the relative and deep parts. -/
theorem traceDual_cutoff_descent {M N R J : Submodule O A}
    (hNM : N ≤ M) (hJR : J ≤ R) (hcover : M ⊓ R ≤ J) :
    (N ⊔ R) ⊓ (M ⊔ J) = N ⊔ J := by
  have hJN : J ≤ N ⊔ R := hJR.trans le_sup_right
  calc
    (N ⊔ R) ⊓ (M ⊔ J) = J ⊔ ((N ⊔ R) ⊓ M) := by
      rw [inf_comm, sup_comm M J, sup_inf_assoc_of_le _ hJN, inf_comm M]
    _ = J ⊔ (N ⊔ (R ⊓ M)) := by rw [sup_inf_assoc_of_le _ hNM]
    _ = N ⊔ J := by
      rw [← sup_assoc, sup_comm J N, sup_assoc, inf_comm R, sup_eq_left.mpr hcover]

/-- The cutoff identity extends to all character depths once the dual of
the relative step and the complementary adjoint lifting are available. -/
theorem traceDual_simpleHLayer_of_cutoff (L : LatticeChain O F V) (b : A) (n : ℤ) (tail : List A)
    (r m : ℕ) (D : Submodule O A → Submodule O A) (J W : Submodule O A)
    (hW : simpleHLattice L n b tail = centralizerLattice L b 0 ⊔ W)
    (hWdeep : W ≤ L.endFiltration ((r / 2 + 1 : ℕ) : ℤ))
    (hDsup : ∀ M N : Submodule O A, D (M ⊔ N) = D M ⊓ D N)
    (hDinf : D (simpleHLayer L n b tail (r / 2 + 1) ⊓ L.endFiltration (m + 1 : ℕ)) =
      D (simpleHLayer L n b tail (r / 2 + 1)) ⊔ D (L.endFiltration (m + 1 : ℕ)))
    (hDP : D (L.endFiltration (m + 1 : ℕ)) = L.endFiltration (-(m : ℤ)))
    (hDQ : D (centralizerLattice L b (m + 1 : ℕ)) =
      L.endFiltration (-(m : ℤ)) ⊔ ((adjointMap F b).range.restrictScalars O))
    (hcut : D (simpleHLayer L n b tail (r / 2 + 1)) =
      J.map (adjointMap O b) ⊔ L.endFiltration (-((r / 2 : ℕ) : ℤ)))
    (hcover : L.endFiltration (-((r / 2 : ℕ) : ℤ)) ⊓ ((adjointMap F b).range.restrictScalars O) ≤
      J.map (adjointMap O b)) :
    D (simpleHLayer L n b tail (m + 1)) = J.map (adjointMap O b) ⊔ L.endFiltration (-(m : ℤ)) := by
  rcases le_total (r / 2) m with h | h
  · have hs : simpleHLayer L n b tail (m + 1) =
        simpleHLayer L n b tail (r / 2 + 1) ⊓ L.endFiltration (m + 1 : ℕ) :=
      layer_eq_deep_inf_of_le L _ (by omega)
    rw [hs, hDinf, hcut, hDP, sup_assoc]
    rw [sup_eq_right.mpr (L.endFiltration_antitone (by omega))]
  · have hs : simpleHLayer L n b tail (m + 1) =
        centralizerLattice L b (m + 1 : ℕ) ⊔ simpleHLayer L n b tail (r / 2 + 1) := by
      unfold simpleHLayer
      rw [hW]
      exact layer_eq_relative_sup_deep_of_le L b W (by omega) (by omega) hWdeep
    have hJR : J.map (adjointMap O b) ≤ (adjointMap F b).range.restrictScalars O := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, rfl⟩
    rw [hs, hDsup, hDQ, hcut, sup_comm (J.map (adjointMap O b))]
    exact (traceDual_cutoff_descent (L.endFiltration_antitone (by omega)) hJR hcover).trans
      (sup_comm _ _)

end Langlands.BushnellKutzko
