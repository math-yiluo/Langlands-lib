import Langlands.LinearAlgebra.RangeIntertwinerExtension
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! # Similarity of matched generalized eigenspaces from shifted ranks -/

noncomputable section

open Module LinearMap
open scoped DirectSum

set_option autoImplicit false

namespace Langlands

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The nilpotent part of an endomorphism on a specified generalized eigenspace. -/
def generalizedEigenNilpotent (f : End K V) (a : K) : End K (f.maxGenEigenspace a) :=
  (f - a • 1).restrict (f.mapsTo_maxGenEigenspace_of_comm
    (Algebra.mul_sub_algebraMap_commutes f a) a)

@[simp]
theorem coe_generalizedEigenNilpotent_apply (f : End K V) (a : K) (v : f.maxGenEigenspace a) :
    (generalizedEigenNilpotent f a v : V) = f v - a • (v : V) := rfl

theorem isNilpotent_generalizedEigenNilpotent [FiniteDimensional K V] (f : End K V) (a : K) :
    IsNilpotent (generalizedEigenNilpotent f a) :=
  f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap a

private theorem coe_generalizedEigenNilpotent_pow_apply (f : End K V) (a : K) (k : ℕ)
    (v : f.maxGenEigenspace a) :
    ((generalizedEigenNilpotent f a ^ k) v : V) = ((f - a • 1) ^ k) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, coe_generalizedEigenNilpotent_apply, ih, pow_succ',
      Module.End.mul_apply]
    rfl

/-- The kernel of a shifted power is contained in the corresponding generalized eigenspace,
so the restriction has the same kernel dimension. -/
theorem finrank_ker_generalizedEigenNilpotent_pow (f : End K V) (a : K) (k : ℕ) :
    finrank K (LinearMap.ker (generalizedEigenNilpotent f a ^ k)) =
      finrank K (LinearMap.ker ((f - a • 1) ^ k)) := by
  let E := f.maxGenEigenspace a
  let P := LinearMap.ker ((f - a • 1) ^ k)
  have hP : P ≤ E := fun v hv => (f.mem_maxGenEigenspace a v).mpr ⟨k, mem_ker.mp hv⟩
  have hker : LinearMap.ker (generalizedEigenNilpotent f a ^ k) = P.comap E.subtype := by
    ext v
    change (generalizedEigenNilpotent f a ^ k) v = 0 ↔ ((f - a • 1) ^ k) (v : V) = 0
    rw [← coe_generalizedEigenNilpotent_pow_apply]
    exact (Submodule.coe_eq_zero).symm
  rw [hker]
  exact (Submodule.comapSubtypeEquivOfLe hP).finrank_eq

/-- Equal algebraic multiplicities and equal ranks of shifted ambient powers give a linear
equivalence intertwining the nilpotent restrictions at the two specified eigenvalues. -/
theorem exists_generalizedEigenNilpotent_equiv [FiniteDimensional K V] [FiniteDimensional K W]
    (f : End K V) (g : End K W) (a b : K) (hdim : finrank K V = finrank K W)
    (hm : f.charpoly.rootMultiplicity a = g.charpoly.rootMultiplicity b)
    (hr : ∀ k ≤ finrank K V,
      finrank K (LinearMap.range ((f - a • 1) ^ k)) =
      finrank K (LinearMap.range ((g - b • 1) ^ k))) :
    ∃ e : f.maxGenEigenspace a ≃ₗ[K] g.maxGenEigenspace b,
      ∀ v, e (generalizedEigenNilpotent f a v) = generalizedEigenNilpotent g b (e v) := by
  apply exists_intertwiningLinearEquiv_of_nilpotent_rankPowers _ _
    (isNilpotent_generalizedEigenNilpotent f a) (isNilpotent_generalizedEigenNilpotent g b)
  intro k hk
  have hd : finrank K (f.maxGenEigenspace a) = finrank K (g.maxGenEigenspace b) := by
    rw [f.finrank_maxGenEigenspace_eq, g.finrank_maxGenEigenspace_eq, hm]
  have hle : k ≤ finrank K V := hk.trans (Submodule.finrank_le _)
  have hfa := ((f - a • 1) ^ k : End K V).finrank_range_add_finrank_ker
  have hga := ((g - b • 1) ^ k : End K W).finrank_range_add_finrank_ker
  have hker : finrank K (LinearMap.ker ((f - a • 1) ^ k)) =
      finrank K (LinearMap.ker ((g - b • 1) ^ k)) := by
    rw [hr k hle, hdim, ← hga] at hfa
    exact Nat.add_left_cancel hfa
  have hf := ((generalizedEigenNilpotent f a) ^ k).finrank_range_add_finrank_ker
  have hg := ((generalizedEigenNilpotent g b) ^ k).finrank_range_add_finrank_ker
  rw [finrank_ker_generalizedEigenNilpotent_pow, hker, hd, ← hg,
    finrank_ker_generalizedEigenNilpotent_pow] at hf
  exact Nat.add_right_cancel hf

/-- The generalized eigenspaces of the distinct eigenvalues give an internal direct sum. -/
theorem isInternal_finset_maxGenEigenspace [DecidableEq K] [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) (s : Finset K) (hs : ∀ z, z ∈ s ↔ f.HasEigenvalue z) :
    DirectSum.IsInternal (fun z : s => f.maxGenEigenspace (z : K)) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (f.independent_maxGenEigenspace.comp Subtype.coe_injective)
  apply top_unique
  rw [← f.iSup_maxGenEigenspace_eq_top]
  apply iSup_le
  intro z
  by_cases hz : z ∈ s
  · exact le_iSup (fun x : s => f.maxGenEigenspace (x : K)) ⟨z, hz⟩
  · have hbot : f.maxGenEigenspace z = ⊥ := by
      rw [f.maxGenEigenspace_eq_genEigenspace_finrank]
      by_contra hne
      exact hz ((hs z).mpr (Module.End.hasEigenvalue_of_hasGenEigenvalue hne))
    rw [hbot]
    exact bot_le

/-- Intertwining equivalences on all components of two internal direct sums assemble into
an ambient intertwining equivalence. -/
theorem exists_intertwiningLinearEquiv_of_internal {ι : Type*} [DecidableEq ι]
    (U : ι → Submodule K V) (Z : ι → Submodule K W)
    (hU : DirectSum.IsInternal U) (hZ : DirectSum.IsInternal Z) (f : End K V) (g : End K W)
    (e : ∀ i, U i ≃ₗ[K] Z i) (hf : ∀ i, Set.MapsTo f (U i) (U i))
    (he : ∀ i (x : U i), (e i ⟨f x, hf i x.property⟩ : W) = g (e i x : W)) :
    ∃ E : V ≃ₗ[K] W, (∀ i (x : U i), E x = (e i x : W)) ∧ ∀ v, E (f v) = g (E v) := by
  let P := LinearEquiv.ofBijective (DirectSum.coeLinearMap U) hU
  let Q := LinearEquiv.ofBijective (DirectSum.coeLinearMap Z) hZ
  let E := P.symm.trans ((DirectSum.congrLinearEquiv e).trans Q)
  have hP (i : ι) (x : U i) : P (DirectSum.lof K ι (fun i => U i) i x) = (x : V) :=
    DirectSum.coeLinearMap_lof U i x
  have hE (i : ι) (x : U i) : E x = (e i x : W) := by
    rw [← hP i x]
    change Q (DirectSum.congrLinearEquiv e (P.symm (P (DirectSum.lof K ι (fun i => U i) i x)))) = _
    rw [P.symm_apply_apply, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
    exact DirectSum.coeLinearMap_lof Z i (e i x)
  refine ⟨E, hE, fun v => ?_⟩
  have h : (E.toLinearMap.comp f).comp P.toLinearMap = (g.comp E.toLinearMap).comp P.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    ext1 x
    change E (f (P (DirectSum.lof K ι (fun i => U i) i x))) =
      g (E (P (DirectSum.lof K ι (fun i => U i) i x)))
    rw [hP, hE i x]
    have h' : E (f x) = (e i ⟨f x, hf i x.property⟩ : W) := hE i ⟨f x, hf i x.property⟩
    rw [h', he]
  have hv := LinearMap.congr_fun h (P.symm v)
  change E (f (P (P.symm v))) = g (E (P (P.symm v))) at hv
  rwa [P.apply_symm_apply] at hv

end Langlands
