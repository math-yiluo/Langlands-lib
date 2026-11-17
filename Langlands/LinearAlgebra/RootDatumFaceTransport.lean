import Langlands.LinearAlgebra.RootDatumFaceHeight

/-! # Based face heights under full root-datum equivalences -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.LinearAlgebra.RootDatumFaceTransport

open RootDatumFaceHeight

variable {J M N J' M' N' : Type*}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  {P : RootDatum J M N} {Q : RootDatum J' M' N'} (e : RootPairing.Equiv P Q)

/-- A full root-datum equivalence maps the integral root span into the target
integral root span. -/
theorem weight_mem_rootSpan {x : M} (hx : x ∈ P.rootSpan ℤ) :
    e.weightEquiv x ∈ Q.rootSpan ℤ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [RootPairing.Equiv.weightEquiv_apply, e.root_weightMap_apply P Q]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- Restrict the full weight-lattice equivalence to the integral root spans. -/
def rootSpanMap : P.rootSpan ℤ →ₗ[ℤ] Q.rootSpan ℤ where
  toFun x := ⟨e.weightEquiv x, weight_mem_rootSpan e x.property⟩
  map_add' x y := Subtype.ext (map_add e.weightEquiv (x : M) (y : M))
  map_smul' a x := Subtype.ext (map_smul e.weightEquiv a (x : M))

@[simp] theorem rootSpanMap_root (a : J) :
    rootSpanMap e (P.rootSpanMem ℤ a) = Q.rootSpanMem ℤ (e.indexEquiv a) := by
  apply Subtype.ext
  exact e.root_weightMap_apply P Q a

variable (b : P.Base)

/-- Ordinary based heights are unchanged by the matching of root indices. -/
theorem height_map (a : J) : (b.map e).height (e.indexEquiv a) = b.height a := by
  classical
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int a
  have hg : Q.root (e.indexEquiv a) =
      ∑ c ∈ (b.map e).support, f (e.indexEquiv.symm c) • Q.root c := by
    rw [RootPairing.Base.support_map_eq, Finset.sum_image e.indexEquiv.injective.injOn]
    simp only [Equiv.symm_apply_apply]
    have h := congrArg e.weightEquiv hf
    simp only [map_sum, map_zsmul, RootPairing.Equiv.weightEquiv_apply,
      e.root_weightMap_apply P Q] at h
    exact h
  rw [(b.map e).height_eq_sum hg, b.height_eq_sum hf,
    RootPairing.Base.support_map_eq, Finset.sum_image e.indexEquiv.injective.injOn]
  simp only [Equiv.symm_apply_apply]

/-- A full root-datum equivalence preserves positivity relative to the mapped base. -/
theorem isPos_map_iff (a : J) :
    (b.map e).IsPos (e.indexEquiv a) ↔ b.IsPos a := by
  rw [RootPairing.Base.isPos_iff, height_map, RootPairing.Base.isPos_iff]

/-- The unscaled face-height linear form is natural under the full weight and
contravariant coweight equivalences, including all central lattice directions. -/
theorem faceHeight_map (v : N) :
    (faceHeight (b.map e) (e.coweightEquiv.symm v)).comp (rootSpanMap e) =
      faceHeight b v := by
  classical
  apply b.toWeightBasisInt.ext
  intro a
  have ha : b.toWeightBasisInt a = P.rootSpanMem ℤ a := by ext; simp
  have hs : e.indexEquiv (a : J) ∈ (b.map e).support := by
    rw [RootPairing.Base.support_map_eq]
    exact Finset.mem_image.mpr ⟨a, a.property, rfl⟩
  rw [LinearMap.comp_apply, ha, rootSpanMap_root,
    faceHeight_simple _ _ _ hs, faceHeight_simple _ _ _ a.property,
    e.root'_coweightEquiv]

end Langlands.LinearAlgebra.RootDatumFaceTransport
