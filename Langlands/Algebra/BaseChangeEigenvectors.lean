import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Eigenvectors of an endomorphism after extension of scalars -/

noncomputable section

open TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.BaseChangeEigenvectors

variable {k K M N : Type*} [Field k] [Field K] [Algebra k K]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Over a field, the kernel of a scalar extension is the scalar extension of the kernel. -/
theorem ker_baseChange (f : M →ₗ[k] N) :
    LinearMap.ker (f.baseChange K) = LinearMap.range ((LinearMap.ker f).subtype.baseChange K) :=
  Module.Flat.ker_lTensor_eq (R := k) K K f

/-- The range of a scalar extension is the scalar extension of any submodule equal to the
range. -/
theorem range_baseChange_eq {f : M →ₗ[k] N} {W : Submodule k N} (hW : LinearMap.range f = W) :
    LinearMap.range (f.baseChange K) = LinearMap.range (W.subtype.baseChange K) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul z m =>
      have hm : f m ∈ W := hW ▸ LinearMap.mem_range_self f m
      exact ⟨z ⊗ₜ ⟨f m, hm⟩, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul z w =>
      obtain ⟨m, hm⟩ : (w : N) ∈ LinearMap.range f := hW.symm ▸ w.2
      exact ⟨z ⊗ₜ m, by rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hm]; rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- The scalar extension of an endomorphism minus a scalar. -/
theorem baseChange_sub_smul (T : M →ₗ[k] M) (c : k) :
    (T - c • LinearMap.id).baseChange K = T.baseChange K - algebraMap k K c • LinearMap.id := by
  ext m
  simp [LinearMap.baseChange_sub, Algebra.smul_def]

/-- An eigenvector of the scalar extension lies in the scalar extension of the eigenspace. -/
theorem mem_range_of_baseChange_eigen (T : M →ₗ[k] M) (c : k) {x : K ⊗[k] M}
    (hx : T.baseChange K x = algebraMap k K c • x) :
    x ∈ LinearMap.range
      ((LinearMap.ker (T - c • LinearMap.id)).subtype.baseChange K) := by
  rw [← ker_baseChange, LinearMap.mem_ker, baseChange_sub_smul, LinearMap.sub_apply, hx,
    LinearMap.smul_apply, LinearMap.id_apply, sub_self]

/-- Pure tensors with an eigenvector on the right are eigenvectors. -/
theorem baseChange_tmul_eigen (T : M →ₗ[k] M) (c : k) (z : K) {m : M} (hm : T m = c • m) :
    T.baseChange K (z ⊗ₜ m) = algebraMap k K c • (z ⊗ₜ[k] m) := by
  rw [LinearMap.baseChange_tmul, hm, tmul_smul, algebraMap_smul]

/-- If a set of vectors is stable under the base field and contained in a submodule's span,
pure tensors with entries from its span lie in the span of the pure tensors from the set. -/
theorem tmul_mem_span_of_mem_span {E : Set M} {E' : Set (K ⊗[k] M)}
    (hE : ∀ z : K, ∀ m ∈ E, z ⊗ₜ[k] m ∈ Submodule.span K E') {m : M}
    (hm : m ∈ Submodule.span k E) (z : K) : z ⊗ₜ[k] m ∈ Submodule.span K E' := by
  induction hm using Submodule.span_induction generalizing z with
  | mem m hm => exact hE z m hm
  | zero => simp
  | add a b _ _ ha hb => rw [tmul_add]; exact Submodule.add_mem _ (ha z) (hb z)
  | smul c a _ ha => rw [← smul_tmul]; exact ha (c • z)

/-- Spanning by integral eigenvectors is preserved by extension of scalars. -/
theorem span_baseChange_eigen_eq_top (T : M →ₗ[k] M)
    (hT : Submodule.span k {m : M | ∃ n : ℤ, T m = (n : k) • m} = ⊤) :
    Submodule.span K {x : K ⊗[k] M | ∃ n : ℤ, T.baseChange K x = (n : K) • x} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul z m =>
    refine tmul_mem_span_of_mem_span (fun z m hm => ?_) (hT ▸ Submodule.mem_top) z
    obtain ⟨n, hn⟩ := hm
    refine Submodule.subset_span ⟨n, ?_⟩
    rw [baseChange_tmul_eigen T n z hn, map_intCast]

/-- The span of the positive integral eigenvectors after extension of scalars is the scalar
extension of the span of the positive integral eigenvectors. -/
theorem span_baseChange_positive_eigen (T : M →ₗ[k] M) [CharZero k] :
    Submodule.span K {x : K ⊗[k] M | ∃ n : ℕ, T.baseChange K x = ((n + 1 : ℕ) : K) • x} =
      LinearMap.range ((Submodule.span k {m : M | ∃ n : ℕ, T m = ((n + 1 : ℕ) : k) • m}).subtype.baseChange K) := by
  set W := Submodule.span k {m : M | ∃ n : ℕ, T m = ((n + 1 : ℕ) : k) • m}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨n, hn⟩
    have hx := mem_range_of_baseChange_eigen T ((n + 1 : ℕ) : k)
      (x := x) (by rw [hn, map_natCast])
    have hle : LinearMap.ker (T - ((n + 1 : ℕ) : k) • LinearMap.id) ≤ W := by
      intro m hm
      refine Submodule.subset_span ⟨n, ?_⟩
      have := LinearMap.mem_ker.mp hm
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(Submodule.inclusion hle).baseChange K y, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul z w =>
      rw [LinearMap.baseChange_tmul]
      refine tmul_mem_span_of_mem_span (fun z m hm => ?_) w.2 z
      obtain ⟨n, hn⟩ := hm
      refine Submodule.subset_span ⟨n, ?_⟩
      rw [baseChange_tmul_eigen T _ z hn, map_natCast]

omit [Field K] [Algebra k K] in
/-- If submodules spanning the space consist of eigenvectors for pairwise distinct eigenvalues,
they are exactly the eigenspaces. -/
theorem eq_eigenspace_of_iSup_eq_top {ι : Type*} (T : Module.End k M) (W : ι → Submodule k M)
    (μ : ι → k) (hμ : Function.Injective μ) (hW : ∀ i, ∀ x ∈ W i, T x = μ i • x)
    (htop : ⨆ i, W i = ⊤) (i : ι) : W i = T.eigenspace (μ i) := by
  have hind : iSupIndep (fun j => T.eigenspace (μ j)) :=
    (Module.End.eigenspaces_iSupIndep T).comp hμ
  have hle : W ≤ fun j => T.eigenspace (μ j) := fun j x hx =>
    Module.End.mem_eigenspace_iff.mpr (hW j x hx)
  exact congrFun ((hind.le_iff_eq_of_iSup_eq_top htop).mp hle) i

end Langlands.Algebra.BaseChangeEigenvectors
