import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Langlands.Representation.Tensor.SmoothDualInjectivityStatement

/-!
# Injectivity of the finite smooth-dual tensor map

Over a field, the canonical map from a finite tensor product of spaces of
functionals into the dual of the tensor product is injective, without any
finiteness assumption on the factors. The smooth-dual tensor map is this map
precomposed with the tensor product of the injective inclusions of the factor
smooth duals.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uK uI uM uN

section Generic

variable {K : Type uK} [Field K] {ι : Type uI} [Finite ι]
variable {M : ι → Type uM} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
variable {N : ι → Type uN} [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]

omit [Finite ι] in
/-- Every tensor is the image of a tensor of finite-dimensional subspaces under
the tensor product of their inclusions. -/
theorem exists_finiteDimensional_tensor_preimage (x : ⨂[K] i, N i) :
    ∃ (D : ∀ i, Submodule K (N i)) (_ : ∀ i, FiniteDimensional K (D i))
      (y : ⨂[K] i, D i), PiTensorProduct.map (fun i => (D i).subtype) y = x := by
  classical
  have hx : x ∈ Submodule.span K (Set.range (PiTensorProduct.tprod K)) := by
    rw [PiTensorProduct.span_tprod_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  let D : ∀ i, Submodule K (N i) := fun i =>
    Submodule.span K ((c.support.image fun f => f i : Finset (N i)) : Set (N i))
  have hmem : ∀ f ∈ c.support, ∀ i, f i ∈ D i := fun f hf i =>
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hf))
  refine ⟨D, fun i => FiniteDimensional.span_finset K _,
    ∑ f ∈ c.support.attach,
      c f.1 • PiTensorProduct.tprod K (fun i => (⟨f.1 i, hmem f.1 f.2 i⟩ : D i)), ?_⟩
  rw [map_sum, Finsupp.sum, ← Finset.sum_attach c.support]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_smul, PiTensorProduct.map_tprod]
  rfl

/-- The finite-dimensional case: for injective maps from finite-dimensional
spaces into the factor duals, the induced map into the dual of the tensor
product is injective. -/
theorem dualDistrib_comp_map_injective_of_finiteDimensional
    {D : ι → Type uN} [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    [∀ i, FiniteDimensional K (D i)]
    (g : ∀ i, D i →ₗ[K] Module.Dual K (M i)) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map g) := by
  have := Fintype.ofFinite ι
  -- The evaluation maps `M i → Dual (D i)` are surjective.
  have he : ∀ i, Function.Surjective (g i).flip := by
    intro i
    rw [← LinearMap.dualMap_injective_iff]
    intro φ ψ h
    obtain ⟨d, rfl⟩ := (Module.evalEquiv K (D i)).surjective φ
    obtain ⟨d', rfl⟩ := (Module.evalEquiv K (D i)).surjective ψ
    congr 1
    apply hg i
    ext m
    exact LinearMap.congr_fun h m
  have hs : ∀ i, ∃ s : Module.Dual K (D i) →ₗ[K] M i, (g i).flip ∘ₗ s = LinearMap.id :=
    fun i => (g i).flip.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (he i))
  choose s hs using hs
  -- The finite-dimensional pairing factors through `g` and the right inverses `s`.
  have key : (PiTensorProduct.dualDistrib :
        (⨂[K] i, Module.Dual K (D i)) →ₗ[K] Module.Dual K (⨂[K] i, D i)) =
      (PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map g).flip ∘ₗ
        PiTensorProduct.map s := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro φ
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro d
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (LinearMap.congr_fun (LinearMap.congr_fun (hs i) (φ i)) (d i)).symm
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  rw [← Module.forall_dual_apply_eq_zero_iff K y]
  intro ψ
  obtain ⟨φ, rfl⟩ := (PiTensorProduct.dualDistribEquiv (R := K) (M := D)).surjective ψ
  change PiTensorProduct.dualDistrib φ y = 0
  rw [key, LinearMap.comp_apply, LinearMap.flip_apply, hy, LinearMap.zero_apply]

/-- Over a field, for injective maps into the factor duals, the induced map into
the dual of the finite tensor product is injective. No finiteness of the factors
is assumed. -/
theorem dualDistrib_comp_map_injective
    (g : ∀ i, N i →ₗ[K] Module.Dual K (M i)) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨D, hD, y, rfl⟩ := exists_finiteDimensional_tensor_preimage x
  have hy : y = 0 := by
    apply (LinearMap.ker_eq_bot'.mp (LinearMap.ker_eq_bot.mpr
      (dualDistrib_comp_map_injective_of_finiteDimensional
        (fun i => g i ∘ₗ (D i).subtype)
        (fun i => (hg i).comp (D i).injective_subtype)))) y
    rw [PiTensorProduct.map_comp]
    exact hx
  rw [hy, map_zero]

/-- Over a field, the canonical map from the finite tensor product of the factor
duals to the dual of the tensor product is injective. -/
theorem dualDistrib_injective :
    Function.Injective (PiTensorProduct.dualDistrib :
      (⨂[K] i, Module.Dual K (M i)) →ₗ[K] Module.Dual K (⨂[K] i, M i)) := by
  have h := dualDistrib_comp_map_injective (K := K) (M := M)
    (fun i => LinearMap.id) (fun _ => Function.injective_id)
  rwa [PiTensorProduct.map_id, LinearMap.comp_id] at h

end Generic

universe uG uV

/-- The canonical map from the finite tensor of smooth duals to the smooth dual
of the external tensor product is injective. -/
theorem smoothDualTensorInjectivity : SmoothDualTensorInjectivityStatement.{uI, uG, uV} := by
  intro ι _ G _ _ _ V _ _ ρ x y hxy
  have h := congrArg Subtype.val hxy
  rw [smoothDualTensorMap_val, smoothDualTensorMap_val] at h
  exact dualDistrib_comp_map_injective (fun i => smoothDualPairing (ρ i))
    (fun i => (smoothVectors (ρ i).dual).injective_subtype) h

end Langlands.FiniteTensor
