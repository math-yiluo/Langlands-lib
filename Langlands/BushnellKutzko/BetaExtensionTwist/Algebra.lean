import Langlands.LinearAlgebra.IrreducibleRepresentationSpan
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Tensor intertwiners with one factor trivial on a restricted domain -/

noncomputable section
open scoped TensorProduct

namespace Langlands.BushnellKutzko

universe uG uH uM uN

variable {G : Type uG} [Group G] {H : Type uH} [Group H]
  {M : Type uM} [AddCommGroup M] [Module ℂ M]
  {N : Type uN} [AddCommGroup N] [Module ℂ N]

section Slices

/-- Evaluation against a linear functional on the right tensor factor. -/
private def rightSlice (φ : N →ₗ[ℂ] ℂ) : M ⊗[ℂ] N →ₗ[ℂ] M :=
  (TensorProduct.rid ℂ M).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ

@[simp] private theorem rightSlice_tmul (φ : N →ₗ[ℂ] ℂ) (x : M) (y : N) :
    rightSlice φ (x ⊗ₜ[ℂ] y) = φ y • x := by
  simp [rightSlice]

private theorem rightSlice_map_one (φ : N →ₗ[ℂ] ℂ) (a : Module.End ℂ M) (z : M ⊗[ℂ] N) :
    rightSlice φ (TensorProduct.map a (1 : Module.End ℂ N) z) = a (rightSlice φ z) := by
  change (rightSlice φ ∘ₗ TensorProduct.map a (1 : Module.End ℂ N)) z =
    (a ∘ₗ rightSlice φ) z
  congr 1
  exact TensorProduct.ext' fun x y => by simp

private theorem rightSlice_separates {z z' : M ⊗[ℂ] N}
    (h : ∀ φ : N →ₗ[ℂ] ℂ, rightSlice φ z = rightSlice φ z') : z = z' := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ N
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  simpa only [TensorProduct.equivFinsuppOfBasisRight_apply, rightSlice,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_def] using h (b.coord i)

/-- Evaluation against a linear functional on the left tensor factor. -/
private def leftSlice (ψ : M →ₗ[ℂ] ℂ) : M ⊗[ℂ] N →ₗ[ℂ] N :=
  (TensorProduct.lid ℂ N).toLinearMap ∘ₗ TensorProduct.map ψ LinearMap.id

@[simp] private theorem leftSlice_tmul (ψ : M →ₗ[ℂ] ℂ) (x : M) (y : N) :
    leftSlice ψ (x ⊗ₜ[ℂ] y) = ψ x • y := by
  simp [leftSlice]

private theorem leftSlice_rightSlice (ψ : M →ₗ[ℂ] ℂ) (φ : N →ₗ[ℂ] ℂ) (z : M ⊗[ℂ] N) :
    φ (leftSlice ψ z) = ψ (rightSlice φ z) := by
  change (φ ∘ₗ leftSlice ψ) z = (ψ ∘ₗ rightSlice φ) z
  congr 1
  exact TensorProduct.ext' fun x y => by simp [mul_comm]

private theorem tensorLeft_injective {x : M} (hx : x ≠ 0) :
    Function.Injective ((TensorProduct.mk ℂ M N) x) := by
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  intro y y' h
  change x ⊗ₜ[ℂ] y = x ⊗ₜ[ℂ] y' at h
  simpa [hψ] using congrArg (leftSlice ψ) h

variable (a : H →* G) (ρ₁ ρ₂ : Representation ℂ G M) (τ₁ τ₂ : Representation ℂ G N)
  (ht₁ : ∀ h, τ₁ (a h) = 1) (ht₂ : ∀ h, τ₂ (a h) = 1)

private def restrictTensorSlice
    (f : (ρ₁.tprod τ₁).IntertwiningMap (ρ₂.tprod τ₂)) (y : N) (φ : N →ₗ[ℂ] ℂ) :
    Representation.IntertwiningMap (ρ₁.comp a) (ρ₂.comp a) where
  toLinearMap := rightSlice φ ∘ₗ f.toLinearMap ∘ₗ (TensorProduct.mk ℂ M N).flip y
  isIntertwining' h := by
    ext x
    change rightSlice φ (f (ρ₁ (a h) x ⊗ₜ[ℂ] y)) =
      ρ₂ (a h) (rightSlice φ (f (x ⊗ₜ[ℂ] y)))
    have hf := congrArg (rightSlice (M := M) φ) (Representation.IntertwiningMap.isIntertwining _ _ f (a h) (x ⊗ₜ[ℂ] y))
    simpa only [Representation.tprod_apply, ht₁, ht₂, TensorProduct.map_tmul,
      Module.End.one_apply, rightSlice_map_one] using hf

include ht₁ ht₂ in
/-- An intertwiner of the tensor products yields a nonzero intertwiner of the left
factors on a subgroup on which both right factors are trivial. -/
theorem exists_intertwiner_of_tensor_restriction
    (f : (ρ₁.tprod τ₁).IntertwiningMap (ρ₂.tprod τ₂)) (hf : f ≠ 0) :
    ∃ s : Representation.IntertwiningMap (ρ₁.comp a) (ρ₂.comp a), s ≠ 0 := by
  by_contra! h
  apply hf
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  apply rightSlice_separates
  intro φ
  exact congrArg (fun s : Representation.IntertwiningMap (ρ₁.comp a) (ρ₂.comp a) => s x)
    (h (restrictTensorSlice a ρ₁ ρ₂ τ₁ τ₂ ht₁ ht₂ f y φ))

/-- If a single nonzero full intertwiner spans the restricted intertwining space,
tensoring by it identifies the right-factor and tensor-product intertwining spaces. -/
def tensorIntertwiningEquiv
    (s : ρ₁.IntertwiningMap ρ₂) (hs : s ≠ 0)
    (hspan : ∀ q : Representation.IntertwiningMap (ρ₁.comp a) (ρ₂.comp a),
      ∃ c : ℂ, q.toLinearMap = c • s.toLinearMap) :
    (τ₁.IntertwiningMap τ₂) ≃ₗ[ℂ] ((ρ₁.tprod τ₁).IntertwiningMap (ρ₂.tprod τ₂)) := by
  let T : (τ₁.IntertwiningMap τ₂) →ₗ[ℂ] ((ρ₁.tprod τ₁).IntertwiningMap (ρ₂.tprod τ₂)) :=
    { toFun := s.tensor
      map_add' := fun _ _ => Representation.IntertwiningMap.tensor_add_right _ _ _
      map_smul' := fun _ _ => Representation.IntertwiningMap.tensor_smul_right _ _ _ }
  refine LinearEquiv.ofBijective T ?_
  obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hs
  change s x₀ ≠ 0 at hx₀
  constructor
  · intro t t' heq
    apply DFunLike.ext
    intro y
    exact tensorLeft_injective hx₀
      (congrArg (fun f : (ρ₁.tprod τ₁).IntertwiningMap (ρ₂.tprod τ₂) => f (x₀ ⊗ₜ[ℂ] y)) heq)
  · intro f
    obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hx₀
    let t : Module.End ℂ N := leftSlice ψ ∘ₗ f.toLinearMap ∘ₗ (TensorProduct.mk ℂ M N) x₀
    have hfactor (x : M) (y : N) : f (x ⊗ₜ[ℂ] y) = s x ⊗ₜ[ℂ] t y := by
      apply rightSlice_separates
      intro φ
      let q := restrictTensorSlice a ρ₁ ρ₂ τ₁ τ₂ ht₁ ht₂ f y φ
      obtain ⟨c, hc⟩ := hspan q
      have hc' (v : M) : rightSlice φ (f (v ⊗ₜ[ℂ] y)) = c • s v :=
        congrArg (fun g : Module.End ℂ M => g v) hc
      rw [hc', rightSlice_tmul]
      change c • s x = φ (leftSlice ψ (f (x₀ ⊗ₜ[ℂ] y))) • s x
      rw [leftSlice_rightSlice, hc']
      simp [hψ]
    have ht (g : G) (y : N) : t (τ₁ g y) = τ₂ g (t y) := by
      have h₀ := Representation.IntertwiningMap.isIntertwining _ _ f g (x₀ ⊗ₜ[ℂ] y)
      have hnonzero : s (ρ₁ g x₀) ≠ 0 := by
        rw [Representation.IntertwiningMap.isIntertwining _ _ s]
        simpa only [map_zero] using (Representation.apply_bijective ρ₂ g).injective.ne hx₀
      apply tensorLeft_injective hnonzero
      change s (ρ₁ g x₀) ⊗ₜ[ℂ] t (τ₁ g y) = s (ρ₁ g x₀) ⊗ₜ[ℂ] τ₂ g (t y)
      simpa only [Representation.tprod_apply, TensorProduct.map_tmul, hfactor,
        Representation.IntertwiningMap.isIntertwining _ _ s] using h₀
    refine ⟨t.intertwiningMap_of_isIntertwiningMap τ₁ τ₂ ht, ?_⟩
    exact Representation.IntertwiningMap.ext (TensorProduct.ext' fun x y => (hfactor x y).symm)

end Slices

section Irreducibility

open scoped MonoidAlgebra

/-- If the left factor stays irreducible on a subgroup on which the right factor is
trivial, then tensoring with the right irreducible factor preserves irreducibility. -/
theorem isIrreducible_tensor_of_irreducible_restriction [FiniteDimensional ℂ M]
    [FiniteDimensional ℂ N] (a : H →* G) (ρ : Representation ℂ G M)
    (τ : Representation ℂ G N) (hρ : Representation.IsIrreducible (ρ.comp a)) (hτ : τ.IsIrreducible)
    (ht : ∀ h, τ (a h) = 1) : (ρ.tprod τ).IsIrreducible := by
  let := hρ
  let := hτ
  have : Nontrivial M := IsSimpleModule.nontrivial ℂ[H] (Representation.asModule (ρ.comp a))
  have : Nontrivial N := IsSimpleModule.nontrivial ℂ[G] τ.asModule
  have : Nontrivial (M ⊗[ℂ] N) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    obtain ⟨y, hy⟩ := exists_ne (0 : N)
    exact ⟨⟨x ⊗ₜ[ℂ] y, x ⊗ₜ[ℂ] 0, (tensorLeft_injective hx).ne hy⟩⟩
  have : Nontrivial (Subrepresentation (ρ.tprod τ)) :=
    ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule ℂ (M ⊗[ℂ] N)) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU => ?_
  let P := U.toSubmodule
  have hP : P ≠ ⊥ := fun h => hU (Subrepresentation.toSubmodule_injective h)
  have left (f : Module.End ℂ M) (z : M ⊗[ℂ] N) (hz : z ∈ P) :
      TensorProduct.map f (1 : Module.End ℂ N) z ∈ P := by
    obtain ⟨r, rfl⟩ := Langlands.LinearAlgebra.asAlgebraHom_surjective_of_irreducible
      (ρ.comp a) f
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp [P]
    | add r r' hr hr' =>
      rw [map_add, TensorProduct.map_add_left, LinearMap.add_apply]
      exact P.add_mem hr hr'
    | single h c =>
      rw [Representation.asAlgebraHom_single, TensorProduct.map_smul_left, LinearMap.smul_apply]
      apply P.smul_mem
      simpa only [Representation.tprod_apply, ht, MonoidHom.comp_apply] using
        U.apply_mem_toSubmodule (a h) hz
  have right (f : Module.End ℂ N) (z : M ⊗[ℂ] N) (hz : z ∈ P) :
      TensorProduct.map (1 : Module.End ℂ M) f z ∈ P := by
    obtain ⟨r, rfl⟩ := Langlands.LinearAlgebra.asAlgebraHom_surjective_of_irreducible τ f
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp [P]
    | add r r' hr hr' =>
      rw [map_add, TensorProduct.map_add_right, LinearMap.add_apply]
      exact P.add_mem hr hr'
    | single g c =>
      rw [Representation.asAlgebraHom_single, TensorProduct.map_smul_right, LinearMap.smul_apply]
      apply P.smul_mem
      have hz' := left (ρ g⁻¹) _ (U.apply_mem_toSubmodule g hz)
      change TensorProduct.map (ρ g⁻¹) 1 (TensorProduct.map (ρ g) (τ g) z) ∈ P at hz'
      have hinv : ρ g⁻¹ * ρ g = 1 := by
        rw [← map_mul ρ, inv_mul_cancel, map_one]
      have hcomp : (ρ g⁻¹).comp (ρ g) = (1 : Module.End ℂ M) := hinv
      simpa only [TensorProduct.map_map, hcomp, Module.End.one_eq_id, LinearMap.id_comp]
        using hz'
  apply Subrepresentation.toSubmodule_injective
  change P = ⊤
  obtain ⟨z, hz, hz₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hmem (f : Module.End ℂ (M ⊗[ℂ] N)) : f z ∈ P := by
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ M N M N).surjective f
    induction t with
    | tmul f g =>
      change TensorProduct.map f g z ∈ P
      have h := left f _ (right g z hz)
      simpa only [TensorProduct.map_map, Module.End.one_eq_id, LinearMap.comp_id,
        LinearMap.id_comp] using h
    | add t t' ht ht' =>
      simpa only [map_add, LinearMap.add_apply] using P.add_mem ht ht'
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hz₀
  refine eq_top_iff.mpr fun y _ => ?_
  simpa only [LinearMap.smulRight_apply, hψ, one_smul] using hmem (ψ.smulRight y)

end Irreducibility

end Langlands.BushnellKutzko
