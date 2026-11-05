import Langlands.GroupScheme.Reductive.CovariantProducts
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-! # Injectivity of products of left-covariant coordinates -/

noncomputable section

open TensorProduct Coalgebra WithConv

namespace Langlands.GroupScheme.Chevalley

section Convolution

variable {k A R : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
  [CommRing R] [Algebra k R]

/-- The antipode algebra map is a right convolution inverse of the identity map:
`id * S = 1`. -/
theorem id_convMul_antipodeAlgHom :
    toConv (AlgHom.id k A) * toConv (HopfAlgebra.antipodeAlgHom k A) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  simp [LinearMap.id_mul_antipode]

/-- Composition with an algebra map preserves the convolution unit. -/
theorem comp_convOne (f : A →ₐ[k] R) :
    f.comp (1 : WithConv (A →ₐ[k] A)).ofConv = (1 : WithConv (A →ₐ[k] R)).ofConv := by
  ext a
  simp [AlgHom.convOne_def]

/-- A point `f` composed with the antipode is a left convolution inverse of `f`:
`(f ∘ S) * f = 1`. -/
theorem antipode_convMul_self (f : A →ₐ[k] R) :
    toConv (f.comp (HopfAlgebra.antipodeAlgHom k A)) * toConv f = 1 := by
  apply WithConv.ofConv_injective
  have h := AlgHom.comp_convMul_distrib f (toConv (HopfAlgebra.antipodeAlgHom k A))
    (toConv (AlgHom.id k A))
  rw [AlgHom.antipode_id_cancel, comp_convOne] at h
  simpa using h.symm

/-- A point `f` composed with the antipode is a right convolution inverse of `f`:
`f * (f ∘ S) = 1`. -/
theorem self_convMul_antipode (f : A →ₐ[k] R) :
    toConv f * toConv (f.comp (HopfAlgebra.antipodeAlgHom k A)) = 1 := by
  apply WithConv.ofConv_injective
  have h := AlgHom.comp_convMul_distrib f (toConv (AlgHom.id k A))
    (toConv (HopfAlgebra.antipodeAlgHom k A))
  rw [id_convMul_antipodeAlgHom, comp_convOne] at h
  simpa using h.symm

/-- Left convolution by a point cancels against its antipode composite. -/
theorem self_convMul_antipode_convMul (f g : A →ₐ[k] R) :
    toConv f * (toConv (f.comp (HopfAlgebra.antipodeAlgHom k A)) * toConv g) = toConv g := by
  rw [← mul_assoc, self_convMul_antipode, one_mul]

variable {C D : Type*} [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]

/-- The tensor product of two algebra maps after comultiplication is the convolution of
the two maps into the tensor product. -/
theorem map_comp_comulAlgHom (f : A →ₐ[k] C) (g : A →ₐ[k] D) :
    (Algebra.TensorProduct.map f g).comp (Bialgebra.comulAlgHom k A) =
      (toConv (Algebra.TensorProduct.includeLeft.comp f) *
        toConv (Algebra.TensorProduct.includeRight.comp g)).ofConv := by
  rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

/-- Convolution with a covariant coordinate splits off the covariance weight. -/
theorem convMul_apply_of_mem_leftCovariantSubspace (r : A →ₐ[k] C) (χ : C) {f : A}
    (hf : f ∈ leftCovariantSubspace r.toLinearMap χ) (p : C →ₐ[k] R) (w : A →ₐ[k] R) :
    (toConv (p.comp r) * toConv w).ofConv f = p χ * w f := by
  rw [mem_leftCovariantSubspace] at hf
  have hmap : (Algebra.TensorProduct.map (p.comp r) w).toLinearMap =
      (Algebra.TensorProduct.map p w).toLinearMap ∘ₗ r.toLinearMap.rTensor A := by
    apply TensorProduct.ext'
    intro x y
    rfl
  rw [AlgHom.convMul_def, ofConv_toConv]
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  have h := LinearMap.congr_fun hmap (comul (R := k) f)
  simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
  rw [h, hf]
  simp

end Convolution

section Injective

variable {k A C D : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
  [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]

/-- The coordinate comorphism of `(p, q) ↦ i(p) i'(q)⁻¹` for two coordinate restriction
maps `r` and `s`. -/
def differenceComorphism (r : A →ₐ[k] C) (s : A →ₐ[k] D) : A →ₐ[k] C ⊗[k] D :=
  (Algebra.TensorProduct.map r (s.comp (HopfAlgebra.antipodeAlgHom k A))).comp
    (Bialgebra.comulAlgHom k A)

/-- The comorphism of `(a, y) ↦ (a y, y)` on the product of the group with itself. -/
def shearComorphism : A ⊗[k] A →ₐ[k] A ⊗[k] A :=
  Algebra.TensorProduct.productMap (Bialgebra.comulAlgHom k A)
    Algebra.TensorProduct.includeRight

/-- The comorphism of `(x, y) ↦ (x y⁻¹, y)`, inverse to `shearComorphism`. -/
def unshearComorphism : A ⊗[k] A →ₐ[k] A ⊗[k] A :=
  Algebra.TensorProduct.productMap
    (toConv (Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := A)) *
      toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A) (B := A)).comp
        (HopfAlgebra.antipodeAlgHom k A))).ofConv
    Algebra.TensorProduct.includeRight

theorem productMap_comp_comulAlgHom {R : Type*} [CommRing R] [Algebra k R]
    (f g : A →ₐ[k] R) :
    (Algebra.TensorProduct.productMap f g).comp (Bialgebra.comulAlgHom k A) =
      (toConv f * toConv g).ofConv := by
  rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

theorem unshear_comp_shear :
    (unshearComorphism (k := k) (A := A)).comp shearComorphism = AlgHom.id k (A ⊗[k] A) := by
  have hleft : ∀ a : A, unshearComorphism (k := k) (A := A) (comul (R := k) a) = a ⊗ₜ[k] 1 := by
    intro a
    have h := congrArg (fun φ : A →ₐ[k] A ⊗[k] A => φ a)
      (productMap_comp_comulAlgHom
        (toConv (Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := A)) *
          toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A) (B := A)).comp
            (HopfAlgebra.antipodeAlgHom k A))).ofConv
        (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := A)))
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, toConv_ofConv] at h
    rw [mul_assoc, antipode_convMul_self, mul_one] at h
    exact h
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [AlgHom.comp_apply, shearComorphism, Algebra.TensorProduct.productMap_apply_tmul,
    Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeRight_apply, map_mul, hleft,
    AlgHom.id_apply]
  simp only [unshearComorphism, Algebra.TensorProduct.productMap_right_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]

theorem shearComorphism_injective :
    Function.Injective (shearComorphism (k := k) (A := A)) := by
  intro x y h
  have := congrArg (unshearComorphism (k := k) (A := A)) h
  simpa only [← AlgHom.comp_apply, unshear_comp_shear, AlgHom.id_apply] using this

/-- If the comorphism of `(p, q) ↦ i(p) i'(q)⁻¹` is injective, then multiplication is
injective on the full tensor product of a left `r`-covariant coordinate subspace with a
left `s`-covariant coordinate subspace. -/
theorem coordinateProduct_injective (r : A →ₐ[k] C) (s : A →ₐ[k] D) (χ : C) (ψ : D)
    {V W : Submodule k A} (hV : V ≤ leftCovariantSubspace r.toLinearMap χ)
    (hW : W ≤ leftCovariantSubspace s.toLinearMap ψ)
    (hdom : Function.Injective (differenceComorphism r s)) :
    Function.Injective (coordinateProduct V W) := by
  -- the canonical points of `(C ⊗ D) ⊗ A`
  let pC : C →ₐ[k] (C ⊗[k] D) ⊗[k] A :=
    Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft
  let pD : D →ₐ[k] (C ⊗[k] D) ⊗[k] A :=
    Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight
  let Z : A →ₐ[k] (C ⊗[k] D) ⊗[k] A := Algebra.TensorProduct.includeRight
  let Q' : A →ₐ[k] (C ⊗[k] D) ⊗[k] A :=
    (pD.comp s).comp (HopfAlgebra.antipodeAlgHom k A)
  let Y : A →ₐ[k] (C ⊗[k] D) ⊗[k] A := (toConv Q' * toConv Z).ofConv
  let δ := differenceComorphism r s
  let E : A ⊗[k] A →ₐ[k] (C ⊗[k] D) ⊗[k] A :=
    (Algebra.TensorProduct.map δ (AlgHom.id k A)).comp shearComorphism
  have hδ : (Algebra.TensorProduct.includeLeft (R := k) (B := A)).comp δ =
      (toConv (pC.comp r) * toConv Q').ofConv := by
    simp only [δ, differenceComorphism]
    rw [AlgHom.comp_assoc, map_comp_comulAlgHom, AlgHom.comp_convMul_distrib]
    rfl
  have hX : (Algebra.TensorProduct.map δ (AlgHom.id k A)).comp (Bialgebra.comulAlgHom k A) =
      (toConv (pC.comp r) * toConv Y).ofConv := by
    rw [map_comp_comulAlgHom, hδ, toConv_ofConv, AlgHom.comp_id, mul_assoc]
  have hZ : Z = (toConv (pD.comp s) * toConv Y).ofConv := by
    have h1 : toConv (pD.comp s) * toConv Y = toConv Z :=
      self_convMul_antipode_convMul (pD.comp s) Z
    rw [h1]
  have hE : ∀ (v : V) (w : W), E ((v : A) ⊗ₜ[k] (w : A)) =
      (pC χ * pD ψ) * Y ((v : A) * (w : A)) := by
    intro v w
    have hv : (Algebra.TensorProduct.map δ (AlgHom.id k A)) (comul (R := k) (v : A)) =
        pC χ * Y v := by
      rw [← convMul_apply_of_mem_leftCovariantSubspace r χ (hV v.2), ← hX]
      rfl
    have hw : Z (w : A) = pD ψ * Y w := by
      conv_lhs => rw [hZ]
      exact convMul_apply_of_mem_leftCovariantSubspace s ψ (hW w.2) pD Y
    simp only [E, shearComorphism, AlgHom.comp_apply,
      Algebra.TensorProduct.productMap_apply_tmul, Bialgebra.comulAlgHom_apply,
      Algebra.TensorProduct.includeRight_apply, map_mul, hv]
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    change _ * Z (w : A) = _
    rw [hw]
    ring
  have hlin : E.toLinearMap ∘ₗ TensorProduct.map V.subtype W.subtype =
      (LinearMap.mulLeft k (pC χ * pD ψ)) ∘ₗ Y.toLinearMap ∘ₗ coordinateProduct V W := by
    apply TensorProduct.ext'
    intro v w
    exact hE v w
  have hmap : Function.Injective (Algebra.TensorProduct.map δ (AlgHom.id k A)) := by
    have h2 : (Algebra.TensorProduct.map δ (AlgHom.id k A)).toLinearMap =
        TensorProduct.map δ.toLinearMap LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      rfl
    have h3 := TensorProduct.map_injective_of_flat_flat δ.toLinearMap
      (LinearMap.id : A →ₗ[k] A) hdom Function.injective_id
    rw [← h2] at h3
    exact h3
  have hι : Function.Injective (TensorProduct.map V.subtype W.subtype) :=
    TensorProduct.map_injective_of_flat_flat _ _ V.injective_subtype W.injective_subtype
  rw [injective_iff_map_eq_zero]
  intro F hF
  apply hι
  rw [map_zero]
  apply shearComorphism_injective
  rw [map_zero]
  apply hmap
  rw [map_zero]
  have := LinearMap.congr_fun hlin F
  simp only [LinearMap.comp_apply, hF, map_zero] at this
  exact this

end Injective

end Langlands.GroupScheme.Chevalley
