/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Fibre product of a finite Galois field extension

Source: Stacks Project, `pione.tex`, Tag 03SF (blueprint:
lem-exc-finite-galois-algebra-tensor-decomposition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

/-- (blueprint: lem-exc-finite-galois-algebra-tensor-decomposition) For a finite Galois
extension `E/L`, a supplied algebra isomorphism sending `a ⊗ b` to `(a * q b)₍q₎`
identifies the affine fibre product with the finite coproduct of copies of `Spec E`.
Under the affine pullback isomorphism (lem-weil-pbc-fibre-product-affine-spectra),
the component maps are induced by the coordinate projections of the product ring
(lem-weil-pbc-spec-finite-product-fields). On the `q`-th component the first pullback
projection is the identity and the second is `Spec q`: the tensor inclusions
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` become `a ↦ a` and `b ↦ q b` after evaluation at `q`.
The argument includes `E = L`, when the automorphism group has one element.
Source: Stacks Project, `pione.tex`, Tags 03SF, 01I4, and 00ED. -/
theorem finiteGaloisTensorCoproduct
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E]
    (φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E))
    (hφ : ∀ (a b : E) (q : E ≃ₐ[L] E), φ (a ⊗ₜ[L] b) q = a * q b) :
    ∃ e : (∐ fun _ : E ≃ₐ[L] E => Spec (.of E)) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap L E)))
          (Spec.map (CommRingCat.ofHom (algebraMap L E))),
      (∀ q : E ≃ₐ[L] E,
        Sigma.ι (fun _ : E ≃ₐ[L] E => Spec (.of E)) q ≫ e.hom ≫
          pullback.fst _ _ = 𝟙 (Spec (.of E))) ∧
      (∀ q : E ≃ₐ[L] E,
        Sigma.ι (fun _ : E ≃ₐ[L] E => Spec (.of E)) q ≫ e.hom ≫
          pullback.snd _ _ = Spec.map (CommRingCat.ofHom q.toRingEquiv.toRingHom)) := by
  classical
  let R : (E ≃ₐ[L] E) → CommRingCat := fun _ ↦ .of E
  let eφ := Scheme.Spec.mapIso φ.toRingEquiv.toCommRingCatIso.op
  refine ⟨asIso (sigmaSpec R) ≪≫ eφ ≪≫ (pullbackSpecIso L E E).symm, ?_, ?_⟩
  · intro q
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_fst]
    rw [ι_sigmaSpec_assoc R q]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : E ≃ₐ[L] E ↦ E) q)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    have h : (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : E ≃ₐ[L] E ↦ E) q) =
        𝟙 (CommRingCat.of E) := by
      ext a
      simpa using hφ a 1 q
    rw [Category.assoc, h, Spec.map_id]
  · intro q
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_snd]
    rw [ι_sigmaSpec_assoc R q]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : E ≃ₐ[L] E ↦ E) q)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext b
    simpa using hφ 1 b q

end AlgebraicGeometry
