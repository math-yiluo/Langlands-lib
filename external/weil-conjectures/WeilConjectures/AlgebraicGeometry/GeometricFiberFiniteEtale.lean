/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# The geometric fibre of a finite étale scheme over a field

Let `Z₀` be a finite reduced scheme over a perfect field `k`, for instance the reduced closed
complement of a dense open of a curve over a finite field. Then `Z₀` is the spectrum of a finite
étale `k`-algebra `A`, and its geometric fibre `Z₀ ×_k k̄ = Spec (k̄ ⊗_k A)` is a finite disjoint
union of copies of `Spec k̄`: `k̄ ⊗_k A` is a finite product of copies of `k̄`, `k̄` being
separably closed.

## Main statements

- `AlgebraicGeometry.exists_isIso_sigmaDesc_geometricFiber_SpecMap`: for `A` étale over `k`,
  the geometric fibre of `Spec A` is `∐ Spec k̄`, by sections of its structure morphism.
- `AlgebraicGeometry.exists_isIso_sigmaDesc_geometricFiber_of_isFinite`: the same for a finite
  reduced `k`-scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **The geometric fibre of the spectrum of an étale algebra.** For an étale `k`-algebra `A`,
the geometric fibre `Spec A ×_k k̄ = Spec (A ⊗_k k̄)` of `Spec A` is a finite disjoint union of
copies of `Spec k̄`, by sections of its structure morphism to `Spec k̄`: the `k̄`-algebra
`k̄ ⊗_k A` is étale, hence a finite product of copies of `k̄`. -/
theorem exists_isIso_sigmaDesc_geometricFiber_SpecMap (A : Type u) [CommRing A] [Algebra k A]
    [Algebra.Etale k A] :
    ∃ (C : Type u) (_ : Finite C) (t : C → (Spec (.of (AlgebraicClosure k)) ⟶
        (Spec.map (CommRingCat.ofHom (algebraMap k A))).geometricFiber)),
      (∀ c, t c ≫ Scheme.Hom.geometricFiberToAlgebraicClosure _ = 𝟙 _) ∧
        IsIso (Sigma.desc t) := by
  let B := AlgebraicClosure k ⊗[k] A
  have := Algebra.Etale.finite_primeSpectrum (AlgebraicClosure k) B
  let e : B ≃ₐ[AlgebraicClosure k] (PrimeSpectrum B → AlgebraicClosure k) :=
    Algebra.FormallyEtale.equivPiOfIsSepClosed (AlgebraicClosure k) B
  let φ : A ⊗[k] AlgebraicClosure k ≃+* (PrimeSpectrum B → AlgebraicClosure k) :=
    (Algebra.TensorProduct.comm k A (AlgebraicClosure k)).toRingEquiv.trans e.toRingEquiv
  let g : (∐ fun _ : PrimeSpectrum B ↦ Spec (.of (AlgebraicClosure k))) ⟶
      (Spec.map (CommRingCat.ofHom (algebraMap k A))).geometricFiber :=
    sigmaSpec (fun _ : PrimeSpectrum B ↦ CommRingCat.of (AlgebraicClosure k)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (pullbackSpecIso k A (AlgebraicClosure k)).inv
  have hg : Sigma.desc (fun c ↦
      Sigma.ι (fun _ : PrimeSpectrum B ↦ Spec (.of (AlgebraicClosure k))) c ≫ g) = g :=
    Sigma.hom_ext _ _ fun c ↦ by simp
  refine ⟨PrimeSpectrum B, inferInstance,
    fun c ↦ Sigma.ι (fun _ : PrimeSpectrum B ↦ Spec (.of (AlgebraicClosure k))) c ≫ g,
    fun c ↦ ?_, ?_⟩
  · simp only [g, Category.assoc, ι_sigmaSpec_assoc]
    erw [pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact congrFun (e.commutes x) c
  · rw [hg]
    have : IsIso (CommRingCat.ofHom φ.toRingHom) :=
      inferInstanceAs (IsIso φ.toCommRingCatIso.hom)
    infer_instance

/-- **The geometric fibre of a finite reduced scheme over a perfect field.** If `Z₀` is finite
and reduced over the perfect field `k`, its geometric fibre `Z₀ ×_k k̄` is a finite disjoint union
of copies of `Spec k̄`, by sections of its structure morphism to `Spec k̄`: `Z₀` is the spectrum
of the finite reduced, hence étale, `k`-algebra `Γ(Z₀)`
(`AlgebraicGeometry.exists_isIso_sigmaDesc_geometricFiber_SpecMap`). -/
theorem exists_isIso_sigmaDesc_geometricFiber_of_isFinite [PerfectField k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k)) [IsFinite f] [IsReduced Z] :
    ∃ (n : ℕ) (t : Fin n → (Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber)),
      (∀ i, t i ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _) ∧ IsIso (Sigma.desc t) := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  let φ₀ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let : Algebra k Γ(Z, ⊤) := φ₀.hom.toAlgebra
  have : Module.Finite k Γ(Z, ⊤) :=
    RingHom.Finite.comp f.finite_appTop (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.Etale.of_isReduced_of_perfectField k Γ(Z, ⊤)
  obtain ⟨C, _, t, ht, hiso⟩ := exists_isIso_sigmaDesc_geometricFiber_SpecMap (k := k) Γ(Z, ⊤)
  have hf : Z.isoSpec.inv ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤))) := by
    rw [← Category.comp_id f, ← toSpecΓ_SpecMap_ΓSpecIso_inv, Scheme.toSpecΓ_naturality_assoc,
      Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp]
    rfl
  let m := Scheme.Hom.geometricFiberMap Z.isoSpec.inv hf
  have : IsIso m := ⟨Scheme.Hom.geometricFiberMap Z.isoSpec.hom
    (by rw [← hf, Iso.hom_inv_id_assoc]), by
      rw [← Scheme.Hom.geometricFiberMap_comp]
      simp, by
      rw [← Scheme.Hom.geometricFiberMap_comp]
      simp⟩
  obtain ⟨n, ⟨ε⟩⟩ := Finite.exists_equiv_fin C
  refine ⟨n, fun i ↦ t (ε.symm i) ≫ m, fun i ↦ by simp [m, ht], ?_⟩
  have : Sigma.desc (fun i ↦ t (ε.symm i) ≫ m) =
      (Sigma.reindex ε.symm (fun _ : C ↦ Spec (.of (AlgebraicClosure k)))).hom ≫
        Sigma.desc t ≫ m :=
    Sigma.hom_ext _ _ fun i ↦ by
      refine Eq.trans ?_ (Sigma.ι_reindex_hom_assoc ε.symm
        (fun _ : C ↦ Spec (.of (AlgebraicClosure k))) i (Sigma.desc t ≫ m)).symm
      simp
  rw [this]
  infer_instance

end AlgebraicGeometry
