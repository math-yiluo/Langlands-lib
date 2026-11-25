/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineNormalizationCoproduct
import WeilConjectures.AlgebraicGeometry.Morphisms.ReducedArtinianAffineNormalizationCharts

/-! # Integral-closure charts for reduced Artinian tensor algebras

## References

* Stacks Project, Tags 035H and 0307
-/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite affine coproduct with reduced Artinian base changes has normalization
charts given by integral closures in its residue fields. -/
theorem reduced_artinian_tensor_normalization_charts
    (B A : CommRingCat.{u}) [Algebra B A]
    (r : ℕ) (E : Fin r → Type u) [∀ i, CommRing (E i)] [∀ i, Algebra B (E i)]
    (hD : ∀ i, IsArtinianRing (E i ⊗[B] A) ∧ _root_.IsReduced (E i ⊗[B] A))
    (X : Scheme.{u}) (p : X ⟶ Spec B)
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap B (E i)))) = p) :
    let a := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B A)))
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ x : a.normalization,
    ∃ (i : Fin r) (P : Ideal (E i ⊗[B] A)) (hP : P.IsMaximal),
    letI := hP
    let F := (E i ⊗[B] A) ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∃ c : Spec (CommRingCat.of S) ⟶ a.normalization,
      IsOpenImmersion c ∧
      c ≫ a.fromNormalization = Spec.map (CommRingCat.ofHom (algebraMap A S)) ∧
      x ∈ Set.range c := by
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  intro x
  let D (i : Fin r) := E i ⊗[B] A
  let (i : Fin r) : Algebra A (D i) :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom.toAlgebra
  obtain ⟨t, ht⟩ := finite_affine_tensor_base_change B A r E X p e he
  obtain ⟨n, hn⟩ := finite_affine_normalization_coproduct A r D _
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B A)))) t ht
  let N (i : Fin r) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A (D i)))).normalization
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover N).exists_eq (n.inv x)
  have hy' : (Sigma.ι N i ≫ n.hom) y = x := by
    rw [Hom.comp_apply]
    change n.hom ((sigmaOpenCover _).f i y) = x
    rw [hy]
    rw [← Hom.comp_apply, n.inv_hom_id]
    rfl
  let : IsArtinianRing (D i) := (hD i).1
  let : _root_.IsReduced (D i) := (hD i).2
  obtain ⟨P, hP, c, hc, hcomp, hmem⟩ :=
    reduced_artinian_affine_normalization_charts A (D i) y
  refine ⟨i, P, hP, c ≫ Sigma.ι N i ≫ n.hom, ?_, ?_, ?_⟩
  · let := hc
    infer_instance
  · rw [Category.assoc, Category.assoc, hn, hcomp]
  · obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    rw [Hom.comp_apply, hz, hy']

end AlgebraicGeometry.Scheme
