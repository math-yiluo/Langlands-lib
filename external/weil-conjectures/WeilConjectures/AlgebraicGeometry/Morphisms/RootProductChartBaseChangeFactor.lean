/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Pi

/-! Open factors of a base-changed product root chart.

## References

* Stacks Project, Tag 0EYI, preliminary root-chart base change calculation
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A product root chart has open generic factors after any extension of its coefficient ring.
-/
theorem rootProductChart_baseChange_factor {L N : Scheme.{u}} (n : N ⟶ L)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (m : ℕ) (e : Fin m → ℕ)
    (α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (∀ k : Fin m,
        AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))) =
          pullback.snd n φ)
    (K : Type u) [Field K] (θ : R →+* K) (k : Fin m) :
    ∃ g : Spec (CommRingCat.of
        (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e k - Polynomial.C (θ f)))) ⟶
          pullback n (Spec.map (CommRingCat.ofHom θ) ≫ φ),
      IsOpenImmersion g ∧
      g ≫ pullback.snd n (Spec.map (CommRingCat.ofHom θ) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap K
          (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e k - Polynomial.C (θ f)))))  := by
  classical
  let := θ.toAlgebra
  let D (i : Fin m) := AdjoinRoot ((Polynomial.X : Polynomial R) ^ e i - Polynomial.C f)
  let E (i : Fin m) :=
    AdjoinRoot ((Polynomial.X : Polynomial K) ^ e i - Polynomial.C (θ f))
  let ε (i : Fin m) : TensorProduct R K (D i) ≃ₐ[K] E i := by
    let p := (Polynomial.X : Polynomial R) ^ e i - Polynomial.C f
    let q := p.map (Algebra.TensorProduct.includeRight :
      R →ₐ[R] TensorProduct R K R).toRingHom
    let r := (Polynomial.X : Polynomial K) ^ e i - Polynomial.C (θ f)
    have hqr : q.map (Algebra.TensorProduct.rid R K K) = r := by
      simp [q, p, r, Polynomial.map_sub, Polynomial.map_pow]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
      (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R K K) q r (hqr ▸ Associated.refl r))
  let εall : TensorProduct R K (∀ i, D i) ≃ₐ[K] (∀ i, E i) :=
    (Algebra.TensorProduct.piRight R K K D).trans (AlgEquiv.piCongrRight ε)
  let fD := Spec.map (CommRingCat.ofHom (algebraMap R (∀ i, D i)))
  let r := Spec.map (CommRingCat.ofHom θ)
  have ha : α.inv ≫ pullback.snd n φ = fD := by
    rw [← hα, Iso.inv_hom_id_assoc]
  have hchart : IsPullback (α.inv ≫ pullback.fst n φ) fD n φ :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, ha]⟩
      α.symm rfl ha
  have hsquare := (IsPullback.of_hasPullback fD r).paste_horiz hchart
  let γ := hsquare.isoPullback
  let κ := Scheme.Spec.mapIso εall.toRingEquiv.toCommRingCatIso.op
  let ξ := κ ≪≫ (pullbackSpecIso R K (∀ i, D i)).symm ≪≫
    pullbackSymmetry r fD ≪≫ γ
  let i := Spec.map (CommRingCat.ofHom (Pi.evalRingHom E k))
  have hξ : ξ.hom ≫ pullback.snd n (r ≫ φ) =
      Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, E i))) := by
    simp only [ξ, γ, r, fD, Iso.trans_hom, Category.assoc, hsquare.isoPullback_hom_snd,
      pullbackSymmetry_hom_comp_snd, Iso.symm_hom]
    change κ.hom ≫ (pullbackSpecIso R K (∀ i, D i)).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K))) _ = _
    rw [pullbackSpecIso_inv_fst']
    change Spec.map (CommRingCat.ofHom εall.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K _)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact εall.toAlgHom.comp_algebraMap
  refine ⟨i ≫ ξ.hom, inferInstance, ?_⟩
  rw [Category.assoc, hξ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl



end AlgebraicGeometry.Scheme
