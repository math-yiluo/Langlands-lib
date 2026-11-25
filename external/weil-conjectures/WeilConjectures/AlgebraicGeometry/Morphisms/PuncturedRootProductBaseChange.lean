/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Base change for punctured products of root algebras

## References

* Stacks Project, Tag 0EYG, descent paragraph
* Stacks Project, Tag 05N9
-/

@[expose] public section

noncomputable section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The finite product of the root algebras `R[X] / (X ^ e k - g)`. -/
abbrev puncturedRootProductRing (R : CommRingCat.{u}) (g : R) (m : ℕ)
    (e : Fin m → ℕ) :=
  ∀ k : Fin m, AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C g)

/-- The basic open defined by the image of the prescribed coefficient. -/
abbrev puncturedRootProductOpen (R : CommRingCat.{u}) (g : R) (m : ℕ)
    (e : Fin m → ℕ) : (Spec (.of (puncturedRootProductRing R g m e))).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R (puncturedRootProductRing R g m e) g)

/-- The structural map of the explicitly constructed punctured chart. -/
abbrev puncturedRootProductMap (R : CommRingCat.{u}) (g : R) (m : ℕ)
    (e : Fin m → ℕ) : (puncturedRootProductOpen R g m e).toScheme ⟶ Spec R :=
  (puncturedRootProductOpen R g m e).ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (puncturedRootProductRing R g m e)))

/-- Punctured products of root algebras are affine and finitely presented, and their
formation commutes with arbitrary base change. -/
theorem punctured_root_product_base_change
    (R : CommRingCat.{u}) (g : R) (m : ℕ) (e : Fin m → ℕ) :
    IsAffineHom (puncturedRootProductMap R g m e) ∧
    LocallyOfFinitePresentation (puncturedRootProductMap R g m e) ∧
    ∀ (S : CommRingCat.{u}) (φ : R →+* S),
      ∃ δ : pullback (puncturedRootProductMap R g m e)
          (Spec.map (CommRingCat.ofHom φ)) ≅
          (puncturedRootProductOpen S (φ g) m e).toScheme,
        δ.hom ≫ puncturedRootProductMap S (φ g) m e =
          pullback.snd (puncturedRootProductMap R g m e)
            (Spec.map (CommRingCat.ofHom φ))  := by
  classical
  let A := puncturedRootProductRing R g m e
  let V := puncturedRootProductOpen R g m e
  let fA := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : IsAffine V.toScheme :=
    IsAffineOpen.Spec_basicOpen (R := .of A) (algebraMap R A g)
  have : LocallyOfFinitePresentation fA := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    change (algebraMap R A).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro S φ
  let := φ.toAlgebra
  let D (i : Fin m) := AdjoinRoot ((Polynomial.X : Polynomial R) ^ e i - Polynomial.C g)
  let E (i : Fin m) :=
    AdjoinRoot ((Polynomial.X : Polynomial S) ^ e i - Polynomial.C (φ g))
  let ε (i : Fin m) : TensorProduct R S (D i) ≃ₐ[S] E i := by
    let p := (Polynomial.X : Polynomial R) ^ e i - Polynomial.C g
    let q := p.map (Algebra.TensorProduct.includeRight :
      R →ₐ[R] TensorProduct R S R).toRingHom
    let r := (Polynomial.X : Polynomial S) ^ e i - Polynomial.C (φ g)
    have hqr : q.map (Algebra.TensorProduct.rid R S S) = r := by
      simp [q, p, r, Polynomial.map_sub, Polynomial.map_pow]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
      (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R S S) q r
        (hqr ▸ Associated.refl r))
  let εall : TensorProduct R S (∀ i, D i) ≃ₐ[S] (∀ i, E i) :=
    (Algebra.TensorProduct.piRight R S S D).trans (AlgEquiv.piCongrRight ε)
  let κ := Scheme.Spec.mapIso εall.toRingEquiv.toCommRingCatIso.op
  let b := Spec.map (CommRingCat.ofHom φ)
  let fE := Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, E i)))
  let ξ := κ ≪≫ (pullbackSpecIso R S (∀ i, D i)).symm ≪≫
    pullbackSymmetry b fA
  have hξ : ξ.hom ≫ pullback.snd fA b = fE := by
    simp only [ξ, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      Iso.symm_hom]
    change κ.hom ≫ (pullbackSpecIso R S (∀ i, D i)).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) _ = _
    rw [pullbackSpecIso_inv_fst']
    change Spec.map (CommRingCat.ofHom εall.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S _)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact εall.toAlgHom.comp_algebraMap
  let froot := ξ.hom ≫ pullback.fst fA b
  have Hroot : IsPullback froot fE fA b := by
    apply IsPullback.of_iso_pullback _ ξ rfl hξ
    constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc, hξ]
  have hVR : V = fA ⁻¹ᵁ PrimeSpectrum.basicOpen g :=
    (PrimeSpectrum.comap_basicOpen (algebraMap R A) g).symm
  have hVS : froot ⁻¹ᵁ V = puncturedRootProductOpen S (φ g) m e := by
    rw [hVR, ← Scheme.Hom.comp_preimage, Hroot.w, Scheme.Hom.comp_preimage]
    change fE ⁻¹ᵁ PrimeSpectrum.basicOpen (φ g) = _
    exact PrimeSpectrum.comap_basicOpen (algebraMap S (∀ i, E i)) (φ g)
  let H := (isPullback_morphismRestrict froot V).paste_vert Hroot
  let η := (Spec (.of (∀ i, E i))).isoOfEq hVS
  refine ⟨H.isoPullback.symm ≪≫ η, ?_⟩
  change (H.isoPullback.inv ≫ η.hom) ≫
    (puncturedRootProductOpen S (φ g) m e).ι ≫ fE = _
  rw [Category.assoc, Scheme.isoOfEq_hom_ι_assoc]
  exact H.isoPullback_inv_snd

end AlgebraicGeometry.Scheme
