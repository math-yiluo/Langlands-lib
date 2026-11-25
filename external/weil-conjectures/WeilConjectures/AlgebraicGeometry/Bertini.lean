/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.BertiniAux
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Curves through prescribed points preserving a finite étale cover

Let `X₀` be a smooth geometrically connected affine scheme of dimension `d ≥ 2` over a finite
field `k₀`, with geometric fiber `X = X₀ ×_{k₀} k̄`, let `T ⟶ X` be a connected finite étale
cover and `S` a nonempty finite set of `k̄`-points of `X`. A Bertini argument produces a smooth
connected closed affine curve `C ⊆ X` through `S` over which `T` stays connected; the curve is
defined over a finite extension of `k₀`, that is, it is stable under a power of the geometric
Galois Frobenius of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback`: blueprint
  `lemma-curve-preserving-finite-cover--1`.

## Implementation notes

The blueprint lemma is stated over an arbitrary algebraically closed field `k`, with a
complement on descent when `k = 𝔽̄_q`. Only the case `k = 𝔽̄_q` is used, and it is stated here
directly for the geometric fiber of a scheme `X₀` over `𝔽_q`: "defined over a finite extension
`𝔽_{qᵐ}`" is rendered as stability of `C` under the `m`-th power of the geometric Galois Frobenius
`𝟙 × σ` of `X`, an automorphism `φ` of `C` with `φ ≫ i = i ≫ (𝟙 × σ)ᵐ`; by Galois descent, this
is the same as a model of `C ⟶ X` over `𝔽_{qᵐ}`. Dimensions are relative dimensions of smooth
morphisms.

## References

- [Stacks Project, Tags 0FD5, 0FD6 and 0G4F](https://stacks.math.columbia.edu/tag/0FD5), the
  Bertini theorems the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- **Curves through prescribed points preserving a finite cover**
(blueprint: `lemma-curve-preserving-finite-cover--1`). Let `f : X₀ ⟶ Spec k₀` be a smooth
geometrically connected affine scheme of relative dimension `d ≥ 2` over a finite field, with
geometric fiber `X`, let `π : T ⟶ X` be a finite étale morphism with `T` connected, and let `S`
be a nonempty finite set of `k̄`-points of `X`. There is a closed immersion `i : C ⟶ X` of a
smooth connected affine curve over `k̄` through every point of `S`, such that `T ×_X C` is
connected and `C` is stable under some power `(𝟙 × σ)ᵐ`, `m ≥ 1`, of the geometric Galois
Frobenius of `X`. -/
theorem exists_isClosedImmersion_connectedSpace_pullback {k₀ : Type u} [Field k₀] [Finite k₀]
    {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) [IsAffine X₀] {d : ℕ} (hd : 2 ≤ d)
    [SmoothOfRelativeDimension d f] [GeometricallyConnected f] {T : Scheme.{u}}
    (π : T ⟶ f.geometricFiber) [IsFinite π] [Etale π] [ConnectedSpace T]
    (S : Finset (Spec (.of (AlgebraicClosure k₀)) ⟶ f.geometricFiber)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ f.geometricFiber), IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1 (i ≫ f.geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧ ConnectedSpace ↑(pullback π i) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C,
        φ.hom ≫ i = i ≫ (f.geometricGaloisFrobenius ^ m).asIso.hom := by
  classical
  let := Fintype.ofFinite k₀
  obtain ⟨R, _, _, eR, heR⟩ := exists_iso_Spec_of_isAffine f
  set K := AlgebraicClosure k₀
  set A := K ⊗[k₀] R
  set e := f.geometricFiberIsoSpec eR heR
  -- `Spec A` is smooth of relative dimension `d` and connected
  have hsm : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    have h : SmoothOfRelativeDimension d f.geometricFiberToAlgebraicClosure :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
        (IsPullback.of_hasPullback f _) ‹_›
    rw [← f.geometricFiberIsoSpec_hom_algebraMap eR heR] at h
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension d) _ _).mp h
  have hX : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) _ _ _
      (IsPullback.of_hasPullback _ _)
  have hA : ConnectedSpace (Spec (.of A)) := Scheme.connectedSpace_of_iso e
  have : ConnectedSpace (PrimeSpectrum A) := hA
  -- the finite étale cover `T = Spec B`
  have : IsAffine f.geometricFiber := IsAffine.of_isIso e.hom
  have : IsAffine T := isAffine_of_isAffineHom π
  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of A ⟶ Γ(T, ⊤), Spec.map φ = T.isoSpec.inv ≫ π ≫ e.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  let : Algebra A Γ(T, ⊤) := φ.hom.toAlgebra
  let : Algebra K Γ(T, ⊤) := (φ.hom.comp (algebraMap K A)).toAlgebra
  have : IsScalarTower K A Γ(T, ⊤) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale A Γ(T, ⊤) := by
    have h : Etale (Spec.map φ) := by
      rw [hφ]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h
    exact RingHom.etale_algebraMap.mp h
  have : Module.Finite A Γ(T, ⊤) := by
    have h : IsFinite (Spec.map φ) := by
      rw [hφ]
      infer_instance
    rw [IsFinite.SpecMap_iff] at h
    exact h
  have hB : ConnectedSpace (Spec Γ(T, ⊤)) := Scheme.connectedSpace_of_iso T.isoSpec
  have : ConnectedSpace (PrimeSpectrum Γ(T, ⊤)) := hB
  -- the points of `S` as ring homomorphisms `A →+* K`
  let ψ (s : Spec (.of K) ⟶ f.geometricFiber) : A →+* K := (Spec.preimage (s ≫ e.hom)).hom
  have hψ (s : Spec (.of K) ⟶ f.geometricFiber)
      (hs : s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _) :
      (ψ s).comp (algebraMap K A) = RingHom.id K := by
    have h : Spec.map (CommRingCat.ofHom (algebraMap K A) ≫ Spec.preimage (s ≫ e.hom)) =
        Spec.map (𝟙 _) := by
      rw [Spec.map_comp, Spec.map_preimage, Category.assoc,
        Scheme.Hom.geometricFiberIsoSpec_hom_algebraMap, hs, Spec.map_id]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨J, hJfg, hJS, hdom, hsm1, hconn⟩ :=
    exists_ideal_smoothOfRelativeDimension_one_connectedSpace_pullback (B := Γ(T, ⊤)) hd hsm
      (ψ '' S) (S.finite_toSet.image _) ((Finset.coe_nonempty.mpr hS).image _)
      (by rintro _ ⟨s, hs, rfl⟩; exact hψ s (hS' s hs))
  -- the Frobenius
  obtain ⟨m, hm, hJm⟩ :=
    hJfg.exists_map_pow_eq _ (exists_geometricFrobeniusTensor_pow_apply_eq_self k₀ R)
  obtain ⟨Φ, hΦ⟩ := exists_iso_comp_eq_of_map_eq e (f.geometricGaloisFrobenius ^ m).asIso _
    (f.geometricGaloisFrobenius_pow_hom_comp_geometricFiberIsoSpec_hom eR heR m) J hJm
  have he : e.inv ≫ f.geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    rw [Iso.inv_comp_eq, Scheme.Hom.geometricFiberIsoSpec_hom_algebraMap]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨Spec (.of (A ⧸ J)), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ e.inv,
    inferInstance, inferInstance, ?_, IrreducibleSpace.connectedSpace _, ?_, ?_, m, hm, Φ, hΦ⟩
  · rw [Category.assoc, he, ← Spec.map_comp]
    exact hsm1
  · intro s hs
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (ψ s)
      fun a ha ↦ hJS _ ⟨s, hs, rfl⟩ ha)), ?_⟩
    have h : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom (Ideal.Quotient.lift J
        (ψ s) fun a ha ↦ hJS _ ⟨s, hs, rfl⟩ ha) = Spec.preimage (s ≫ e.hom) := by
      exact CommRingCat.hom_ext (Ideal.Quotient.lift_comp_mk _ _ _)
    rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_preimage, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · have hP := (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap A Γ(T, ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J))))).of_iso (Iso.refl _) T.isoSpec.symm
      (Iso.refl _) e.symm (fst' := pullback.fst _ _ ≫ T.isoSpec.inv) (snd' := pullback.snd _ _)
      (f' := π) (g' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ e.inv)
      (by simp) (by simp) ?_ (by simp)
    · exact Scheme.connectedSpace_of_iso hP.isoPullback
    · rw [Iso.symm_hom, Iso.symm_hom]
      exact (congrArg (· ≫ e.inv) hφ).trans (by simp)

end AlgebraicGeometry.Scheme.Hom
