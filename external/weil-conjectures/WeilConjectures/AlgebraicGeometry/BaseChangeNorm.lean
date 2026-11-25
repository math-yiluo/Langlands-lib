/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.RingTheory.Localization.NormTrace

/-!
# Norms along the base change to a finite field extension

Let `k'/k` be a finite field extension, `X` a `k`-scheme and `π : Y = X ×_k k' ⟶ X` the base
change. For an affine open `U` of `X`, the ring `Γ(Y, π⁻¹ U) = Γ(X, U) ⊗_k k'` is finite free
over `Γ(X, U)`, so there is a norm map `Γ(Y, π⁻¹ U) ⟶ Γ(X, U)`
(`AlgebraicGeometry.Scheme.Hom.normAt`). It is multiplicative, compatible with restriction to
basic opens, and the norm of a function `a` does not vanish at `x` if and only if `a` does not
vanish at any point of the fibre `π⁻¹ x`.

We also record that an open `W` of `X` is affine as soon as `π⁻¹ W` is affine, by descent of
affine morphisms along the faithfully flat `Spec k' ⟶ Spec k`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.normAt`: the norm `Γ(Y, π⁻¹ U) ⟶ Γ(X, U)`.

## Main statements

- `AlgebraicGeometry.mem_basicOpen_normAt`: the non-vanishing locus of a norm.
- `AlgebraicGeometry.normAt_map_of_eq_basicOpen`: compatibility with basic opens.
- `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage`: affineness descends.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The norm `Γ(Y, π⁻¹ U) ⟶ Γ(X, U)` along a morphism `π : Y ⟶ X`, for the `Γ(X, U)`-algebra
structure given by `π`. It is meaningful when `Γ(Y, π⁻¹ U)` is finite free over `Γ(X, U)`, as is
the case for the base change to a finite field extension and `U` affine. -/
def Scheme.Hom.normAt {X Y : Scheme.{u}} (π : Y ⟶ X) (U : X.Opens) :
    Γ(Y, π ⁻¹ᵁ U) →* Γ(X, U) :=
  letI := (π.app U).hom.toAlgebra
  Algebra.norm Γ(X, U)

lemma surjective_specMap_algebraMap_of_field {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Nonempty (Spec (.of k')) := inferInstanceAs (Nonempty (PrimeSpectrum k'))
  exact ⟨fun x ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [Module.Finite k k']
  {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {π : Y ⟶ X} {q : Y ⟶ Spec (.of k')}
  (H : IsPullback π q f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))

include H

lemma isFinite_of_isPullback_spec : IsFinite π := by
  refine MorphismProperty.of_isPullback (P := @IsFinite) H.flip ?_
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma flat_of_isPullback_spec : Flat π := by
  refine MorphismProperty.of_isPullback (P := @Flat) H.flip ?_
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

omit [Module.Finite k k'] in
lemma surjective_of_isPullback_spec : Surjective π :=
  MorphismProperty.of_isPullback (P := @Surjective) H.flip surjective_specMap_algebraMap_of_field


/-- Over an affine open `U`, the ring `Γ(Y, π⁻¹ U)` is finite free over `Γ(X, U)`: it is
`Γ(X, U) ⊗_k k'`. -/
lemma free_finite_app {U : X.Opens} (hU : IsAffineOpen U) :
    letI := (π.app U).hom.toAlgebra
    Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := by
  have hUY : π ⁻¹ᵁ U = π ⁻¹ᵁ U ⊓ q ⁻¹ᵁ ⊤ := by simp
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (by simp) (by simp) hUY (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hpo := (isIso_pushoutSection_iff ..).mp this
  set eA := Scheme.ΓSpecIso (.of k)
  set eB := Scheme.ΓSpecIso (.of k')
  have happ : π.appLE U (π ⁻¹ᵁ U) (by simp) = π.app U := by
    rw [Scheme.Hom.app_eq_appLE]
  rw [happ] at hpo
  have hpo' := hpo.of_iso eA (Iso.refl _) eB (Iso.refl _) (f' := eA.inv ≫ f.appLE ⊤ U (by simp))
    (g' := CommRingCat.ofHom (algebraMap k k')) (inl' := π.app U)
    (inr' := eB.inv ≫ q.appLE ⊤ (π ⁻¹ᵁ U) (by simp)) (by simp) (by
      rw [show (Spec.map (CommRingCat.ofHom (algebraMap k k'))).appLE ⊤ ⊤ (by simp) =
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))).appTop by
          rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl,
        Scheme.ΓSpecIso_naturality]) (by simp) (by simp)
  let : Algebra k Γ(X, U) := (eA.inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Algebra k' Γ(Y, π ⁻¹ᵁ U) := (eB.inv ≫ q.appLE ⊤ (π ⁻¹ᵁ U) (by simp)).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  let : Algebra k Γ(Y, π ⁻¹ᵁ U) :=
    ((eA.inv ≫ f.appLE ⊤ U (by simp)) ≫ π.app U).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k k' Γ(Y, π ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' (by
    change ((eA.inv ≫ f.appLE ⊤ U _) ≫ π.app U).hom = ((CommRingCat.ofHom (algebraMap k k')) ≫
      (eB.inv ≫ q.appLE ⊤ (π ⁻¹ᵁ U) _)).hom
    rw [hpo'.w])
  have hpush : Algebra.IsPushout k k' Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
    (CommRingCat.isPushout_iff_isPushout).mp hpo'.flip
  have e := (hpush.symm).equiv
  exact ⟨.of_equiv e.toLinearEquiv, .equiv e.toLinearEquiv⟩

/-- **The non-vanishing locus of a norm.** For `U` affine and `a ∈ Γ(Y, π⁻¹ U)`, the norm of `a`
does not vanish at `x ∈ U` if and only if `a` does not vanish at any point over `x`. -/
lemma mem_basicOpen_normAt {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(Y, π ⁻¹ᵁ U)) {x : X}
    (hx : x ∈ U) : x ∈ X.basicOpen (π.normAt U a) ↔ ∀ y, π y = x → y ∈ Y.basicOpen a := by
  obtain ⟨hfree, hfin⟩ := free_finite_app H hU
  have := isFinite_of_isPullback_spec H
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  obtain ⟨z, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hpt (w : Spec Γ(Y, π ⁻¹ᵁ U)) :
      π (hV.fromSpec w) = hU.fromSpec (PrimeSpectrum.comap (π.app U).hom w) := by
    have := congrArg (fun g ↦ g w) (IsAffineOpen.SpecMap_appLE_fromSpec π hU hV le_rfl)
    simp only [Scheme.Hom.comp_apply, Spec.map_apply] at this
    rw [← this, ← Scheme.Hom.app_eq_appLE]
  change z ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen _ ↔ _
  rw [hU.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
  let := (π.app U).hom.toAlgebra
  refine (Algebra.norm_notMem_iff z.asIdeal a).trans ⟨fun h y hy ↦ ?_, fun h Q hQ hQz ↦ ?_⟩
  · obtain ⟨w, rfl⟩ : y ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      change π y ∈ U
      rw [hy]
      exact (Set.ext_iff.mp hU.range_fromSpec _).mp ⟨z, rfl⟩
    change w ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen a
    rw [hV.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
    refine h w.asIdeal w.isPrime ?_
    rw [hpt] at hy
    exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective hy)
  · have := h (hV.fromSpec ⟨Q, hQ⟩) (by
      rw [hpt]
      congr 1
      exact PrimeSpectrum.ext hQz)
    change (⟨Q, hQ⟩ : PrimeSpectrum _) ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen a at this
    rwa [hV.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen] at this

/-- **Affineness descends along a finite field extension.** If the preimage of an open `W`
of `X` in `Y = X ×_k k'` is affine, then `W` is affine. -/
lemma isAffineOpen_of_isAffineOpen_preimage {W : X.Opens} (hW : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsAffineOpen W := by
  have hsq := (isPullback_morphismRestrict π W).paste_vert H
  have : IsAffine (π ⁻¹ᵁ W).toScheme := hW
  have := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : IsAffineHom (W.ι ≫ f) := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq.flip
    ⟨⟨surjective_specMap_algebraMap_of_field, hflat⟩, inferInstance⟩ inferInstance
  have : IsAffine W := isAffine_of_isAffineHom (W.ι ≫ f)
  exact this

/-- **Norms commute with restriction to basic opens.** For `U` affine, `r ∈ Γ(X, U)` and
`V = D(r)`, the norm of the restriction of `a ∈ Γ(Y, π⁻¹ U)` to `π⁻¹ V` is the restriction of
the norm of `a`. -/
lemma normAt_map_of_eq_basicOpen {U V : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (hV : V = X.basicOpen r) (a : Γ(Y, π ⁻¹ᵁ U)) :
    π.normAt V (Y.presheaf.map (homOfLE (π.preimage_mono
      (hV.le.trans (X.basicOpen_le r)))).op a) =
      X.presheaf.map (homOfLE (hV.le.trans (X.basicOpen_le r))).op (π.normAt U a) := by
  subst hV
  obtain ⟨hfree, hfin⟩ := free_finite_app H hU
  have := isFinite_of_isPullback_spec H
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  let : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  let : Algebra Γ(Y, π ⁻¹ᵁ U) Γ(Y, π ⁻¹ᵁ X.basicOpen r) :=
    (Y.presheaf.map (homOfLE (π.preimage_mono (X.basicOpen_le r))).op).hom.toAlgebra
  let : Algebra Γ(X, X.basicOpen r) Γ(Y, π ⁻¹ᵁ X.basicOpen r) :=
    (π.app (X.basicOpen r)).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ X.basicOpen r) :=
    (π.app U ≫ Y.presheaf.map (homOfLE (π.preimage_mono (X.basicOpen_le r))).op).hom.toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, π ⁻¹ᵁ U) Γ(Y, π ⁻¹ᵁ X.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r) Γ(Y, π ⁻¹ᵁ X.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (π.app U ≫ Y.presheaf.map _).hom = (X.presheaf.map _ ≫ π.app _).hom
      rw [π.naturality]
      rfl)
  have : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U) (Submonoid.powers r))
      Γ(Y, π ⁻¹ᵁ X.basicOpen r) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    have e : π ⁻¹ᵁ X.basicOpen r = Y.basicOpen (π.app U r) := Scheme.preimage_basicOpen π r
    have := hU'.isLocalization_basicOpen (π.app U r)
    let ψ := (Y.presheaf.mapIso (eqToIso e).op).commRingCatIsoToRingEquiv
    refine IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (π.app U r))
      { ψ with commutes' := fun x ↦ ?_ }
    change (Y.presheaf.map _ ≫ Y.presheaf.map _) x = Y.presheaf.map _ x
    rw [← Functor.map_comp]
    rfl
  exact Algebra.norm_localization (Rₘ := Γ(X, X.basicOpen r))
    (Sₘ := Γ(Y, π ⁻¹ᵁ X.basicOpen r)) Γ(X, U) (Submonoid.powers r) a

end AlgebraicGeometry
