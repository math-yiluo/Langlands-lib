/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Universal homeomorphisms of rings

An algebra `B` over `A` is a *universal homeomorphism* if `Spec B ⟶ Spec A` is one. We record
the basic consequences at the level of rings: `B` is integral over `A`, the map on prime spectra
is bijective, and the notion is stable under base change and passes to intermediate integral
subalgebras.

## Main definitions

- `Algebra.IsUniversalHomeomorphism`: the class of `A`-algebras `B` such that
  `Spec B ⟶ Spec A` is a universal homeomorphism.

## Main statements

- `Algebra.IsUniversalHomeomorphism.tensorProduct`: stability under base change.
- `Algebra.IsUniversalHomeomorphism.of_subalgebra`: if `B` is a universal homeomorphism over
  `A` and `B₀ ⊆ B` is an `A`-subalgebra, then so is `B₀`.
- `AlgebraicGeometry.isHomeomorph_pullback_fst_of_isPurelyInseparable`: base change along a
  purely inseparable field extension is a homeomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- If `g ≫ h` is universally injective and `g` is surjective, then `h` is universally
injective. -/
lemma UniversallyInjective.of_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [UniversallyInjective (g ≫ h)] [Surjective g] : UniversallyInjective h := by
  rw [UniversallyInjective.iff_diagonal]
  have hΔ : Surjective (pullback.diagonal (g ≫ h)) := (UniversallyInjective.iff_diagonal _).mp ‹_›
  let m : pullback (g ≫ h) (g ≫ h) ⟶ pullback h h :=
    pullback.map (g ≫ h) (g ≫ h) h h g g (𝟙 _) (by simp) (by simp)
  have hm : Surjective m :=
    MorphismProperty.pullbackMap (P := @Surjective) ‹_› ‹_› rfl rfl
  have hcomm : pullback.diagonal (g ≫ h) ≫ m = g ≫ pullback.diagonal h := by
    apply pullback.hom_ext <;> simp [m]
  constructor
  intro z
  obtain ⟨w, rfl⟩ := hm.surj z
  obtain ⟨b, rfl⟩ := hΔ.surj w
  exact ⟨g b, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]⟩

end AlgebraicGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- An `A`-algebra `B` is a universal homeomorphism if `Spec B ⟶ Spec A` is one. -/
class Algebra.IsUniversalHomeomorphism : Prop where
  isUniversalHomeomorphism :
    AlgebraicGeometry.IsUniversalHomeomorphism
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))

namespace AlgebraicGeometry

namespace Algebra.IsUniversalHomeomorphism

attribute [instance] _root_.Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism

variable [Algebra.IsUniversalHomeomorphism A B]

instance isIntegral : Algebra.IsIntegral A B := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap A B))) := inferInstance
  rw [IsIntegralHom.SpecMap_iff] at this
  exact (algebraMap_isIntegral_iff (R := A) (A := B)).mp this

lemma comap_bijective : Function.Bijective (PrimeSpectrum.comap (algebraMap A B)) :=
  ⟨(Spec.map (CommRingCat.ofHom (algebraMap A B))).injective,
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).surjective⟩

lemma comap_injective : Function.Injective (PrimeSpectrum.comap (algebraMap A B)) :=
  (comap_bijective A B).1

lemma comap_surjective : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) :=
  (comap_bijective A B).2

/-- Universal homeomorphisms of rings are stable under base change. -/
instance tensorProduct (A' : Type u) [CommRing A'] [Algebra A A'] :
    Algebra.IsUniversalHomeomorphism A' (A' ⊗[A] B) where
  isUniversalHomeomorphism := by
    have : Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B))) =
        (pullbackSpecIso A A' B).inv ≫ pullback.fst _ _ := by
      rw [pullbackSpecIso_inv_fst]
      rfl
    rw [this]
    infer_instance

variable {A B}

/-- If `B` is a universal homeomorphism over `A`, then so is every `A`-subalgebra of `B`. -/
lemma of_subalgebra (B₀ : Subalgebra A B) : Algebra.IsUniversalHomeomorphism A B₀ where
  isUniversalHomeomorphism := by
    have hint : Algebra.IsIntegral A B₀ := by
      constructor
      intro x
      have := Algebra.IsIntegral.isIntegral (R := A) (x : B)
      rwa [← isIntegral_algebraMap_iff (A := B₀) (B := B)]
    have hint' : Algebra.IsIntegral B₀ B :=
      Algebra.IsIntegral.tower_top (R := A) (S := B₀) (T := B)
    have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B₀ B)) :=
      Algebra.IsIntegral.comap_surjective B₀ B
    -- `Spec B ⟶ Spec B₀` is surjective, `Spec B ⟶ Spec A` is a universal homeomorphism.
    let g : Spec (.of B) ⟶ Spec (.of B₀) := Spec.map (CommRingCat.ofHom (algebraMap B₀ B))
    let h : Spec (.of B₀) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B₀))
    have hgh : g ≫ h = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
      simp only [g, h, ← Spec.map_comp]
      congr 1
    have hg : Surjective g := ⟨hsurj⟩
    have h1 : IsIntegralHom h := IsIntegralHom.SpecMap_iff.mpr
      ((algebraMap_isIntegral_iff (R := A) (A := B₀)).mpr hint)
    have h2 : Surjective h := by
      have : Surjective (g ≫ h) := hgh ▸ inferInstance
      exact Surjective.of_comp g h
    have h3 : UniversallyInjective h := by
      have : UniversallyInjective (g ≫ h) := hgh ▸ inferInstance
      exact UniversallyInjective.of_comp g h
    exact { }

end Algebra.IsUniversalHomeomorphism

/-- A purely inseparable extension of fields `L/K` is a universal homeomorphism: `Spec L ⟶ Spec K`
is integral, surjective onto the point `Spec K`, and universally injective, since two field
points `Spec Ω ⟶ Spec L` over `Spec K` are given by two embeddings `L ⟶ Ω` which agree on `K`,
hence agree. -/
instance _root_.Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable (K L : Type u) [Field K]
    [Field L] [Algebra K L] [IsPurelyInseparable K L] : Algebra.IsUniversalHomeomorphism K L where
  isUniversalHomeomorphism := by
    let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
    have h1 : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr
      ((algebraMap_isIntegral_iff (R := K) (A := L)).mpr inferInstance)
    have h2 : Surjective f := ⟨fun x ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
    have h3 : UniversallyInjective f := by
      refine ((tfae_universallyInjective f).out 2 1).mp ?_
      intro Ω _ g₁ g₂ hg
      rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
      simp only [f, ← Spec.map_comp] at hg
      have h := Spec.map_injective hg
      congr 1
      ext x
      exact congr($(IsPurelyInseparable.injective_comp_algebraMap K L Ω
        (a₁ := (Spec.preimage g₁).hom) (a₂ := (Spec.preimage g₂).hom)
        (congrArg CommRingCat.Hom.hom h)) x)
    exact { }

/-- **Base change along a purely inseparable extension is a homeomorphism.** For a purely
inseparable extension `k'/k` and a `k`-scheme `f: X ⟶ Spec k`, the projection
`X_{k'} = X ×_{Spec k} Spec k' ⟶ X` is a homeomorphism: it is the base change of the universal
homeomorphism `Spec k' ⟶ Spec k`. -/
theorem isHomeomorph_pullback_fst_of_isPurelyInseparable (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsPurelyInseparable k k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsHomeomorph (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base :=
  Scheme.Hom.isHomeomorph _

end AlgebraicGeometry
