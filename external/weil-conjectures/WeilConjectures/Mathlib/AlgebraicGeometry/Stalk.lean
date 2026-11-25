/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Stalks at generizations

For a specialization `x ⤳ y` in a scheme `X`, the specialization map `𝒪_{X,y} ⟶ 𝒪_{X,x}` is
the localization of `𝒪_{X,y}` at the prime ideal corresponding to `x`, the preimage of the
maximal ideal of `𝒪_{X,x}`; and that prime is the point of `Spec 𝒪_{X,y}` which is sent to `x`
by `Spec 𝒪_{X,y} ⟶ X`.

## Main results

- `IsLocalization.AtPrime.isLocalization_comap_maximalIdeal`: if `S = R_𝔭` and `T = R_𝔮` with
  `𝔮 ⊆ 𝔭`, then `T` is the localization of `S` at the preimage of the maximal ideal of `T`.
- `AlgebraicGeometry.Scheme.isLocalization_stalkSpecializes`: the specialization map of stalks
  is a localization at a prime.
- `AlgebraicGeometry.Scheme.fromSpecStalk_comap_maximalIdeal`: `Spec 𝒪_{X,y} ⟶ X` sends the
  preimage of the maximal ideal of `𝒪_{X,x}` to `x`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

/-- **Localization at a smaller prime.** If `S = R_𝔭` and `T = R_𝔮` are localizations of `R` at
primes `𝔮 ⊆ 𝔭`, with compatible algebra structures, then `T` is the localization of `S` at the
preimage of the maximal ideal of `T`. -/
theorem IsLocalization.AtPrime.isLocalization_comap_maximalIdeal {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [IsLocalRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [IsLocalization.AtPrime S p]
    [IsLocalization.AtPrime T q] :
    IsLocalization.AtPrime T ((maximalIdeal T).comap (algebraMap S T)) := by
  have hT := IsLocalization.isLocalization_of_submonoid_le S T p.primeCompl q.primeCompl
    (fun a ha h ↦ ha (hqp h))
  have hcomap : (maximalIdeal T).comap (algebraMap R T) = q :=
    IsLocalization.AtPrime.under_maximalIdeal T q
  refine IsLocalization.of_le_of_exists_dvd (q.primeCompl.map (algebraMap R S)) _ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ h
    refine ha ?_
    rw [← hcomap]
    change algebraMap R T a ∈ maximalIdeal T
    rw [IsScalarTower.algebraMap_apply R S T]
    exact h
  · intro n hn
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj p.primeCompl n
    refine ⟨algebraMap R S a, ⟨a, fun ha ↦ ?_, rfl⟩, ⟨algebraMap R S s, e.symm⟩⟩
    have hn' : IsUnit (algebraMap S T n) := by
      by_contra h
      exact hn ((mem_maximalIdeal _).2 h)
    have hs : IsUnit (algebraMap S T (algebraMap R S s)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.map_units T (⟨s, fun h ↦ s.2 (hqp h)⟩ : q.primeCompl)
    have : IsUnit (algebraMap R T a) := by
      rw [IsScalarTower.algebraMap_apply R S T, ← e, map_mul]
      exact hn'.mul hs
    rw [← hcomap] at ha
    exact (mem_maximalIdeal _).1 ha this

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **The specialization map of stalks is a localization.** For `x ⤳ y` in a scheme `X`, the
stalk `𝒪_{X,x}` is the localization of `𝒪_{X,y}` at the preimage of the maximal ideal of
`𝒪_{X,x}`: on an affine open `U ∋ y` both are localizations of `Γ(X, U)`, at primes `𝔮 ⊆ 𝔭`. -/
theorem isLocalization_stalkSpecializes {x y : X} (h : x ⤳ y) :
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk x)
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x ∈ U := h.mem_open U.2 hyU
  let : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      (congrArg (fun φ ↦ φ.hom a) (X.presheaf.germ_stalkSpecializes hyU h)).symm
  have hy := hU.isLocalization_stalk ⟨y, hyU⟩
  have hx := hU.isLocalization_stalk ⟨x, hxU⟩
  refine IsLocalization.AtPrime.isLocalization_comap_maximalIdeal
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ?_
  have hxy : hU.primeIdealOf ⟨x, hxU⟩ ⤳ hU.primeIdealOf ⟨y, hyU⟩ :=
    ((Topology.IsInducing.subtypeVal.specializes_iff (x := (⟨x, hxU⟩ : U))
      (y := ⟨y, hyU⟩)).1 h).map hU.isoSpec.hom.base.hom.continuous
  exact (PrimeSpectrum.le_iff_specializes _ _).2 hxy

/-- For `x ⤳ y`, the morphism `Spec 𝒪_{X,y} ⟶ X` sends the preimage of the maximal ideal of
`𝒪_{X,x}` under the specialization map to `x`. -/
theorem fromSpecStalk_comap_maximalIdeal {x y : X} (h : x ⤳ y) :
    X.fromSpecStalk y ⟨(maximalIdeal (X.presheaf.stalk x)).comap
      (X.presheaf.stalkSpecializes h).hom, inferInstance⟩ = x := by
  have e := congrArg (fun f ↦ f (closedPoint (X.presheaf.stalk x)))
    (SpecMap_stalkSpecializes_fromSpecStalk h)
  simp only [Scheme.Hom.comp_apply, fromSpecStalk_closedPoint] at e
  exact e

/-- A point in the image of `Spec 𝒪_{X,y} ⟶ X` generalises `y`. -/
theorem fromSpecStalk_specializes {y : X} (p : PrimeSpectrum (X.presheaf.stalk y)) :
    X.fromSpecStalk y p ⤳ y := by
  have : X.fromSpecStalk y p ∈ Set.range (X.fromSpecStalk y) := Set.mem_range_self p
  rwa [range_fromSpecStalk] at this

/-- The point of `X` defined by a prime `𝔭` of `𝒪_{X,y}` has local ring the localization at `𝔭`:
the preimage of its maximal ideal under the specialization map is `𝔭`. -/
theorem comap_stalkSpecializes_fromSpecStalk {y : X} (p : PrimeSpectrum (X.presheaf.stalk y)) :
    (maximalIdeal (X.presheaf.stalk (X.fromSpecStalk y p))).comap
      (X.presheaf.stalkSpecializes (fromSpecStalk_specializes p)).hom = p.asIdeal :=
  congrArg PrimeSpectrum.asIdeal ((X.fromSpecStalk y).isEmbedding.injective
    (fromSpecStalk_comap_maximalIdeal (fromSpecStalk_specializes p)))

/-- The local ring at the point of `X` defined by a prime `𝔭` of `𝒪_{X,y}` is the localization of
`𝒪_{X,y}` at `𝔭`. -/
theorem isLocalization_stalkSpecializes_fromSpecStalk {y : X}
    (p : PrimeSpectrum (X.presheaf.stalk y)) :
    letI := (X.presheaf.stalkSpecializes (fromSpecStalk_specializes p)).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk y p)) p.asIdeal := by
  have h := isLocalization_stalkSpecializes (fromSpecStalk_specializes p)
  convert h using 2
  exact (comap_stalkSpecializes_fromSpecStalk p).symm

/-! ### Points with values in a local ring -/

section stalkClosedPointTo

variable {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]

open IsLocalRing

/-- Two morphisms `Spec R ⟶ X` from the spectrum of a local ring agree if they send the closed
point to the same point and induce the same local homomorphism on stalks. -/
theorem eq_of_stalkClosedPointTo_eq {f g : Spec R ⟶ X} (h : f (closedPoint R) = g (closedPoint R))
    (e : stalkClosedPointTo f =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ stalkClosedPointTo g) : f = g :=
  (SpecToEquivOfLocalRing X R).injective (SpecToEquivOfLocalRing_eq_iff.mpr ⟨h, e⟩)

/-- The local homomorphism on stalks attached to `Spec φ ≫ (Spec 𝒪_{X,x} ⟶ X)` is `φ`. -/
theorem stalkClosedPointTo_spec_map_fromSpecStalk {x : X} (φ : X.presheaf.stalk x ⟶ R)
    [IsLocalHom φ.hom] :
    stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom ≫ φ := by
  have h := (SpecToEquivOfLocalRing X R).right_inv ⟨x, φ, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp h
  exact h₂

/-- Precomposing a morphism `f : Spec R ⟶ X` with `Spec ψ`, for a local homomorphism
`ψ : R ⟶ S` of local rings, postcomposes the homomorphism `stalkClosedPointTo f` with `ψ`. -/
theorem stalkClosedPointTo_spec_map_comp (ψ : R ⟶ S) [IsLocalHom ψ.hom] (f : Spec R ⟶ X) :
    stalkClosedPointTo (Spec.map ψ ≫ f) =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom ≫ stalkClosedPointTo f ≫ ψ := by
  have e : Spec.map ψ ≫ f = Spec.map (stalkClosedPointTo f ≫ ψ) ≫ X.fromSpecStalk _ := by
    conv_lhs => rw [← Spec_stalkClosedPointTo_fromSpecStalk f]
    rw [Spec.map_comp, Category.assoc]
  have : IsLocalHom (stalkClosedPointTo f ≫ ψ).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have h := congrArg (SpecToEquivOfLocalRing X S) e
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp
    (h.trans ((SpecToEquivOfLocalRing X S).right_inv ⟨_, _, this⟩))
  exact h₂

end stalkClosedPointTo

end AlgebraicGeometry.Scheme
