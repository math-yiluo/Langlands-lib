/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction

/-!
# Specialization of geometric points

Let `B` be a ring which is integrally closed in a field `Ω ⊇ B`, and `a : Spec B ⟶ S` a morphism
of schemes. A point `t : Spec Ω ⟶ X` of a finite `S`-scheme `X` over `a` extends uniquely to a
point `Spec B ⟶ X` over `a` (`AlgebraicGeometry.Scheme.existsUnique_extend_of_isFinite`): over the
affine `Spec B` the scheme `X` is the spectrum of a finite `B`-algebra `A`, and a ring map
`A → Ω` over `B` lands in `B`, since the image is integral over `B`.

Restricting the extension to a point `Spec κ ⟶ Spec B` gives, for finite étale `S`-schemes, a
natural map from the fibre at `Spec Ω ⟶ Spec B ⟶ S` to the fibre at `Spec κ ⟶ Spec B ⟶ S`, the
*specialization* (`AlgebraicGeometry.Scheme.FiniteEtale.specialization`). If `Ω` and `κ` are
separably closed and `S` is connected, it is an isomorphism of fibre functors, a path from the
generic geometric point to the special one. It is compatible with automorphisms of `B` over `S`
(`AlgebraicGeometry.Scheme.FiniteEtale.specialization_hom_app_precomp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

section Ring

variable {B A Ω : Type*} [CommRing B] [CommRing A] [CommRing Ω] [Algebra B Ω]
  [IsIntegrallyClosedIn B Ω]

/-- A ring map `ψ : A → Ω` from an integral `B`-algebra `A`, compatible with the inclusion of `B`
into `Ω` in which `B` is integrally closed, factors through `B`. -/
lemma RingHom.exists_comp_eq_of_isIntegrallyClosedIn (φ : B →+* A) (hφ : φ.IsIntegral)
    (ψ : A →+* Ω) (h : ψ.comp φ = algebraMap B Ω) :
    ∃ χ : A →+* B, χ.comp φ = RingHom.id B ∧ (algebraMap B Ω).comp χ = ψ := by
  let := φ.toAlgebra
  let := ψ.toAlgebra
  have : IsScalarTower B A Ω := IsScalarTower.of_algebraMap_eq fun b ↦ (RingHom.congr_fun h b).symm
  have : Algebra.IsIntegral B A := ⟨hφ⟩
  let χ := IsIntegralClosure.lift B B Ω (S := A)
  refine ⟨χ.toRingHom, ?_, ?_⟩
  · ext b
    exact χ.commutes b
  · ext a
    exact IsIntegralClosure.algebraMap_lift B B Ω a

end Ring

variable {S X : Scheme.{u}} {B Ω : Type u} [CommRing B] [Field Ω] [Algebra B Ω]
  [IsIntegrallyClosedIn B Ω]

/-- **Extension of points of finite schemes.** Let `B` be integrally closed in a field `Ω`. A
point `Spec Ω ⟶ X` of a finite `S`-scheme over `a : Spec B ⟶ S` extends uniquely to a point
`Spec B ⟶ X` over `a`. -/
theorem Scheme.existsUnique_extend_of_isFinite (a : Spec (.of B) ⟶ S) (f : X ⟶ S) [IsFinite f]
    (t : Spec (.of Ω) ⟶ X) (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ a) :
    ∃! u : Spec (.of B) ⟶ X, u ≫ f = a ∧ Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ u = t := by
  set ι := CommRingCat.ofHom (algebraMap B Ω)
  let Q := pullback f a
  let q : Q ⟶ Spec (.of B) := pullback.snd f a
  have : IsFinite q := inferInstance
  have : IsAffine Q := isAffine_of_isAffineHom q
  let e := Q.isoSpec
  let t' : Spec (.of Ω) ⟶ Q := pullback.lift t (Spec.map ι) ht
  let φ := Spec.preimage (e.inv ≫ q)
  let ψ := Spec.preimage (t' ≫ e.hom)
  have hφ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
    infer_instance
  have hψφ : ψ.hom.comp φ.hom = algebraMap B Ω := by
    change (φ ≫ ψ).hom = ι.hom
    congr 1
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
      e.hom_inv_id_assoc, pullback.lift_snd]
  -- the sections of `q` over `Spec B` correspond to the ring maps `χ` with `χ ∘ φ = id`
  have key (u : Spec (.of B) ⟶ X) (hu : u ≫ f = a) :
      Spec.map ι ≫ u = t ↔
        (algebraMap B Ω).comp (Spec.preimage (pullback.lift u (𝟙 _) (by simpa) ≫ e.hom)).hom =
          ψ.hom := by
    set s := pullback.lift u (𝟙 (Spec (.of B))) (by simpa)
    have h1 : Spec.map ι ≫ s = t' ↔ Spec.map ι ≫ u = t := by
      constructor
      · intro h
        have := congrArg (· ≫ pullback.fst f a) h
        simp only [s, t', Category.assoc] at this
        rwa [pullback.lift_fst, pullback.lift_fst] at this
      · intro h
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, s, t']
          exact h
        · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, s, t']
    rw [← h1]
    constructor
    · intro h
      change (Spec.preimage (s ≫ e.hom) ≫ ι).hom = ψ.hom
      congr 1
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc, h]
    · intro h
      have h' : Spec.map (Spec.preimage (s ≫ e.hom) ≫ ι) = Spec.map ψ := by
        congr 1
        exact CommRingCat.hom_ext h
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage] at h'
      rw [← cancel_mono e.hom, Category.assoc, h']
  obtain ⟨χ, hχφ, hχψ⟩ := RingHom.exists_comp_eq_of_isIntegrallyClosedIn φ.hom hφ.to_isIntegral
    ψ.hom hψφ
  let s : Spec (.of B) ⟶ Q := Spec.map (CommRingCat.ofHom χ) ≫ e.inv
  have hsq : s ≫ q = 𝟙 _ := by
    change Spec.map _ ≫ (e.inv ≫ q) = _
    rw [← Spec.map_preimage (e.inv ≫ q), ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext hχφ
  refine ⟨s ≫ pullback.fst f a, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hsq, Category.id_comp]
  · change Spec.map ι ≫ Spec.map _ ≫ e.inv ≫ _ = t
    rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom χ ≫ ι = ψ := CommRingCat.hom_ext hχψ
    rw [this, Spec.map_preimage, Category.assoc, e.hom_inv_id_assoc, pullback.lift_fst]
  · rintro u ⟨hu, hut⟩
    have hk := (key u hu).1 hut
    have hk' := (key (s ≫ pullback.fst f a) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsq, Category.id_comp])).1 (by
      change Spec.map ι ≫ Spec.map _ ≫ e.inv ≫ _ = t
      rw [← Category.assoc, ← Spec.map_comp]
      have : CommRingCat.ofHom χ ≫ ι = ψ := CommRingCat.hom_ext hχψ
      rw [this, Spec.map_preimage, Category.assoc, e.hom_inv_id_assoc, pullback.lift_fst])
    have hinj : Function.Injective (algebraMap B Ω) := IsIntegralClosure.algebraMap_injective B B Ω
    have heq : Spec.preimage (pullback.lift u (𝟙 _) (by simpa) ≫ e.hom) =
        Spec.preimage (pullback.lift (s ≫ pullback.fst f a) (𝟙 _) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, hsq, Category.id_comp]) ≫
            e.hom) := by
      ext x
      apply hinj
      exact (RingHom.congr_fun hk x).trans (RingHom.congr_fun hk' x).symm
    have := congrArg Spec.map heq
    rw [Spec.map_preimage, Spec.map_preimage, cancel_mono] at this
    have := congrArg (· ≫ pullback.fst f a) this
    rwa [pullback.lift_fst, pullback.lift_fst] at this

namespace Scheme.FiniteEtale

variable {Y : Scheme.{u}} {κ : Type u} [IsSepClosed Ω] [Field κ] [Algebra B κ] [IsSepClosed κ]
  (a : Spec (.of B) ⟶ Y)

/-- The unique extension `Spec B ⟶ P` over `a` of a point of the fibre of a finite étale
`Y`-scheme `P` at `Spec Ω ⟶ Spec B ⟶ Y`. -/
noncomputable def extendPoint (P : Y.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P) :
    Spec (.of B) ⟶ P.obj.left :=
  have : IsFinite P.obj.hom := P.property
  (Scheme.existsUnique_extend_of_isFinite a P.obj.hom t.left (fiber_left_comp _ t)).choose

lemma extendPoint_comp (P : Y.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P) :
    extendPoint a P t ≫ P.obj.hom = a :=
  have : IsFinite P.obj.hom := P.property
  (Scheme.existsUnique_extend_of_isFinite a P.obj.hom t.left (fiber_left_comp _ t)).choose_spec.1.1

lemma specMap_comp_extendPoint (P : Y.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P) :
    Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ extendPoint a P t = t.left :=
  have : IsFinite P.obj.hom := P.property
  (Scheme.existsUnique_extend_of_isFinite a P.obj.hom t.left (fiber_left_comp _ t)).choose_spec.1.2

lemma extendPoint_eq (P : Y.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P)
    (u : Spec (.of B) ⟶ P.obj.left) (hu : u ≫ P.obj.hom = a)
    (hut : Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ u = t.left) :
    extendPoint a P t = u :=
  have : IsFinite P.obj.hom := P.property
  ((Scheme.existsUnique_extend_of_isFinite a P.obj.hom t.left (fiber_left_comp _ t)).choose_spec.2
    u ⟨hu, hut⟩).symm

variable (Ω κ) in
/-- **Specialization of geometric points.** A point of a finite étale `Y`-scheme over the
geometric point `Spec Ω ⟶ Spec B ⟶ Y` extends uniquely to `Spec B`, and restricts to a point over
`Spec κ ⟶ Spec B ⟶ Y`: a morphism of fibre functors. -/
noncomputable def specialization : fiber (pointOfAlgebra Ω a) ⟶ fiber (pointOfAlgebra κ a) where
  app P := FintypeCat.homMk fun t ↦ Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap B κ)) ≫ extendPoint a P t)
    (by
      change (Spec.map _ ≫ extendPoint a P t) ≫ P.obj.hom = _
      rw [Category.assoc, extendPoint_comp]
      rfl)
  naturality P Q φ := by
    refine FintypeCat.hom_ext _ _ fun t ↦ ?_
    apply fiber_ext
    change Spec.map _ ≫ extendPoint a Q ((fiber _).map φ t) =
      (Spec.map _ ≫ extendPoint a P t) ≫ φ.hom.left
    rw [Category.assoc]
    congr 1
    apply extendPoint_eq
    · rw [Category.assoc, hom_left_comp, extendPoint_comp]
    · rw [← Category.assoc, specMap_comp_extendPoint]
      rfl

lemma specialization_app_left (P : Y.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P) :
    ((specialization Ω κ a).app P t).left =
      Spec.map (CommRingCat.ofHom (algebraMap B κ)) ≫ extendPoint a P t :=
  rfl

instance [ConnectedSpace Y] : IsIso (specialization Ω κ a) :=
  isIso_of_fiberFunctor _ _ _

/-- The specialization is compatible with automorphisms: if a ring automorphism `σ` of `B` over
`Y` extends to automorphisms of `Ω` and `κ`, then specializing commutes with precomposition by
`Spec σ`. -/
lemma specialization_app_fiberPrecompIso (σ : B ≃+* B) (σΩ : Ω ≃+* Ω) (σκ : κ ≃+* κ)
    (ha : Spec.map (CommRingCat.ofHom (σ : B →+* B)) ≫ a = a)
    (hΩ : (algebraMap B Ω).comp (σ : B →+* B) = (σΩ : Ω →+* Ω).comp (algebraMap B Ω))
    (hκ : (algebraMap B κ).comp (σ : B →+* B) = (σκ : κ →+* κ).comp (algebraMap B κ))
    (heΩ : (specMapIso σΩ).hom ≫ pointOfAlgebra Ω a = pointOfAlgebra Ω a)
    (heκ : (specMapIso σκ).hom ≫ pointOfAlgebra κ a = pointOfAlgebra κ a)
    (P : Y.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P) :
    (specialization Ω κ a).app P ((fiberPrecompIso _ (specMapIso σΩ) heΩ).hom.app P t) =
      (fiberPrecompIso _ (specMapIso σκ) heκ).hom.app P ((specialization Ω κ a).app P t) := by
  apply fiber_ext
  rw [specialization_app_left, fiberPrecompIso_hom_app_left, specialization_app_left]
  have hext : extendPoint a P ((fiberPrecompIso _ (specMapIso σΩ) heΩ).hom.app P t) =
      Spec.map (CommRingCat.ofHom (σ : B →+* B)) ≫ extendPoint a P t := by
    apply extendPoint_eq
    · rw [Category.assoc, extendPoint_comp, ha]
    · rw [fiberPrecompIso_hom_app_left, ← specMap_comp_extendPoint a P t, ← Category.assoc,
        ← Spec.map_comp]
      change _ = Spec.map (CommRingCat.ofHom (σΩ : Ω →+* Ω)) ≫ _ ≫ _
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      exact CommRingCat.hom_ext hΩ
  rw [hext, ← Category.assoc, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (σκ : κ →+* κ)) ≫ _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext hκ

end Scheme.FiniteEtale

end AlgebraicGeometry
