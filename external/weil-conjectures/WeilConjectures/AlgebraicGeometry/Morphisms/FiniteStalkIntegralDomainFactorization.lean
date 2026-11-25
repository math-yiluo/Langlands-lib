/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Unramified.Finite

/-!
# Integral domain factorization of a finite stalk map

## References

* Stacks Project, Tag 00GI (integral ring maps) and the localization description of affine stalks
* B. Iversen, I.2.7

## Implementation details

The proof uses Mathlib's `Algebra.FormallyUnramified.flat_of_restrictScalars`
(Iversen, I.2.7).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- For a finite morphism `f` and a point `x` with `𝒪_{X,x}` a domain, the stalk map
`𝒪_{Y,f x} ⟶ 𝒪_{X,x}` factors as an integral map to an integral domain followed by a flat map. -/
theorem finite_stalk_integral_domain_factorization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) (hX : IsDomain (X.presheaf.stalk x)) :
    ∃ (B : CommRingCat.{u}) (a : Y.presheaf.stalk (f x) →+* B)
      (b : B →+* X.presheaf.stalk x),
      IsDomain B ∧ a.IsIntegral ∧ b.Flat ∧ b.comp a = (f.stalkMap x).hom := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  let A := Γ(Y, U)
  let C := Γ(X, f ⁻¹ᵁ U)
  let R := Y.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  let α : A →+* C := (f.app U).hom
  let γ : C →+* T := (X.presheaf.germ (f ⁻¹ᵁ U) x hxU).hom
  let : Algebra A C := α.toAlgebra
  let : Algebra A R := (Y.presheaf.germ U (f x) hxU).hom.toAlgebra
  let : Algebra C T := γ.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal
  let M := p.primeCompl.map α
  let S := Localization M
  have : IsLocalization p.primeCompl R := hU.isLocalization_stalk ⟨f x, hxU⟩
  have : IsLocalization ((hU.preimage f).primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl T :=
    (hU.preimage f).isLocalization_stalk ⟨x, hxU⟩
  have hunit (m : M) : IsUnit (γ m) := by
    obtain ⟨a, ha, he⟩ := m.2
    have hh := (IsLocalization.map_units R ⟨a, ha⟩).map (f.stalkMap x).hom
    change IsUnit ((f.stalkMap x).hom ((Y.presheaf.germ U (f x) hxU).hom a)) at hh
    simpa only [← he, γ, α, f.germ_stalkMap_apply] using hh
  let b₀ : S →+* T := IsLocalization.lift hunit
  let a₀ : R →+* S := IsLocalization.map S α p.primeCompl.le_comap_map
  let : Algebra S T := b₀.toAlgebra
  have : IsScalarTower C S T := IsScalarTower.of_algebraMap_eq fun c ↦
    (IsLocalization.lift_eq hunit c).symm
  have : Module.Flat C T := IsLocalization.flat T
    ((hU.preimage f).primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hb₀ : Module.Flat S T := (Module.flat_iff_of_isLocalization S M T).mpr inferInstance
  have ha₀ : a₀.IsIntegral := by
    have : Module.Finite A C := f.finite_app U hU
    have : Algebra.IsIntegral A C := inferInstance
    have : IsLocalization (Algebra.algebraMapSubmonoid C p.primeCompl) S := by
      change IsLocalization M S
      infer_instance
    exact isIntegral_localization
  have hab₀ : b₀.comp a₀ = (f.stalkMap x).hom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change b₀ (a₀ (algebraMap A R a)) = (f.stalkMap x).hom (algebraMap A R a)
    have hm : a₀ (algebraMap A R a) = algebraMap C S (α a) :=
      IsLocalization.map_eq p.primeCompl.le_comap_map a
    rw [hm]
    have hl : b₀ (algebraMap C S (α a)) = γ (α a) := IsLocalization.lift_eq hunit (α a)
    rw [hl]
    exact (f.germ_stalkMap_apply U x hxU a).symm
  let B := b₀.range
  let a : R →+* B := b₀.rangeRestrict.comp a₀
  let b : B →+* T := B.subtype
  let : IsDomain T := hX
  let : Algebra S B := b₀.rangeRestrict.toAlgebra
  let : Algebra B T := b.toAlgebra
  have : IsScalarTower S B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FormallyUnramified S B :=
    RingHom.FormallyUnramified.of_surjective b₀.rangeRestrict_surjective
  let : Module.Flat S T := hb₀
  have : Module.Finite S B :=
    Module.Finite.of_surjective (Algebra.linearMap S B) b₀.rangeRestrict_surjective
  have hb : b.Flat := Algebra.FormallyUnramified.flat_of_restrictScalars S B T
  refine ⟨CommRingCat.of B, a, b, inferInstance, ?_, hb, ?_⟩
  · intro r
    obtain ⟨s, rfl⟩ := b₀.rangeRestrict_surjective r
    exact (ha₀ s).map b₀.rangeRestrict
  · exact hab₀

end AlgebraicGeometry.Scheme
