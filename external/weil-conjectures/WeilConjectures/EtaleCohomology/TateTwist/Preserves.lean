/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Tate twists preserve the finiteness conditions

Let `Λ` be a finite ring whose characteristic `n` is invertible on `X`. The Tate twists
`Λ_X(m) = (μₙ ⊗ Λ)^{⊗ m}` (`AlgebraicGeometry.Etale.tateTwistObject`) are invertible locally
constant sheaves of rank one placed in degree `0`, and they are flat. So twisting
`K ↦ K(m) = K ⊗ᴸ Λ_X(m)` preserves bounded constructibility and the Tor amplitude interval, on
the étale site and, through the site comparison `ν^*`, on the pro-étale site (blueprint
`definition-tate-twists--10`).

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_and_exists_tateTwistObject`: `Λ_X(m)` is an invertible
  locally constant sheaf of rank one.
- `AlgebraicGeometry.Etale.boundedConstructible_tateTwist`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_tateTwist`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_tateTwist`: twisting preserves `Dᵇc`, Tor
  amplitude intervals and `Dctf` on the étale site.
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_tateTwist`,
  `AlgebraicGeometry.ProEtale.torAmplitudeIn_tateTwist`: the same on the pro-étale site, for the
  twist by `ν^* Λ_X(m)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)] (X : Scheme.{u})
  [HasInvertibleExponent Λ X]

/-- Blueprint `definition-tate-twists--10`: Twists preserve finiteness conditions (the twisting
objects).

Each Tate twist `Λ_X(m)` is an invertible locally constant sheaf of rank one: it is a locally
constant sheaf `L` placed in degree `0` whose geometric stalks are free of rank one, `L` is flat,
and `Λ_X(m)` has a tensor inverse. -/
theorem isInvertible_and_exists_tateTwistObject (m : ℤ) :
    DerivedCategory.isInvertible Λ X (tateTwistObject Λ X m) ∧
      ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
        ObjectProperty.flat L ∧
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
          Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
        Nonempty (tateTwistObject Λ X m ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
  ⟨isInvertible_tateTwistObject Λ X m, tateTwistSheaf Λ X m,
    (isFiniteLocallyConstantSheaf_tateTwistSheaf Λ X m).toIsLocallyConstantSheaf,
    flat_tateTwistSheaf Λ X m, fun _ _ _ s ↦ ⟨sheafFiberTateTwistSheafIso Λ X m s⟩,
    ⟨tateTwistObjectIsoSingleFunctor Λ X m⟩⟩

/-- Each Tate twist `Λ_X(m)` has Tor amplitude in `[0, 0]`: it is a flat sheaf placed in
degree `0`. -/
lemma torAmplitudeIn_tateTwistObject (m : ℤ) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0 (tateTwistObject Λ X m) :=
  (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0).prop_of_iso
    (tateTwistObjectIsoSingleFunctor Λ X m).symm
    (torAmplitudeIn_singleFunctor_zero_of_flat _ _ (flat_tateTwistSheaf Λ X m))

variable {X}

/-- Blueprint `definition-tate-twists--10`: Twists preserve finiteness conditions (Tor
amplitude).

Twisting `K ↦ K(m) = K ⊗ᴸ Λ_X(m)` preserves the Tor amplitude interval `[a, b]`, since `Λ_X(m)`
has Tor amplitude in `[0, 0]`. -/
theorem torAmplitudeIn_tateTwist (m : ℤ) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (tateTwistObject Λ X m)) := by
  simpa using torAmplitudeIn_tensor (ModuleCat.{u + 1} Λ) X a b 0 0 hK
    (torAmplitudeIn_tateTwistObject Λ X m)

variable [Finite Λ]

/-- Blueprint `definition-tate-twists--10`: Twists preserve finiteness conditions (bounded
constructibility).

For a finite ring `Λ`, twisting `K ↦ K(m) = K ⊗ᴸ Λ_X(m)` preserves bounded constructibility:
`Λ_X(m)` is bounded constructible of finite Tor amplitude. -/
theorem boundedConstructible_tateTwist (m : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (tateTwistObject Λ X m)) :=
  boundedConstructible_tensor Λ X hK (boundedConstructibleFiniteTor_tateTwistObject Λ X m).1
    (boundedConstructibleFiniteTor_tateTwistObject Λ X m).2

/-- Blueprint `definition-tate-twists--10`: Twists preserve finiteness conditions (the category
`Dctf`).

For a finite ring `Λ`, twisting `K ↦ K(m)` carries `Dctf(X, Λ)` into itself. -/
theorem constructibleFiniteTor_tateTwist (m : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (tateTwistObject Λ X m)) :=
  ⟨boundedConstructible_tateTwist Λ m hK.1,
    have ⟨a, b, h⟩ := hK.2
    ⟨a, b, torAmplitudeIn_tateTwist Λ m h⟩⟩

end Etale

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)] [Finite Λ] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]

/-- The pro-étale twist `K(m) = K ⊗ᴸ ν^* Λ_X(m)` of a complex `K ∈ D(X_proét, Λ)` of étale origin
`K ≅ ν^* G` is `ν^*` of the étale twist `G(m)`: `ν^*` is monoidal. -/
noncomputable def tateTwistComparisonIso (m : ℤ)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (e : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G ≅ K) :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj G).obj
        (Etale.tateTwistObject Λ X m)) ≅
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (Etale.tateTwistObject Λ X m)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso (ModuleCat.{u + 1} Λ) G).app _ ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e).app _

/-- Blueprint `definition-tate-twists--10`: Twists preserve finiteness conditions (on the
pro-étale site).

For a finite ring `Λ` whose characteristic is invertible on `X`, twisting
`K ↦ K(m) = K ⊗ᴸ ν^* Λ_X(m)` carries `Dctf(X_proét, Λ)` into itself: `K ≅ ν^* G` with
`G ∈ Dctf(X_ét, Λ)`, and `K(m) ≅ ν^*(G(m))`. -/
theorem constructibleFiniteTor_tateTwist (m : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (Etale.tateTwistObject Λ X m))) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  obtain ⟨G, hG, ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ K).1 hbc
  have hGt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b G :=
    DerivedCategory.torAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar Λ
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b).prop_of_iso e.symm hta)
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).prop_of_iso
    (tateTwistComparisonIso Λ m G e)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_tateTwist Λ m ⟨hG, a, b, hGt⟩))

/-- Blueprint `definition-tate-twists--10`: Twists preserve finiteness conditions (Tor
amplitude on the pro-étale site).

For `K ∈ Dctf(X_proét, Λ)` of Tor amplitude in `[a, b]`, the twist `K(m) = K ⊗ᴸ ν^* Λ_X(m)` has
Tor amplitude in `[a, b]`. -/
theorem torAmplitudeIn_tateTwist (m : ℤ) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (Etale.tateTwistObject Λ X m))) := by
  obtain ⟨G, -, ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ K).1 hK
  have hGt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b G :=
    DerivedCategory.torAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar Λ
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b).prop_of_iso e.symm hta)
  exact (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b).prop_of_iso
    (tateTwistComparisonIso Λ m G e)
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory Λ (Etale.torAmplitudeIn_tateTwist Λ m hGt))

end ProEtale

end AlgebraicGeometry
