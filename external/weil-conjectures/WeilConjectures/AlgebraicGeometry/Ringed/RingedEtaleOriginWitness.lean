/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

/-!
# Specified etale-origin witnesses for constant pro-etale coefficients

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleOriginWitness`:
  the data witnessing an étale origin.

## References

* Stacks Tag 00WJ
* Stacks Tag 00YV
* Stacks 03DA, 09BT
* Stacks 099R, 09BT
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- Constant commutative coefficients in the module universe of the small site. -/
noncomputable abbrev etaleOriginRing : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Constant scalar sections into the specified constant commutative ring sheaf. -/
noncomputable def etaleOriginScalars :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (etaleOriginRing T Λ)).obj :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- Constant scalar sections are locally bijective also after forgetting commutativity. -/
theorem etaleOriginScalars_locallyBijective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (etaleOriginScalars T Λ) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (etaleOriginScalars T Λ) := by
  constructor
  · apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective (ProEt.topology T)
      (Functor.whiskerRight (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
          (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  · apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology T)
      (Functor.whiskerRight (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
          (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance

/-- Local injectivity for associated module sheafification. -/
noncomputable instance etaleOriginScalars_isLocallyInjective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (etaleOriginScalars T Λ) :=
  (etaleOriginScalars_locallyBijective T Λ).1

/-- Local surjectivity for associated module sheafification. -/
noncomputable instance etaleOriginScalars_isLocallySurjective :
    Presheaf.IsLocallySurjective (ProEt.topology T) (etaleOriginScalars T Λ) :=
  (etaleOriginScalars_locallyBijective T Λ).2

/-- Canonical realization of fixed-ring module sheaves over the constant ring sheaf.
The module presheaf is the recorded realization and the scalar map is constant sections. -/
noncomputable def etaleOriginRealization :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ) ⥤
      proEtaleRingModules T (etaleOriginRing T Λ) :=
  sheafToPresheaf _ _ ⋙ ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ ⋙
    PresheafOfModules.sheafification (etaleOriginScalars T Λ)

/-- The realization is an exact additive equivalence. -/
theorem etaleOriginRealization_properties :
    (etaleOriginRealization T Λ).Additive ∧
      PreservesFiniteLimits (etaleOriginRealization T Λ) ∧
      PreservesFiniteColimits (etaleOriginRealization T Λ) ∧
      (etaleOriginRealization T Λ).IsEquivalence := by
  have : (etaleOriginRealization T Λ).IsEquivalence :=
    ProEtale.coefficientRealization_isEquivalence (ProEt.topology T) Λ
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (etaleOriginRing T Λ))
      (etaleOriginScalars T Λ)
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance,
    this⟩

/-- Additivity of the constant-coefficient realization. -/
noncomputable instance etaleOriginRealization_additive :
    (etaleOriginRealization T Λ).Additive := (etaleOriginRealization_properties T Λ).1

/-- Left exactness of the constant-coefficient realization. -/
noncomputable instance etaleOriginRealization_preservesFiniteLimits :
    PreservesFiniteLimits (etaleOriginRealization T Λ) :=
  (etaleOriginRealization_properties T Λ).2.1

/-- Right exactness of the constant-coefficient realization. -/
noncomputable instance etaleOriginRealization_preservesFiniteColimits :
    PreservesFiniteColimits (etaleOriginRealization T Λ) :=
  (etaleOriginRealization_properties T Λ).2.2.1

/-- The specified comparison inverse image, with its canonical constant-ring realization. -/
noncomputable def etaleOriginComparison :
    DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (proEtaleRingModules T (etaleOriginRing T Λ)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙
    etaleOriginRealization T Λ).mapDerivedCategory

/-- Reuse the recorded retained origin pair for every finite discrete ring, including
noncommutative rings. Both the input and its etale antecedent are bounded below. -/
abbrev EtaleOriginWitness (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : ProEtale.FiniteCoefficientDerivedCategoryPlus T Λ) :=
  ProEtale.EtaleOriginWitness T Λ K

end AlgebraicGeometry.Scheme

@[expose] public noncomputable section
namespace AlgebraicGeometry.Scheme

/-- The finite constant coefficient sheaf in its function presentation. -/
abbrev finiteOriginFunctionRing (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] := AdicCoefficients.coefficientRing T Λ

/-- Constants-to-functions is the canonical finite coefficient isomorphism. -/
theorem finiteOriginConstantComparison_isIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : IsIso (AdicCoefficients.constantComparison T Λ) := by
  classical
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  have hinj : Presheaf.IsLocallyInjective (ProEt.topology T)
      (AdicCoefficients.constants T Λ) := by
    refine ⟨?_⟩
    intro U a b hab
    by_cases hU : Nonempty U.unop.left
    · obtain ⟨x⟩ := hU
      have hab' := congrArg (fun s : C(ConnectedComponents U.unop.left, Λ) ↦ s ⟦x⟧) hab
      change a = b at hab'
      subst b
      simpa only [Presheaf.equalizerSieve_self_eq_top] using
        (ProEt.topology T).top_mem U.unop
    · have : IsEmpty U.unop.left := not_nonempty_iff.mp hU
      exact (ProEt.topology T).superset_covering bot_le (ProEt.bot_mem_topology U.unop)
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology T)
      (AdicCoefficients.constants T Λ) := by
    refine ⟨?_⟩
    intro U s
    let f : C(U.left, Λ) := s.comp ⟨_, ConnectedComponents.continuous_coe⟩
    let O (x : U.left) : U.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete _).preimage f.continuous⟩
    apply ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨f x, ?_⟩
      apply ContinuousMap.ext
      intro c
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
      change f x = f y.val
      exact y.property.symm
  exact ((ProEt.topology T).W_iff (AdicCoefficients.constants T Λ)).mp
    ((ProEt.topology T).W_of_isLocallyBijective (AdicCoefficients.constants T Λ))

/-- The constants-to-functions transport retains exactly the section map. -/
def finiteOriginConstantIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : etaleOriginRing T Λ ≅ finiteOriginFunctionRing T Λ :=
  @asIso _ _ _ _ (AdicCoefficients.constantComparison T Λ)
    (finiteOriginConstantComparison_isIso T Λ)

/-- Canonical exact restriction from function coefficients to constant coefficients. -/
abbrev finiteOriginToConstant (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    DerivedCategory (proEtaleRingModules T (finiteOriginFunctionRing T Λ)) ⥤
      DerivedCategory (proEtaleRingModules T (etaleOriginRing T Λ)) := by
  let a := (finiteOriginConstantIso T Λ).hom
  letI : PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).1
  letI : PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).2.1
  exact (proEtaleRingRestrictScalars a).mapDerivedCategory

/-- The same retained witness pair after the canonical finite coefficient transport.
It contains a specified bounded-below etale object and its isomorphism, not just existence. -/
structure FiniteEtaleOriginWitness (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (proEtaleRingModules T (finiteOriginFunctionRing T Λ))) where
  complex : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  iso : (etaleOriginComparison T Λ).obj complex.obj ≅ (finiteOriginToConstant T Λ).obj K

end AlgebraicGeometry.Scheme
