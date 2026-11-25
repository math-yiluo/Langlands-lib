/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.EssentialImage

/-!
# The category of bounded below complexes with a retained etale origin

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
`proposition-construction-independence-rf-shriek`, order 1472, and the retained witness of
`proposition-proper-direct-image-constructible-complexes--5`, order 1289
(blueprint: def-sf-etale-origin-subcategory).

Objects retain the pro-etale complex and the complete etale-origin witness. Morphisms
are all morphisms between the pro-etale complexes; no map of witnesses is required.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The category of triples `(K, L, alpha)` with `K` bounded below on the pro-etale site,
`L` bounded below on the etale site, and `alpha : nu^* L ≅ K`. The sigma type retains
`K` and the recorded `EtaleOriginWitness`, hence both `L` and `alpha`. The induced
category has precisely the ambient derived morphisms between the underlying `K`s,
with the ambient identities and composition.
Source: Weil blueprint, `proposition-construction-independence-rf-shriek`, order 1472, and
`proposition-proper-direct-image-constructible-complexes--5`, order 1289
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable abbrev EtaleOriginDerivedCategory (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :=
  InducedCategory (FiniteCoefficientDerivedCategoryPlus T Λ)
    (fun P : Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K ↦ P.1)

/-- Forget the retained witness and keep `K` in the bounded below pro-etale category.
On morphisms this is the identity under `InducedCategory.homEquiv`.
Source: Weil blueprint, `proposition-construction-independence-rf-shriek`, order 1472
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def etaleOriginForgetfulPlus (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    EtaleOriginDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategoryPlus T Λ :=
  inducedFunctor
    (fun P : Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K ↦ P.1)

/-- The forgetful functor is fully faithful by the induced-category construction.
Source: Weil blueprint, `proposition-construction-independence-rf-shriek`, order 1472;
Mathlib, `CategoryTheory.fullyFaithfulInducedFunctor`
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def etaleOriginForgetfulPlusFullyFaithful (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (etaleOriginForgetfulPlus T Λ).FullyFaithful :=
  fullyFaithfulInducedFunctor
    (fun P : Σ K : FiniteCoefficientDerivedCategoryPlus T Λ, EtaleOriginWitness T Λ K ↦ P.1)

/-- Regard the witness-retaining category as a full subcategory of the unbounded
pro-etale derived category through the bounded below inclusion.
Source: Weil blueprint, `proposition-construction-independence-rf-shriek`, order 1472
(blueprint: def-sf-etale-origin-subcategory). -/
noncomputable def etaleOriginForgetful (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    EtaleOriginDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategory T Λ :=
  etaleOriginForgetfulPlus T Λ ⋙ DerivedCategory.Plus.ι

end AlgebraicGeometry.ProEtale
