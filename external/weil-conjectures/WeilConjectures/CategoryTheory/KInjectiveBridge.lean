/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# The K-injective bridge

Source: Weil conjectures blueprint, chap-Abelian-varieties, cor-pqf-proper-quasifinite-finite,
def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge).

## Main definitions

* `CochainComplex.KInjectiveResolutionChoice`: a chosen quasi-isomorphism into a K-injective
  complex in an arbitrary abelian category.
* `CochainComplex.grothendieckKInjectiveResolutionChoice`: the existing functorial resolution
  supplies such a choice for every complex in a Grothendieck abelian category.
* `CategoryTheory.Functor.rightDerivedComplexWithResolution`: `RvK := v(I)` for a chosen
  resolution of a bounded-below complex.
* `CategoryTheory.Functor.rightDerivedCohomologyWithResolution`: `R^p v(K) := H^p(v(I))`.

K-injectivity uses Mathlib's `CochainComplex.IsKInjective`, as in
`prose-03-02`: every map from an acyclic complex is null-homotopic.
The Hom-complex formulation follows by applying this in every shifted degree.
Independence of the choice and agreement with `Functor.rightDerived` on objects in degree zero
are deferred to `lem-sp-kinjective-computes`; the definitions retain the chosen resolution.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A K-injective resolution consists of a complex `I`, a quasi-isomorphism `K ⟶ I`, and
K-injectivity of `I`, using the generic Mathlib notions underlying the étale specialization
`prose-03-02`.
Source: blueprint def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge). -/
structure KInjectiveResolutionChoice {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) where
  complex : CochainComplex C ℤ
  map : K ⟶ complex
  quasiIso : QuasiIso map
  isKInjective : complex.IsKInjective

/-- Every complex in a Grothendieck abelian category has a chosen K-injective resolution,
obtained from the functor and natural transformation of
`lem-weil-pbc-kinjective-functorial-existence`. This includes every bounded-below complex.
Source: blueprint def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge). -/
noncomputable def grothendieckKInjectiveResolutionChoice
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (K : CochainComplex C ℤ) : KInjectiveResolutionChoice K where
  complex := (kInjectiveResolutionFunctor.{w} C).obj K
  map := (toKInjectiveResolution.{w} C).app K
  quasiIso := (monoQuasiIso_toKInjectiveResolution_app.{w} C K).2
  isKInjective := isKInjective_kInjectiveResolutionFunctor_obj.{w} C K

end CochainComplex

namespace CategoryTheory.Functor

/-- For a left exact additive functor `F` and a bounded-below complex `K`, the notation `RFK`
with a chosen K-injective resolution `r : K ⟶ I` means the complex `F(I)` obtained termwise.
Its dependence on `r` is explicit; no choice-independence claim is part of this definition.
Source: blueprint def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge). -/
def rightDerivedComplexWithResolution
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus C) (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    CochainComplex D ℤ :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj r.complex

/-- For a left exact additive functor `F`, a bounded-below complex `K`, and a chosen
K-injective resolution `r`, define `R^p F(K)` as `H^p(RFK)`, for every integer `p`.
Agreement with ordinary right derived functors on objects in degree zero is the later
comparison lemma `lem-sp-kinjective-computes`.
Source: blueprint def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge). -/
noncomputable def rightDerivedCohomologyWithResolution
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus C) (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (p : ℤ) : D :=
  (F.rightDerivedComplexWithResolution K r).homology p

end CategoryTheory.Functor
