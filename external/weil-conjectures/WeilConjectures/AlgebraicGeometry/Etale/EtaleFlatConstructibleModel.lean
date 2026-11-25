/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Bounded flat constructible models on the small etale site

Source: `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/FlatModel.lean`, theorem
`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`, and the constructible variant of
blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`
(blueprint: lem-sf-etale-flat-constructible).

This statement uses the recorded finite-constant-value constructibility predicate, both
on cohomology sheaves and on the terms of the model.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Over a finite commutative ring on a Noetherian scheme, a bounded constructible etale
complex has Tor amplitude in `[a,b]`, with `a ≤ b`, exactly when it has a flat constructible
model supported in that same interval.

Source: `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/FlatModel.lean`, theorem
`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`, lines 160-214; blueprint
`sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`, constructible variant
(blueprint: lem-sf-etale-flat-constructible).

Proof plan:
1. Apply `lem-weil-pbc-constructible-etale-module-sheaf-comparison` to every cohomology
   sheaf, converting the finite-value predicate to `Scheme.IsConstructibleSheaf`.
   Let `T` be this source predicate and `S` its conjunction with flatness.
2. By the kernel and cokernel clauses of `thm-constructible-serre`, and the comparison
   on the source, target and resulting sheaf, `T` is closed under kernels and cokernels.
3. Zero sheaves are constant with zero value on the one-stratum partition, and
   isomorphisms preserve stratum trivializations and flatness. Tensor with zero is exact.
   The split exact sequence for a binary biproduct, `thm-constructible-serre`, and the
   comparison give its constructibility; `lem-weil-pbc-flat-coproduct` gives its flatness.
   Thus `S` contains zero, is invariant under isomorphisms and binary biproducts, and
   is contained in both `T` and the flat objects.
4. The lifting condition for `S,T` is `lem-sf-etale-flat-constructible-lifting`: lift a
   map from a constructible sheaf along an epimorphism after an epimorphic cover by a
   flat constructible sheaf. This does not require the original sheaf to be flat.
5. Given Tor amplitude, apply `lem-sf-flat-model-class-resolution` with these classes.
   The result is supported in `[a,b]`, with flat terms in `T`, and isomorphic to `K`.
   Its lower good truncation term is a constructible cokernel. Invert the isomorphism
   and apply the comparison to each term to obtain finite-value constructibility.
6. Conversely forget termwise constructibility and apply the reverse direction of
   `lem-sf-etale-flat-model`, converting the bounded-constructibility hypothesis using
   the same comparison. Bounded constructibility alone is not finite Tor amplitude. -/
theorem hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [IsNoetherian X]
    (a b : ℤ) (hab : a ≤ b) (K : DerivedCategoryModule Λ X)
    (hK : DerivedCategory.isBoundedConstructible Λ X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        (∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
        (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
        Nonempty ((_root_.DerivedCategory.Q).obj P ≅ K) := by
  have hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
    obtain ⟨c, d, -, hcd⟩ := hK.2
    refine ⟨⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hcd q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hcd q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hK.1 q)
  constructor
  · intro h
    obtain ⟨P, hP, hc, ⟨e⟩⟩ :=
      (hasTorAmplitudeIn_iff_exists_flatConstructibleModel Λ a b hab K hK').1 h
    exact ⟨P, hP.2,
      fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      hP.1, ⟨e.symm⟩⟩
  · rintro ⟨P, hf, -, hz, ⟨e⟩⟩
    exact (hasTorAmplitudeIn_iff_exists_flatModel Λ a b hab K hK').2
      ⟨P, ⟨hz, hf⟩, ⟨e.symm⟩⟩

end AlgebraicGeometry.Etale
