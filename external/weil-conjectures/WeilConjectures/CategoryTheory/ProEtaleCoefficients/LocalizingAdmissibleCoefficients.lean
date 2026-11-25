/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!
# Admissible condensed coefficients for localizing closures

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
coefficient convention (blueprint: definition-localizing-subcategory).

This supplies the coefficient convention omitted from the recorded localizing-closure
interface. The localizing closure itself is the imported `localizingClosureProEtale`.
The algebraic-closure clause is the finite-subextension-valued ring `padicAlgClRingObj`
(blueprint: sk-def-sfb-qlbar-condensed). The ring of all continuous maps to the algebraic
closure is not an admissible coefficient (removed 2026-10-25).

It also supplies `IsLocalizingSubcategoryOfSize` and `localizingClosureOfSize`, the
imported `IsLocalizingSubcategory` and `localizingClosure` with the index universe of
the direct sums given as a free parameter `w`. At `w = u`, the object universe, they
are the imported definitions. A fixed index universe shared by two categories of
different sizes, as in proposition-proper-direct-image-extension-zero, needs this form.
-/

@[expose] public section

set_option autoImplicit false

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A property describes a full replete triangulated subcategory closed under all
coproducts indexed by types in the universe `w` that exist in the ambient category.
At `w = v` (the morphism universe) this is `IsLocalizingSubcategory`. -/
def IsLocalizingSubcategoryOfSize {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) : Prop :=
  P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
    ∀ {I : Type w} (F : Discrete I ⥤ C), (hF : HasColimit F) →
      (∀ i : I, P (F.obj (Discrete.mk i))) →
        let _ := hF
        P (colimit F)

/-- The intersection of all full replete triangulated subcategories containing `S` and
closed under the existing `w`-indexed coproducts. At `w = v` (the morphism universe) this is
`localizingClosure`. -/
def localizingClosureOfSize {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : ObjectProperty C :=
  fun K ↦ ∀ P : ObjectProperty C, IsLocalizingSubcategoryOfSize.{w} P →
    (∀ L : C, S L → P L) → P K

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The admissible coefficients are the finite discrete rings killed by a power of `ℓ`,
`ℤ_ℓ`, `ℚ_ℓ`, finite subextensions of `ℚ_ℓ` in its fixed algebraic closure, their valuation
rings, and the finite-subextension-valued algebraic closure `padicAlgClRingObj`
(sk-def-sfb-qlbar-condensed); the ring of all continuous maps to the algebraic closure is
not admissible. Isomorphisms are in monoid objects of condensed abelian groups,
hence preserve both the additive and ring
structures. Finite rings can be represented in `Type 0` without restricting their
isomorphism classes. Source: blueprint definition-localizing-subcategory, coefficient convention
(blueprint: definition-localizing-subcategory). -/
def IsLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

end AlgebraicGeometry.ProEtale
