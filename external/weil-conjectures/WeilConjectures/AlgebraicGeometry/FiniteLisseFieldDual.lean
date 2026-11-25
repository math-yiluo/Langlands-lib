/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual

/-!
# Duals of bounded finite locally constant complexes over a prime field

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-lisse-field-dual.md
(blueprint: lemma-smooth-morphisms-locally-constant-sheaves).

The existing etale `derivedHom` is the K-injective derived internal Hom in the
`ModuleCat` encoding. Its construction derives the homotopy-category Hom functor
using K-injectives in `DerivedCategory.tensorHomAdjunctionQhObj`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

/-- The internal-Hom comparison followed by an isomorphism in the second variable.
It is the transpose of pulled-back evaluation, as recorded by the identity below.
Source: blueprint lemma-smooth-morphisms-locally-constant-sheaves, proof step 5
(blueprint: lemma-smooth-morphisms-locally-constant-sheaves). -/
noncomputable def derivedHomPullbackAlongIsoComparison
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf T'.smallEtaleTopology A))
    (e : (L(upperStar A v)).obj M ≅ N) :
    (L(upperStar A v)).obj (((derivedHom A T).obj (op C)).obj M) ⟶
      ((derivedHom A T').obj (op ((L(upperStar A v)).obj C))).obj N :=
  derivedHomUpperStarComparison A v C M ≫
    ((derivedHom A T').obj (op ((L(upperStar A v)).obj C))).map e.hom

end General

/-- The canonical map from the pullback of the coefficient dual to the dual of the
pullback: transpose the pulled-back evaluation using the strong monoidal pullback
and its unit comparison. Source: blueprint lemma-smooth-morphisms-locally-constant-sheaves, proof
step 5; Stacks, Sites Cohomology, Section 08J7 (blueprint:
lemma-smooth-morphisms-locally-constant-sheaves). -/
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :=
  derivedHomPullbackAlongIsoComparison v C (constantComplex Λ T) (constantComplex Λ T')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v)

/-- Duality for an ordinary bounded etale complex over the prime field: finite local
constancy of cohomology is preserved, cohomology is the degree-reversed sheaf dual,
and the canonical comparison commutes with every scheme pullback.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-lisse-field-dual.md
(blueprint: lemma-smooth-morphisms-locally-constant-sheaves).

Proof: the global vanishing bounds give `C.IsGE a` and `C.IsLE b`, and the coefficient
ring `ULift (ZMod ℓ)` is a field. The truncation devissage of
`isFiniteLocallyConstantSheaf_homology_coefficientDual` (exact pairings of finite locally
constant cohomology sheaves over a field) gives finite local constancy of the dual
cohomology and the degree-reversed sheaf-dual formula. The same devissage,
`isIso_coefficientDualComparison_of_isFiniteLocallyConstantSheaf`, proves invertibility of
`coefficientDualComparison`, which is by definition the displayed pullback map: the
internal-Hom comparison of the strong monoidal pullback followed by the unit comparison. -/
theorem finiteLisseFieldDual
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (_hℓ : IsUnit (ℓ : Γ(T, ⊤)))
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj C))
    (_hlisse : ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) :
    (∀ q : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((derivedHom
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)))) ∧
    (∀ q : ℤ, Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((derivedHom
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
              (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj
          (𝟙_ (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))))) ∧
    (∀ (T' : Scheme.{u}) (v : T' ⟶ T),
      IsIso (finiteLisseDualPullbackComparison v C)) := by
  obtain ⟨a, b, _, hab⟩ := _hbounded
  have : C.IsGE a := (_root_.DerivedCategory.isGE_iff C a).2
    (fun n hn ↦ hab n (.inl hn))
  have : C.IsLE b := (_root_.DerivedCategory.isLE_iff C b).2
    (fun n hn ↦ hab n (.inr hn))
  have hfield : IsField (ULift.{u + 1} (ZMod ℓ)) := Field.toIsField _
  refine ⟨fun q ↦ ?_, fun q ↦ ?_, fun T' v ↦ ?_⟩
  · exact (isFiniteLocallyConstantSheaf_homology_coefficientDual hfield C a b _hlisse q).1
  · exact (isFiniteLocallyConstantSheaf_homology_coefficientDual hfield C a b _hlisse q).2
  · exact isIso_coefficientDualComparison_of_isFiniteLocallyConstantSheaf
      hfield C a b _hlisse v

end AlgebraicGeometry.Etale
