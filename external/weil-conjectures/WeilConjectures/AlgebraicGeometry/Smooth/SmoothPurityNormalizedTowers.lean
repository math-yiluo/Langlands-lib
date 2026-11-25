/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude

/-!
# Constructible and normalized coefficient towers

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-def-sp-normalized-towers/_section.md` (blueprint: prose-09-21).

The natural index n denotes positive level n+1. The finite-level category and both
tower categories are full subcategories of the ordinary derived categories. The
parameter D is the sectionwise normalized coefficient-tower interface of
`prose-09-21`, which supplies exact evaluation and the canonical
reduction natural transformation, including its tensor-unitor normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

attribute [local instance 2000] WeilConjectures.sfAbBijective

/-- The actual ell-power quotient is finite. This proof-valued instance is obtained
from the recorded cofinality and finite uniformizer-power quotients by the surjective
quotient map; it makes no new coefficient construction or choice of ring.
Source: blueprint, finite ring A_n (blueprint: prose-09-21). -/
instance spEllQuotientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) :=
  let h := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
  let m := h.choose
  letI : Finite (Padic.coefficientExtensionIntegers l E ⧸
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.le_add_left 1 m)
  Finite.of_surjective
    (Ideal.Quotient.factor
      ((Ideal.pow_le_pow_right (Nat.le_succ m)).trans h.choose_spec))
    (Ideal.Quotient.factor_surjective _)

/-- Finite-level Dctf: bounded cohomology, constructible in every degree, and finite
Tor amplitude. Bounds here may depend on the object.
Source: blueprint, finite-level convention (blueprint: prose-09-21). -/
def spFiniteConstructibleTor (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (Scheme.proEtaleDerivedCategory T A) :=
  fun K ↦
    (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((@DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
        _ _ (HasDerivedCategory.standard _) i).obj K)) ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T A
      ((@DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
        _ _ (HasDerivedCategory.standard _) i).obj K)) ∧
    Scheme.HasFiniteProEtaleTorAmplitude T A K

/-- The full finite-level subcategory, with precisely the ambient derived morphisms.
Source: blueprint, finite-level convention (blueprint: prose-09-21). -/
abbrev spFiniteConstructibleTorCategory (A : Type u) [CommRing A] [Finite A] :=
  (spFiniteConstructibleTor T A).FullSubcategory

/-- The ordinary derived category of the recorded abelian category of coefficient
towers, using the localization supplied by D. There is no normalization condition here.
Source: blueprint, ambient category (blueprint: prose-09-21). -/
abbrev spDerivedCoefficientTowers (D : SpCoefficientTowersAbelian l E T) :=
  @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived

/-- Exact level evaluation on the ordinary derived tower category; n means n+1.
Source: blueprint, levels C_n; coefficient-tower lemma clause (2)
(blueprint: prose-09-21). -/
def spDerivedCoefficientEvaluation (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    spDerivedCoefficientTowers l E T D ⥤
      Scheme.proEtaleDerivedCategory T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  @Functor.mapDerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived
    (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
    _ _ (HasDerivedCategory.standard _)
    (spCoefficientEvaluation l E T D.equivalence n) _ _ _

/-- Constructible finite-Tor towers with one common cohomological interval and one
common Tor interval, independently chosen and uniform over all positive levels.
Source: blueprint, first paragraph (blueprint: prose-09-21). -/
def spConstructibleTorTowers (D : SpCoefficientTowersAbelian l E T) :
    ObjectProperty (spDerivedCoefficientTowers l E T D) :=
  fun C ↦
    (∀ n : ℕ, spFiniteConstructibleTor T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
      ((spDerivedCoefficientEvaluation l E T D n).obj C)) ∧
    ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero
        ((@DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
            (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
          _ _ (HasDerivedCategory.standard _) i).obj
          ((spDerivedCoefficientEvaluation l E T D n).obj C))) ∧
      Scheme.HasProEtaleTorAmplitude T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((spDerivedCoefficientEvaluation l E T D n).obj C) c d

/-- Dctf(T,O_E/ell^bullet), with all ambient derived morphisms.
Source: blueprint, first paragraph (blueprint: prose-09-21). -/
abbrev spConstructibleTorTowerCategory (D : SpCoefficientTowersAbelian l E T) :=
  (spConstructibleTorTowers l E T D).FullSubcategory

/-- Normalization tests the specified canonical reduction for every m <= n.
Equal indices are included, where the recorded reduction is the tensor unitor.
Source: blueprint, second paragraph (blueprint: prose-09-21). -/
def IsSpNormalizedTower (D : SpCoefficientTowersAbelian l E T)
    (C : spDerivedCoefficientTowers l E T D) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)

/-- The predicate for the normalized constructible finite-Tor full subcategory.
Source: blueprint, final sentence (blueprint: prose-09-21). -/
def spNormalizedConstructibleTorTowers (D : SpCoefficientTowersAbelian l E T) :
    ObjectProperty (spDerivedCoefficientTowers l E T D) :=
  fun C ↦ spConstructibleTorTowers l E T D C ∧ IsSpNormalizedTower l E T D C

end AlgebraicGeometry.ProEtale
