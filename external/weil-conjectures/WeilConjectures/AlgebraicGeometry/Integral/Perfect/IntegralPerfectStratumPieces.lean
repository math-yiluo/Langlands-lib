/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Locally perfect pieces supported on a locally closed subscheme

## References

* Bhatt--Scholze, Lemma 6.3.14, final devissage, and Lemma 6.8.12
* Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.3.14
* Bhatt--Scholze, Lemma 6.3.14, final paragraph
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.flatConstantModulesAbelian

namespace AlgebraicGeometry.Scheme

/-- A bounded-above locally perfect complex on one scheme. The covering models
are taken on the identity stratum, with the same completed coefficient ring as
in the stratified-perfect predicate. -/
def IsIntegralLocallyPerfect (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (L : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  (∃ b : ℤ, L.IsLE b) ∧
  ∃ V : Sieve (⊤_ T.ProEt), V ∈ ProEt.topology T (⊤_ T.ProEt) ∧
    ∀ (W : T.ProEt) (f : W ⟶ ⊤_ T.ProEt), V f →
      ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
        @DerivedCategory.IsPerfectRingComplex A _
          (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
        Nonempty (integralLocalDerived (𝟙 T) (pbcAdicCompletion T d) W L ≅
          integralLocalDerived (𝟙 T) (pbcAdicCompletion T d) W
            ((integralConstantDerived T d).obj P))

/-- A locally closed support piece, in the open-then-closed order used by the
closed filtration: extend a locally perfect complex from a closed subscheme of
an open subscheme, and then extend by zero to T. Both functors are the actual
ordinary uncompleted derived functors. The coefficient comparisons are the fixed
inverse-image identifications of the adic datum. -/
def IsIntegralPerfectStratumPiece (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    ObjectProperty (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :=
  fun K ↦ ∃ (U Z : Scheme.{u}) (j : U ⟶ T) (hj : IsOpenImmersion j)
    (i : Z ⟶ U), IsClosedImmersion i ∧
    ∃ L : DerivedCategory (pbcModules Z (pbcAdicCompletion Z d)),
      IsIntegralLocallyPerfect Z d L ∧
      Nonempty (K ≅ (cbcDerivedOpenShriek d j hj).obj
        ((d.push i).obj L))

end AlgebraicGeometry.Scheme
