/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelInverseCohomology
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelEtaleModelComparison

/-! # Bounded finite-lisse model at one coefficient level

## References

* Stacks Project, Tags 099Y, 099Z and 09B1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/--
For a bounded finite level with local constant models, construct the bounded
finite-locally-constant etale complex and its fixed-realization comparison.
This is the model-and-comparison part of
`lisse_finite_level_etale_descent`; geometric Isom stalks are handled separately.
-/
theorem lisse_finite_level_etale_model
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E))
    (hfinite : ∀ q : ℤ, Module.Finite (lisseTowerEtaleRing d n)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) q).obj E))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∃ D : DerivedCategory
        (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      (∀ q : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N) := by
  let F := lisseTowerFixedRealization (U.hom ≫ g) d n
  let P := (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N
  let K := F.asEquivalence.inverse.obj P
  obtain ⟨hKbounded, hKlisse⟩ := lisse_finite_level_inverse_realization_cohomology
    X Y g d U n N E hbounded hfinite hmodels
  have hcohom (q : ℤ) :=
    (proEtale_lisse_origin U.left (lisseTowerEtaleRing d n)).2 _ (hKlisse q)
  obtain ⟨D, hDbounded, hDlisse, ⟨e⟩⟩ :=
    lisse_finite_level_etale_model_comparison U.left (lisseTowerEtaleRing d n)
      K hKbounded hcohom
  exact ⟨D, hDbounded, hDlisse,
    ⟨F.mapIso e ≪≫ F.asEquivalence.counitIso.app P⟩⟩

end AlgebraicGeometry.Scheme
