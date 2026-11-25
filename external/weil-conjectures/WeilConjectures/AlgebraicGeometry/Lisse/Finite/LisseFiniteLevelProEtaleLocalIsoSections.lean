/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelProEtaleLocalIsoDescent
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelFixedRealizationLocalModel

/-! # Pro-etale local sections of the finite-level derived Isom sheaf

## References

* Stacks Project, Tags 099Y, 099Z, 09B1 and 09BV
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The finite-level comparison data yields a local section of the pro-etale derived Isom
presheaf through every geometric point.
-/
theorem lisse_finite_level_proetale_local_iso_sections
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hDbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj D))
    (hDlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj D))
    (hcomparison : Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((derivedLocalIsoPresheaf (ProEt.topology U.left)
          (lisseTowerEtaleRing d n)
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E))
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj D)).obj
            (op ((toProEt U.left).obj V))) := by
  have hlocal := lisse_finite_level_fixed_realization_local_model X Y g d U n N E D
    hcomparison hmodels
  exact exists_proetale_local_iso_section_of_fixed_realization_local_model X Y g d U n E D
    hDbounded hDlisse hlocal

end AlgebraicGeometry.Scheme
